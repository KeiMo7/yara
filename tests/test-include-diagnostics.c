/*
Copyright (c) 2026. The YARA Authors. All Rights Reserved.

Redistribution and use in source and binary forms, with or without modification,
are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this
list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice,
this list of conditions and the following disclaimer in the documentation and/or
other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its contributors
may be used to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

// Tests for the compiler's opt-in diagnostics facility: include cycle /
// duplicate-include / duplicated rule / undefined rule attribution, with
// full include chains carrying file identity and line numbers.

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#include <yara.h>

static int tests_failed = 0;

#define CHECK(cond)                                                        \
  do                                                                       \
  {                                                                        \
    if (!(cond))                                                           \
    {                                                                      \
      fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond);      \
      tests_failed++;                                                      \
    }                                                                      \
  } while (0)

// True if str ends with suffix.
static int ends_with(const char* str, const char* suffix)
{
  size_t str_len = strlen(str);
  size_t suffix_len = strlen(suffix);

  return str_len >= suffix_len &&
         strcmp(str + str_len - suffix_len, suffix) == 0;
}

static char test_dir[4096];

static void make_test_dir(void)
{
  strcpy(test_dir, "/tmp/yara_diag_test_XXXXXX");

  if (mkdtemp(test_dir) == NULL)
  {
    perror("mkdtemp");
    exit(1);
  }
}

static void path_join(char* out, size_t out_size, const char* name)
{
  snprintf(out, out_size, "%s/%s", test_dir, name);
}

static void write_file(const char* name, const char* content)
{
  char path[4096];
  path_join(path, sizeof(path), name);

  FILE* f = fopen(path, "w");

  if (f == NULL)
  {
    perror(path);
    exit(1);
  }

  fputs(content, f);
  fclose(f);
}

// Captures the last compiler callback message, used to verify that the
// human-readable error output is unchanged.
static char last_callback_message[512];
static int callback_message_count;

static void compiler_callback(
    int error_level,
    const char* file_name,
    int line_number,
    const YR_RULE* rule,
    const char* message,
    void* user_data)
{
  callback_message_count++;
  strncpy(
      last_callback_message,
      message,
      sizeof(last_callback_message) - 1);
  last_callback_message[sizeof(last_callback_message) - 1] = '\0';
}

static YR_COMPILER* new_compiler(int diagnostics)
{
  YR_COMPILER* compiler = NULL;

  if (yr_compiler_create(&compiler) != ERROR_SUCCESS)
  {
    fprintf(stderr, "yr_compiler_create failed\n");
    exit(1);
  }

  yr_compiler_set_diagnostics_enabled(compiler, diagnostics);
  yr_compiler_set_callback(compiler, compiler_callback, NULL);

  callback_message_count = 0;
  last_callback_message[0] = '\0';

  return compiler;
}

// Compiles the file "name" (inside the test directory) in the given
// namespace, returning the number of errors reported.
static int add_file(YR_COMPILER* compiler, const char* name, const char* ns)
{
  char path[4096];
  path_join(path, sizeof(path), name);

  FILE* f = fopen(path, "r");

  if (f == NULL)
  {
    perror(path);
    exit(1);
  }

  int errors = yr_compiler_add_file(compiler, f, ns, path);

  fclose(f);
  return errors;
}

static const YR_DIAGNOSTIC* only_diagnostic(YR_COMPILER* compiler)
{
  if (yr_compiler_get_num_diagnostics(compiler) != 1)
  {
    fprintf(
        stderr,
        "  (got %d diagnostics, expected 1)\n",
        yr_compiler_get_num_diagnostics(compiler));

    const YR_DIAGNOSTIC* diags = yr_compiler_get_diagnostics(compiler);

    for (int i = 0; i < yr_compiler_get_num_diagnostics(compiler); i++)
      fprintf(stderr, "  diag[%d] kind=%d msg=%s\n", i, diags[i].kind,
              diags[i].message);
  }
  CHECK(yr_compiler_get_num_diagnostics(compiler) == 1);
  return yr_compiler_get_diagnostics(compiler);
}

// 1. A file that includes itself must be reported as a cycle, with the
// include chain pointing at the file and the line of the include statement.
static void test_direct_cycle(void)
{
  write_file("self.yar", "include \"self.yar\"\nrule r { condition: true }\n");

  YR_COMPILER* compiler = new_compiler(true);
  CHECK(add_file(compiler, "self.yar", NULL) > 0);

  const YR_DIAGNOSTIC* diag = only_diagnostic(compiler);
  CHECK(diag->kind == YR_DIAGNOSTIC_INCLUDE_CYCLE);
  CHECK(diag->chain_length == 2);
  CHECK(ends_with(diag->chain[0].file_name, "self.yar"));
  CHECK(ends_with(diag->chain[1].file_name, "self.yar"));
  CHECK(diag->chain[0].line == 0);  // root of the chain
  CHECK(diag->chain[1].line == 1);  // include statement is at line 1
  CHECK(diag->chain[0].canonical_id != NULL);
  CHECK(diag->chain[1].canonical_id == NULL);  // extra hop: not canonicalized
  CHECK(strstr(diag->message, "circular") != NULL);

  yr_compiler_destroy(compiler);
}

// 2. a -> b -> c -> b must be reported as a cycle, and every hop in the
// chain must carry the right file and line.
static void test_indirect_cycle(void)
{
  write_file("ia.yar", "include \"ib.yar\"\nrule a { condition: true }\n");
  write_file("ib.yar", "\n\ninclude \"ic.yar\"\nrule b { condition: true }\n");
  write_file("ic.yar", "include \"ib.yar\"\nrule c { condition: true }\n");

  YR_COMPILER* compiler = new_compiler(true);
  CHECK(add_file(compiler, "ia.yar", NULL) > 0);

  const YR_DIAGNOSTIC* diag = only_diagnostic(compiler);
  CHECK(diag->kind == YR_DIAGNOSTIC_INCLUDE_CYCLE);
  CHECK(diag->chain_length == 4);
  CHECK(ends_with(diag->chain[0].file_name, "ia.yar"));
  CHECK(ends_with(diag->chain[1].file_name, "ib.yar"));
  CHECK(ends_with(diag->chain[2].file_name, "ic.yar"));
  CHECK(ends_with(diag->chain[3].file_name, "ib.yar"));
  CHECK(diag->chain[0].line == 0);
  CHECK(diag->chain[1].line == 1);  // ia includes ib at line 1
  CHECK(diag->chain[2].line == 3);  // ib includes ic at line 3
  CHECK(diag->chain[3].line == 1);  // ic includes ib at line 1

  yr_compiler_destroy(compiler);
}

// 3. The same file reached through different spellings ("./", redundant
// separators, "..") must still be recognized as the same file and reported
// as a cycle, while the chain preserves the original spellings.
static void test_path_variant_cycle(void)
{
  char subdir[4096];
  path_join(subdir, sizeof(subdir), "sub");
  mkdir(subdir, 0755);

  write_file("va.yar", "include \"./vb.yar\"\nrule a { condition: true }\n");
  write_file(
      "vb.yar", "include \"sub/.././/vb.yar\"\nrule b { condition: true }\n");

  YR_COMPILER* compiler = new_compiler(true);
  CHECK(add_file(compiler, "va.yar", NULL) > 0);

  const YR_DIAGNOSTIC* diag = only_diagnostic(compiler);
  CHECK(diag->kind == YR_DIAGNOSTIC_INCLUDE_CYCLE);
  CHECK(diag->chain_length == 3);
  CHECK(ends_with(diag->chain[0].file_name, "va.yar"));
  // The original spelling is preserved for display...
  CHECK(strstr(diag->chain[1].file_name, "./vb.yar") != NULL);
  CHECK(strstr(diag->chain[2].file_name, "sub/.././/vb.yar") != NULL);
  // ...but identity is decided by the canonical form.
  CHECK(diag->chain[0].canonical_id != NULL);
  CHECK(diag->chain[1].canonical_id != NULL);
  CHECK(
      strcmp(diag->chain[0].canonical_id, diag->chain[1].canonical_id) != 0);
  CHECK(diag->chain[1].line == 1);
  CHECK(diag->chain[2].line == 1);

  yr_compiler_destroy(compiler);
}

// 4. A diamond (the same file included from two unrelated branches of the
// include graph, same namespace) is a duplicate include, not a cycle.
static void test_diamond_include(void)
{
  write_file(
      "common.yar", "rule common_rule { condition: true }\n");
  write_file(
      "branch1.yar", "include \"common.yar\"\nrule b1 { condition: true }\n");
  write_file(
      "branch2.yar",
      "\ninclude \"common.yar\"\nrule b2 { condition: true }\n");
  write_file(
      "root.yar",
      "include \"branch1.yar\"\ninclude \"branch2.yar\"\n"
      "rule root_rule { condition: true }\n");

  YR_COMPILER* compiler = new_compiler(true);
  CHECK(add_file(compiler, "root.yar", NULL) > 0);

  const YR_DIAGNOSTIC* diag = only_diagnostic(compiler);
  CHECK(diag->kind == YR_DIAGNOSTIC_INCLUDE_DUPLICATE);
  // The diagnostic points at where the file was included the first time.
  CHECK(diag->related_file != NULL);
  CHECK(ends_with(diag->related_file, "branch1.yar"));
  CHECK(diag->related_line == 1);
  // The chain ends with the second include of common.yar, from branch2.yar
  // line 2.
  CHECK(diag->chain_length == 3);
  CHECK(ends_with(diag->chain[0].file_name, "root.yar"));
  CHECK(ends_with(diag->chain[1].file_name, "branch2.yar"));
  CHECK(ends_with(diag->chain[2].file_name, "common.yar"));
  CHECK(diag->chain[1].line == 2);
  CHECK(diag->chain[2].line == 2);

  yr_compiler_destroy(compiler);
}

// 4b. The same diamond through two different namespaces is legal and must
// compile exactly as before: no errors, no diagnostics, one rule per
// namespace.
static void test_diamond_include_across_namespaces(void)
{
  write_file("nscommon.yar", "rule x { condition: true }\n");
  write_file("nsroot1.yar", "include \"nscommon.yar\"\n");
  write_file("nsroot2.yar", "include \"nscommon.yar\"\n");

  YR_COMPILER* compiler = new_compiler(true);
  CHECK(add_file(compiler, "nsroot1.yar", "ns1") == 0);
  CHECK(add_file(compiler, "nsroot2.yar", "ns2") == 0);
  CHECK(yr_compiler_get_num_diagnostics(compiler) == 0);

  YR_RULES* rules = NULL;
  CHECK(yr_compiler_get_rules(compiler, &rules) == ERROR_SUCCESS);

  int count = 0;
  YR_RULE* rule;
  yr_rules_foreach(rules, rule)
  {
    CHECK(strcmp(rule->identifier, "x") == 0);
    count++;
  }
  CHECK(count == 2);

  yr_rules_destroy(rules);
  yr_compiler_destroy(compiler);
}

// 5. A rule defined in two different files must point to the file and line
// of the first definition.
static void test_cross_file_duplicate_rule(void)
{
  write_file("da.yar", "\nrule dup { condition: true }\n");
  write_file("db.yar", "rule dup { condition: false }\n");
  write_file("droot.yar", "include \"da.yar\"\ninclude \"db.yar\"\n");

  YR_COMPILER* compiler = new_compiler(true);
  CHECK(add_file(compiler, "droot.yar", NULL) > 0);

  const YR_DIAGNOSTIC* diag = only_diagnostic(compiler);
  CHECK(diag->kind == YR_DIAGNOSTIC_DUPLICATED_RULE);
  CHECK(strcmp(diag->identifier, "dup") == 0);
  CHECK(diag->related_file != NULL);
  CHECK(ends_with(diag->related_file, "da.yar"));
  CHECK(diag->related_line == 2);
  // The error happened while parsing db.yar, included from droot.yar line 2.
  CHECK(diag->chain_length == 2);
  CHECK(ends_with(diag->chain[1].file_name, "db.yar"));
  CHECK(diag->chain[1].line == 2);

  yr_compiler_destroy(compiler);
}

// 6. A rule defined twice in the same file must point to the first
// definition.
static void test_same_file_duplicate_rule(void)
{
  write_file(
      "sdup.yar",
      "rule dup { condition: true }\n"
      "rule other { condition: true }\n"
      "rule dup { condition: false }\n");

  YR_COMPILER* compiler = new_compiler(true);
  CHECK(add_file(compiler, "sdup.yar", NULL) > 0);

  const YR_DIAGNOSTIC* diag = only_diagnostic(compiler);
  CHECK(diag->kind == YR_DIAGNOSTIC_DUPLICATED_RULE);
  CHECK(strcmp(diag->identifier, "dup") == 0);
  CHECK(ends_with(diag->related_file, "sdup.yar"));
  CHECK(diag->related_line == 1);

  yr_compiler_destroy(compiler);
}

// 7/8/9. Undefined rule references must distinguish "defined later in this
// file", "exists in another namespace" and "doesn't exist anywhere", while
// the classic error message stays the same.
static void test_forward_reference(void)
{
  write_file(
      "fwd.yar",
      "rule a { condition: b }\n"
      "\n"
      "rule b { condition: true }\n");

  YR_COMPILER* compiler = new_compiler(true);
  CHECK(add_file(compiler, "fwd.yar", NULL) > 0);

  const YR_DIAGNOSTIC* diag = only_diagnostic(compiler);
  CHECK(diag->kind == YR_DIAGNOSTIC_UNDEFINED_RULE_FORWARD_REF);
  CHECK(strcmp(diag->identifier, "b") == 0);
  CHECK(diag->related_line == 3);
  CHECK(diag->related_file != NULL);
  CHECK(ends_with(diag->related_file, "fwd.yar"));

  // The classic error message is unchanged.
  char message[512];
  yr_compiler_get_error_message(compiler, message, sizeof(message));
  CHECK(strcmp(message, "undefined identifier \"b\"") == 0);

  yr_compiler_destroy(compiler);
}

static void test_other_namespace_reference(void)
{
  write_file("ons1.yar", "rule x { condition: true }\n");
  write_file("ons2.yar", "rule y { condition: x }\n");

  YR_COMPILER* compiler = new_compiler(true);
  CHECK(add_file(compiler, "ons1.yar", "ns1") == 0);
  CHECK(add_file(compiler, "ons2.yar", "ns2") > 0);

  const YR_DIAGNOSTIC* diag = only_diagnostic(compiler);
  CHECK(diag->kind == YR_DIAGNOSTIC_UNDEFINED_RULE_OTHER_NAMESPACE);
  CHECK(strcmp(diag->identifier, "x") == 0);
  CHECK(strcmp(diag->name_space, "ns1") == 0);

  yr_compiler_destroy(compiler);
}

static void test_dangling_reference(void)
{
  write_file("dangling.yar", "rule a { condition: no_such_rule }\n");

  YR_COMPILER* compiler = new_compiler(true);
  CHECK(add_file(compiler, "dangling.yar", NULL) > 0);

  const YR_DIAGNOSTIC* diag = only_diagnostic(compiler);
  CHECK(diag->kind == YR_DIAGNOSTIC_UNDEFINED_RULE);
  CHECK(strcmp(diag->identifier, "no_such_rule") == 0);

  yr_compiler_destroy(compiler);
}

// 10a. Including a file that doesn't exist is reported as "not found",
// keeping the original spelling and the include site.
static void test_include_not_found(void)
{
  write_file(
      "notfound.yar",
      "rule before { condition: true }\n"
      "include \"missing.yar\"\n");

  YR_COMPILER* compiler = new_compiler(true);
  CHECK(add_file(compiler, "notfound.yar", NULL) > 0);

  const YR_DIAGNOSTIC* diag = only_diagnostic(compiler);
  CHECK(diag->kind == YR_DIAGNOSTIC_INCLUDE_NOT_FOUND);
  CHECK(diag->chain_length == 2);
  CHECK(strcmp(diag->chain[1].file_name, "missing.yar") == 0);
  CHECK(diag->chain[1].line == 2);

  // The human-readable error is the same as before this facility existed.
  CHECK(strstr(last_callback_message, "can't open include file") != NULL);

  yr_compiler_destroy(compiler);
}

// 10b. A file that exists but can't be read is reported differently from a
// file that doesn't exist.
static void test_include_not_readable(void)
{
  if (geteuid() == 0)
    return;  // root can read anything, the test is meaningless.

  write_file("noperm.yar", "rule x { condition: true }\n");

  char path[4096];
  path_join(path, sizeof(path), "noperm.yar");
  chmod(path, 0);

  write_file("unreadable.yar", "include \"noperm.yar\"\n");

  YR_COMPILER* compiler = new_compiler(true);
  CHECK(add_file(compiler, "unreadable.yar", NULL) > 0);

  const YR_DIAGNOSTIC* diag = only_diagnostic(compiler);
  CHECK(diag->kind == YR_DIAGNOSTIC_INCLUDE_NOT_READABLE);
  CHECK(diag->chain_length == 2);
  CHECK(strcmp(diag->chain[1].file_name, "noperm.yar") == 0);
  CHECK(diag->chain[1].line == 1);

  chmod(path, 0644);
  yr_compiler_destroy(compiler);
}

// 10c. When the include depth limit is hit, the diagnostic carries the
// longest include chain seen so far.
static void test_include_depth_exceeded(void)
{
  // YR_MAX_INCLUDE_DEPTH is 16; create a chain longer than that.
  for (int i = 0; i <= YR_MAX_INCLUDE_DEPTH; i++)
  {
    char name[32];
    char content[128];

    snprintf(name, sizeof(name), "depth%d.yar", i);
    snprintf(
        content,
        sizeof(content),
        "include \"depth%d.yar\"\nrule r%d { condition: true }\n",
        i + 1,
        i);

    write_file(name, content);
  }

  // The chain ends with a file that exists so that the depth check (not
  // "not found") triggers.
  write_file("depth17.yar", "rule r17 { condition: true }\n");

  YR_COMPILER* compiler = new_compiler(true);
  CHECK(add_file(compiler, "depth0.yar", NULL) > 0);

  const YR_DIAGNOSTIC* diag = only_diagnostic(compiler);
  CHECK(diag->kind == YR_DIAGNOSTIC_INCLUDE_DEPTH_EXCEEDED);
  // The chain holds the 16 files that fit, plus the one that didn't.
  CHECK(diag->chain_length == YR_MAX_INCLUDE_DEPTH + 1);
  CHECK(ends_with(diag->chain[0].file_name, "depth0.yar"));
  CHECK(diag->chain[0].line == 0);
  for (int i = 1; i < diag->chain_length; i++)
    CHECK(diag->chain[i].line == 1);

  yr_compiler_destroy(compiler);
}

// 11. With diagnostics disabled, behavior is exactly as before: the compile
// fails with the classic message and no diagnostics are recorded.
static void test_diagnostics_disabled(void)
{
  write_file(
      "plainself.yar", "include \"plainself.yar\"\nrule r { condition: true }\n");

  YR_COMPILER* compiler = new_compiler(false);
  CHECK(add_file(compiler, "plainself.yar", NULL) > 0);
  CHECK(yr_compiler_get_num_diagnostics(compiler) == 0);
  CHECK(strcmp(last_callback_message, "includes circular reference") == 0);

  yr_compiler_destroy(compiler);
}

// 12. A custom include callback (rules coming from memory, not disk) must
// keep working; the identity of such sources is "uncertain" (canonical_id
// NULL) and cycle detection falls back to the name as written.
static const char* custom_include_callback(
    const char* include_name,
    const char* calling_rule_filename,
    const char* calling_rule_namespace,
    void* user_data)
{
  if (strcmp(include_name, "mem://b") == 0)
    return "include \"mem://b\"\nrule mb { condition: true }\n";

  return NULL;
}

static void test_custom_callback_uncertain_identity(void)
{
  YR_COMPILER* compiler = new_compiler(true);
  yr_compiler_set_include_callback(
      compiler, custom_include_callback, NULL, NULL);

  CHECK(
      yr_compiler_add_string(
          compiler, "include \"mem://b\"\nrule ma { condition: true }", NULL) >
      0);

  const YR_DIAGNOSTIC* diag = only_diagnostic(compiler);
  CHECK(diag->kind == YR_DIAGNOSTIC_INCLUDE_CYCLE);
  CHECK(diag->chain_length == 2);
  CHECK(strcmp(diag->chain[1].file_name, "mem://b") == 0);
  // Identity is uncertain: it must not be guessed as a disk path.
  CHECK(diag->chain[0].canonical_id == NULL);
  CHECK(diag->chain[1].canonical_id == NULL);

  yr_compiler_destroy(compiler);
}

// 13. A clean rule base with includes compiles exactly as before: no
// diagnostics, same rules, same matching behavior.
static int match_count;

static int scan_callback(
    YR_SCAN_CONTEXT* context,
    int message,
    void* message_data,
    void* user_data)
{
  if (message == CALLBACK_MSG_RULE_MATCHING)
    match_count++;
  return CALLBACK_CONTINUE;
}

static void test_clean_ruleset(void)
{
  write_file(
      "clean_common.yar",
      "rule clean_x { strings: $a = \"abc\" condition: $a }\n");
  write_file(
      "clean_root.yar",
      "include \"clean_common.yar\"\n"
      "rule clean_y { strings: $b = \"def\" condition: $b }\n");

  YR_COMPILER* compiler = new_compiler(true);
  CHECK(add_file(compiler, "clean_root.yar", NULL) == 0);
  CHECK(yr_compiler_get_num_diagnostics(compiler) == 0);

  YR_RULES* rules = NULL;
  CHECK(yr_compiler_get_rules(compiler, &rules) == ERROR_SUCCESS);

  int count = 0;
  YR_RULE* rule;
  yr_rules_foreach(rules, rule)
    count++;
  CHECK(count == 2);

  match_count = 0;
  const char* data = "abc def";
  CHECK(
      yr_rules_scan_mem(
          rules, (const uint8_t*) data, strlen(data), 0, scan_callback, NULL, 0) ==
      ERROR_SUCCESS);
  CHECK(match_count == 2);

  yr_rules_destroy(rules);
  yr_compiler_destroy(compiler);
}

// 14. Extreme combination: a long include chain that ends in a
// self-reference, with duplicated rules along the way. The compiler must
// terminate, must not crash or hang, and must produce diagnostics for both
// the duplicates and the cycle.
static void test_extreme_combination(void)
{
  // Chain of 8 files, each defining a rule "shared" (duplicated across
  // files) and including the next one; the last one includes itself.
  for (int i = 0; i < 8; i++)
  {
    char name[32];
    char content[256];

    snprintf(name, sizeof(name), "combo%d.yar", i);

    if (i < 7)
      snprintf(
          content,
          sizeof(content),
          "rule shared { condition: true }\n"
          "rule unique%d { condition: true }\n"
          "include \"combo%d.yar\"\n",
          i,
          i + 1);
    else
      snprintf(
          content,
          sizeof(content),
          "rule shared { condition: true }\n"
          "include \"combo7.yar\"\n");

    write_file(name, content);
  }

  YR_COMPILER* compiler = new_compiler(true);
  CHECK(add_file(compiler, "combo0.yar", NULL) > 0);

  int cycles = 0;
  int duplicates = 0;

  const YR_DIAGNOSTIC* diags = yr_compiler_get_diagnostics(compiler);

  for (int i = 0; i < yr_compiler_get_num_diagnostics(compiler); i++)
  {
    if (diags[i].kind == YR_DIAGNOSTIC_INCLUDE_CYCLE)
      cycles++;
    else if (diags[i].kind == YR_DIAGNOSTIC_DUPLICATED_RULE)
      duplicates++;
  }

  CHECK(cycles == 1);
  CHECK(duplicates >= 1);

  yr_compiler_destroy(compiler);
}

int main(int argc, char** argv)
{
  yr_initialize();
  make_test_dir();

  test_direct_cycle();
  test_indirect_cycle();
  test_path_variant_cycle();
  test_diamond_include();
  test_diamond_include_across_namespaces();
  test_cross_file_duplicate_rule();
  test_same_file_duplicate_rule();
  test_forward_reference();
  test_other_namespace_reference();
  test_dangling_reference();
  test_include_not_found();
  test_include_not_readable();
  test_include_depth_exceeded();
  test_diagnostics_disabled();
  test_custom_callback_uncertain_identity();
  test_clean_ruleset();
  test_extreme_combination();

  yr_finalize();

  if (tests_failed > 0)
  {
    fprintf(stderr, "%d checks FAILED\n", tests_failed);
    return 1;
  }

  printf("all include-diagnostics checks passed\n");
  return 0;
}
