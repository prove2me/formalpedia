-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block1.rows_eval_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T12:19:32.680147+00:00
-- url     : https://prove2.me/submissions/82b46960-2513-43a5-a2a1-975a7e20ddf2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E001
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E196
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block1_row_eval_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block1_row_eval_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block1_row_eval_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block1_row_eval_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block1_row_eval_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block1_row_eval_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block1_row_eval_9_e

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation-preserving sparse integer merge. Its soundness needs no sorting
hypothesis: ordering is only used to make generated witnesses short. Each merge
can be checked independently by a finite integer-list equality. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*}

theorem eval_mergeFuel [LinearOrder ι] (fuel : ℕ) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeFuel fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeFuel]
      | cons b bs =>
        simp only [mergeFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_merge [LinearOrder ι] (a b : Sparse ι) (x : ι → ℝ) :
    eval (merge a b) x = eval a x + eval b x := eval_mergeFuel _ _ _ _

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node20_check : node20 =
    Integer.Sparse.merge (Integer.Sparse.scale (317457) entry_1_0) (Integer.Sparse.scale (670055) entry_1_1) := by decide +kernel

theorem node20_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node20 x = (((317457 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + ((670055 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x) := by
  rw [node20_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node21_check : node21 =
    Integer.Sparse.merge (Integer.Sparse.scale (-52372) entry_1_3) (Integer.Sparse.scale (303397) entry_1_4) := by decide +kernel

theorem node21_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node21 x = (((-52372 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((303397 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x) := by
  rw [node21_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node22_check : node22 =
    Integer.Sparse.merge (Integer.Sparse.scale (-459927) entry_1_2) node21 := by decide +kernel

theorem node22_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node22 x = (((-459927 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x + (((-52372 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((303397 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x)) := by
  rw [node22_check, Integer.Sparse.eval_merge]
  rw [node21_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node23_check : node23 =
    Integer.Sparse.merge node20 node22 := by decide +kernel

theorem node23_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node23 x = ((((317457 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + ((670055 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x) + (((-459927 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x + (((-52372 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((303397 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x))) := by
  rw [node23_check, Integer.Sparse.eval_merge]
  rw [node20_eval, node22_eval]

theorem node24_check : node24 =
    Integer.Sparse.merge (Integer.Sparse.scale (-104535) entry_1_5) (Integer.Sparse.scale (-981918) entry_1_6) := by decide +kernel

theorem node24_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node24 x = (((-104535 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x + ((-981918 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x) := by
  rw [node24_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node25_check : node25 =
    Integer.Sparse.merge (Integer.Sparse.scale (-485696) entry_1_8) (Integer.Sparse.scale (-1175469) entry_1_9) := by decide +kernel

theorem node25_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node25 x = (((-485696 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x + ((-1175469 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x) := by
  rw [node25_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node26_check : node26 =
    Integer.Sparse.merge (Integer.Sparse.scale (-162011) entry_1_7) node25 := by decide +kernel

theorem node26_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node26 x = (((-162011 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + (((-485696 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x + ((-1175469 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x)) := by
  rw [node26_check, Integer.Sparse.eval_merge]
  rw [node25_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node27_check : node27 =
    Integer.Sparse.merge node24 node26 := by decide +kernel

theorem node27_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node27 x = ((((-104535 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x + ((-981918 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x) + (((-162011 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + (((-485696 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x + ((-1175469 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x))) := by
  rw [node27_check, Integer.Sparse.eval_merge]
  rw [node24_eval, node26_eval]

theorem node28_check : node28 =
    Integer.Sparse.merge node23 node27 := by decide +kernel

theorem node28_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node28 x = (((((317457 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + ((670055 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x) + (((-459927 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x + (((-52372 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((303397 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x))) + ((((-104535 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x + ((-981918 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x) + (((-162011 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + (((-485696 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x + ((-1175469 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x)))) := by
  rw [node28_check, Integer.Sparse.eval_merge]
  rw [node23_eval, node27_eval]

theorem node29_check : node29 =
    Integer.Sparse.merge (Integer.Sparse.scale (154981) entry_1_10) (Integer.Sparse.scale (419927) entry_1_11) := by decide +kernel

theorem node29_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node29 x = (((154981 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x + ((419927 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x) := by
  rw [node29_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node30_check : node30 =
    Integer.Sparse.merge (Integer.Sparse.scale (-52654) entry_1_13) (Integer.Sparse.scale (-72835) entry_1_14) := by decide +kernel

theorem node30_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node30 x = (((-52654 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + ((-72835 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x) := by
  rw [node30_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node31_check : node31 =
    Integer.Sparse.merge (Integer.Sparse.scale (3385699) entry_1_12) node30 := by decide +kernel

theorem node31_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node31 x = (((3385699 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x + (((-52654 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + ((-72835 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x)) := by
  rw [node31_check, Integer.Sparse.eval_merge]
  rw [node30_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node32_check : node32 =
    Integer.Sparse.merge node29 node31 := by decide +kernel

theorem node32_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node32 x = ((((154981 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x + ((419927 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x) + (((3385699 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x + (((-52654 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + ((-72835 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x))) := by
  rw [node32_check, Integer.Sparse.eval_merge]
  rw [node29_eval, node31_eval]

theorem node33_check : node33 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1304244) entry_1_16) (Integer.Sparse.scale (-320066) entry_1_17) := by decide +kernel

theorem node33_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node33 x = (((-1304244 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + ((-320066 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x) := by
  rw [node33_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node34_check : node34 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1358640) entry_1_15) node33 := by decide +kernel

theorem node34_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node34 x = (((-1358640 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x + (((-1304244 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + ((-320066 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x)) := by
  rw [node34_check, Integer.Sparse.eval_merge]
  rw [node33_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node35_check : node35 =
    Integer.Sparse.merge (Integer.Sparse.scale (-252593) entry_1_19) (Integer.Sparse.scale (-1803981) entry_1_20) := by decide +kernel

theorem node35_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node35 x = (((-252593 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x + ((-1803981 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x) := by
  rw [node35_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node36_check : node36 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1529579) entry_1_18) node35 := by decide +kernel

theorem node36_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node36 x = (((-1529579 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x + (((-252593 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x + ((-1803981 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x)) := by
  rw [node36_check, Integer.Sparse.eval_merge]
  rw [node35_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node37_check : node37 =
    Integer.Sparse.merge node34 node36 := by decide +kernel

theorem node37_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node37 x = ((((-1358640 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x + (((-1304244 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + ((-320066 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x)) + (((-1529579 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x + (((-252593 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x + ((-1803981 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x))) := by
  rw [node37_check, Integer.Sparse.eval_merge]
  rw [node34_eval, node36_eval]

theorem node38_check : node38 =
    Integer.Sparse.merge node32 node37 := by decide +kernel

theorem node38_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node38 x = (((((154981 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x + ((419927 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x) + (((3385699 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x + (((-52654 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + ((-72835 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x))) + ((((-1358640 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x + (((-1304244 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + ((-320066 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x)) + (((-1529579 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x + (((-252593 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x + ((-1803981 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x)))) := by
  rw [node38_check, Integer.Sparse.eval_merge]
  rw [node32_eval, node37_eval]

theorem node39_check : node39 =
    Integer.Sparse.merge node28 node38 := by decide +kernel

theorem node39_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node39 x = ((((((317457 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + ((670055 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x) + (((-459927 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x + (((-52372 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((303397 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x))) + ((((-104535 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x + ((-981918 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x) + (((-162011 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + (((-485696 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x + ((-1175469 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x)))) + (((((154981 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x + ((419927 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x) + (((3385699 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x + (((-52654 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + ((-72835 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x))) + ((((-1358640 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x + (((-1304244 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + ((-320066 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x)) + (((-1529579 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x + (((-252593 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x + ((-1803981 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x))))) := by
  rw [node39_check, Integer.Sparse.eval_merge]
  rw [node28_eval, node38_eval]

theorem node60_check : node60 =
    Integer.Sparse.merge (Integer.Sparse.scale (591578) entry_3_0) (Integer.Sparse.scale (-52372) entry_3_1) := by decide +kernel

theorem node60_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node60 x = (((591578 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-52372 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) := by
  rw [node60_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node61_check : node61 =
    Integer.Sparse.merge (Integer.Sparse.scale (274017) entry_3_3) (Integer.Sparse.scale (-181761) entry_3_4) := by decide +kernel

theorem node61_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node61 x = (((274017 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-181761 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x) := by
  rw [node61_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node62_check : node62 =
    Integer.Sparse.merge (Integer.Sparse.scale (113157) entry_3_2) node61 := by decide +kernel

theorem node62_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node62 x = (((113157 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((274017 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-181761 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x)) := by
  rw [node62_check, Integer.Sparse.eval_merge]
  rw [node61_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node63_check : node63 =
    Integer.Sparse.merge node60 node62 := by decide +kernel

theorem node63_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node63 x = ((((591578 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-52372 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) + (((113157 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((274017 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-181761 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x))) := by
  rw [node63_check, Integer.Sparse.eval_merge]
  rw [node60_eval, node62_eval]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node64_check : node64 =
    Integer.Sparse.merge (Integer.Sparse.scale (94961) entry_3_5) (Integer.Sparse.scale (300328) entry_3_6) := by decide +kernel

theorem node64_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node64 x = (((94961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + ((300328 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x) := by
  rw [node64_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node65_check : node65 =
    Integer.Sparse.merge (Integer.Sparse.scale (174240) entry_3_8) (Integer.Sparse.scale (-1057177) entry_3_9) := by decide +kernel

theorem node65_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node65 x = (((174240 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + ((-1057177 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x) := by
  rw [node65_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node66_check : node66 =
    Integer.Sparse.merge (Integer.Sparse.scale (-195608) entry_3_7) node65 := by decide +kernel

theorem node66_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node66 x = (((-195608 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + (((174240 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + ((-1057177 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x)) := by
  rw [node66_check, Integer.Sparse.eval_merge]
  rw [node65_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node67_check : node67 =
    Integer.Sparse.merge node64 node66 := by decide +kernel

theorem node67_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node67 x = ((((94961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + ((300328 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x) + (((-195608 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + (((174240 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + ((-1057177 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x))) := by
  rw [node67_check, Integer.Sparse.eval_merge]
  rw [node64_eval, node66_eval]

theorem node68_check : node68 =
    Integer.Sparse.merge node63 node67 := by decide +kernel

theorem node68_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node68 x = (((((591578 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-52372 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) + (((113157 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((274017 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-181761 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x))) + ((((94961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + ((300328 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x) + (((-195608 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + (((174240 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + ((-1057177 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x)))) := by
  rw [node68_check, Integer.Sparse.eval_merge]
  rw [node63_eval, node67_eval]

theorem node69_check : node69 =
    Integer.Sparse.merge (Integer.Sparse.scale (-69659) entry_3_10) (Integer.Sparse.scale (-55345) entry_3_11) := by decide +kernel

theorem node69_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node69 x = (((-69659 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x + ((-55345 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x) := by
  rw [node69_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node70_check : node70 =
    Integer.Sparse.merge (Integer.Sparse.scale (26271) entry_3_13) (Integer.Sparse.scale (-167456) entry_3_14) := by decide +kernel

theorem node70_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node70 x = (((26271 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + ((-167456 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x) := by
  rw [node70_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node71_check : node71 =
    Integer.Sparse.merge (Integer.Sparse.scale (-724852) entry_3_12) node70 := by decide +kernel

theorem node71_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node71 x = (((-724852 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x + (((26271 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + ((-167456 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x)) := by
  rw [node71_check, Integer.Sparse.eval_merge]
  rw [node70_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node72_check : node72 =
    Integer.Sparse.merge node69 node71 := by decide +kernel

theorem node72_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node72 x = ((((-69659 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x + ((-55345 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x) + (((-724852 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x + (((26271 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + ((-167456 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x))) := by
  rw [node72_check, Integer.Sparse.eval_merge]
  rw [node69_eval, node71_eval]

theorem node73_check : node73 =
    Integer.Sparse.merge (Integer.Sparse.scale (-578406) entry_3_16) (Integer.Sparse.scale (64222) entry_3_17) := by decide +kernel

theorem node73_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node73 x = (((-578406 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((64222 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x) := by
  rw [node73_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node74_check : node74 =
    Integer.Sparse.merge (Integer.Sparse.scale (610565) entry_3_15) node73 := by decide +kernel

theorem node74_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node74 x = (((610565 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x + (((-578406 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((64222 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x)) := by
  rw [node74_check, Integer.Sparse.eval_merge]
  rw [node73_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node75_check : node75 =
    Integer.Sparse.merge (Integer.Sparse.scale (153302) entry_3_19) (Integer.Sparse.scale (-720802) entry_3_20) := by decide +kernel

theorem node75_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node75 x = (((153302 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + ((-720802 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x) := by
  rw [node75_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node76_check : node76 =
    Integer.Sparse.merge (Integer.Sparse.scale (300878) entry_3_18) node75 := by decide +kernel

theorem node76_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node76 x = (((300878 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x + (((153302 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + ((-720802 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x)) := by
  rw [node76_check, Integer.Sparse.eval_merge]
  rw [node75_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node77_check : node77 =
    Integer.Sparse.merge node74 node76 := by decide +kernel

theorem node77_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node77 x = ((((610565 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x + (((-578406 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((64222 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x)) + (((300878 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x + (((153302 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + ((-720802 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x))) := by
  rw [node77_check, Integer.Sparse.eval_merge]
  rw [node74_eval, node76_eval]

theorem node78_check : node78 =
    Integer.Sparse.merge node72 node77 := by decide +kernel

theorem node78_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node78 x = (((((-69659 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x + ((-55345 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x) + (((-724852 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x + (((26271 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + ((-167456 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x))) + ((((610565 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x + (((-578406 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((64222 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x)) + (((300878 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x + (((153302 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + ((-720802 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x)))) := by
  rw [node78_check, Integer.Sparse.eval_merge]
  rw [node72_eval, node77_eval]

theorem node79_check : node79 =
    Integer.Sparse.merge node68 node78 := by decide +kernel

theorem node79_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node79 x = ((((((591578 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-52372 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) + (((113157 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((274017 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-181761 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x))) + ((((94961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + ((300328 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x) + (((-195608 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + (((174240 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + ((-1057177 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x)))) + (((((-69659 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x + ((-55345 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x) + (((-724852 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x + (((26271 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + ((-167456 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x))) + ((((610565 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x + (((-578406 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((64222 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x)) + (((300878 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x + (((153302 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + ((-720802 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x))))) := by
  rw [node79_check, Integer.Sparse.eval_merge]
  rw [node68_eval, node78_eval]

theorem node80_check : node80 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3564906) entry_4_0) (Integer.Sparse.scale (303397) entry_4_1) := by decide +kernel

theorem node80_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node80 x = (((-3564906 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((303397 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) := by
  rw [node80_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node81_check : node81 =
    Integer.Sparse.merge (Integer.Sparse.scale (-181761) entry_4_3) (Integer.Sparse.scale (3093541) entry_4_4) := by decide +kernel

theorem node81_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node81 x = (((-181761 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((3093541 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x) := by
  rw [node81_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node82_check : node82 =
    Integer.Sparse.merge (Integer.Sparse.scale (3208427) entry_4_2) node81 := by decide +kernel

theorem node82_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node82 x = (((3208427 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((-181761 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((3093541 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x)) := by
  rw [node82_check, Integer.Sparse.eval_merge]
  rw [node81_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node83_check : node83 =
    Integer.Sparse.merge node80 node82 := by decide +kernel

theorem node83_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node83 x = ((((-3564906 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((303397 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) + (((3208427 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((-181761 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((3093541 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x))) := by
  rw [node83_check, Integer.Sparse.eval_merge]
  rw [node80_eval, node82_eval]

theorem node84_check : node84 =
    Integer.Sparse.merge (Integer.Sparse.scale (792287) entry_4_5) (Integer.Sparse.scale (-2353153) entry_4_6) := by decide +kernel

theorem node84_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node84 x = (((792287 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + ((-2353153 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x) := by
  rw [node84_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node85_check : node85 =
    Integer.Sparse.merge (Integer.Sparse.scale (-366545) entry_4_8) (Integer.Sparse.scale (263008) entry_4_9) := by decide +kernel

theorem node85_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node85 x = (((-366545 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + ((263008 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x) := by
  rw [node85_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node86_check : node86 =
    Integer.Sparse.merge (Integer.Sparse.scale (-496914) entry_4_7) node85 := by decide +kernel

theorem node86_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node86 x = (((-496914 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x + (((-366545 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + ((263008 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x)) := by
  rw [node86_check, Integer.Sparse.eval_merge]
  rw [node85_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node87_check : node87 =
    Integer.Sparse.merge node84 node86 := by decide +kernel

theorem node87_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node87 x = ((((792287 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + ((-2353153 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x) + (((-496914 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x + (((-366545 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + ((263008 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x))) := by
  rw [node87_check, Integer.Sparse.eval_merge]
  rw [node84_eval, node86_eval]

theorem node88_check : node88 =
    Integer.Sparse.merge node83 node87 := by decide +kernel

theorem node88_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node88 x = (((((-3564906 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((303397 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) + (((3208427 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((-181761 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((3093541 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x))) + ((((792287 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + ((-2353153 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x) + (((-496914 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x + (((-366545 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + ((263008 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x)))) := by
  rw [node88_check, Integer.Sparse.eval_merge]
  rw [node83_eval, node87_eval]

theorem node89_check : node89 =
    Integer.Sparse.merge (Integer.Sparse.scale (835313) entry_4_10) (Integer.Sparse.scale (637100) entry_4_11) := by decide +kernel

theorem node89_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node89 x = (((835313 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x + ((637100 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x) := by
  rw [node89_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node90_check : node90 =
    Integer.Sparse.merge (Integer.Sparse.scale (-673257) entry_4_13) (Integer.Sparse.scale (1902740) entry_4_14) := by decide +kernel

theorem node90_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node90 x = (((-673257 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_13 x + ((1902740 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x) := by
  rw [node90_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node91_check : node91 =
    Integer.Sparse.merge (Integer.Sparse.scale (3794703) entry_4_12) node90 := by decide +kernel

theorem node91_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node91 x = (((3794703 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_12 x + (((-673257 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_13 x + ((1902740 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x)) := by
  rw [node91_check, Integer.Sparse.eval_merge]
  rw [node90_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node92_check : node92 =
    Integer.Sparse.merge node89 node91 := by decide +kernel

theorem node92_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node92 x = ((((835313 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x + ((637100 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x) + (((3794703 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_12 x + (((-673257 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_13 x + ((1902740 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x))) := by
  rw [node92_check, Integer.Sparse.eval_merge]
  rw [node89_eval, node91_eval]

theorem node93_check : node93 =
    Integer.Sparse.merge (Integer.Sparse.scale (-316085) entry_4_16) (Integer.Sparse.scale (1025294) entry_4_17) := by decide +kernel

theorem node93_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node93 x = (((-316085 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_16 x + ((1025294 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x) := by
  rw [node93_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node94_check : node94 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4006041) entry_4_15) node93 := by decide +kernel

theorem node94_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node94 x = (((-4006041 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_15 x + (((-316085 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_16 x + ((1025294 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x)) := by
  rw [node94_check, Integer.Sparse.eval_merge]
  rw [node93_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node95_check : node95 =
    Integer.Sparse.merge (Integer.Sparse.scale (-921008) entry_4_19) (Integer.Sparse.scale (1327786) entry_4_20) := by decide +kernel

theorem node95_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node95 x = (((-921008 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_19 x + ((1327786 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_20 x) := by
  rw [node95_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node96_check : node96 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4308765) entry_4_18) node95 := by decide +kernel

theorem node96_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node96 x = (((-4308765 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_18 x + (((-921008 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_19 x + ((1327786 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_20 x)) := by
  rw [node96_check, Integer.Sparse.eval_merge]
  rw [node95_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node97_check : node97 =
    Integer.Sparse.merge node94 node96 := by decide +kernel

theorem node97_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node97 x = ((((-4006041 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_15 x + (((-316085 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_16 x + ((1025294 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x)) + (((-4308765 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_18 x + (((-921008 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_19 x + ((1327786 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_20 x))) := by
  rw [node97_check, Integer.Sparse.eval_merge]
  rw [node94_eval, node96_eval]

theorem node98_check : node98 =
    Integer.Sparse.merge node92 node97 := by decide +kernel

theorem node98_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node98 x = (((((835313 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x + ((637100 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x) + (((3794703 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_12 x + (((-673257 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_13 x + ((1902740 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x))) + ((((-4006041 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_15 x + (((-316085 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_16 x + ((1025294 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x)) + (((-4308765 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_18 x + (((-921008 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_19 x + ((1327786 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_20 x)))) := by
  rw [node98_check, Integer.Sparse.eval_merge]
  rw [node92_eval, node97_eval]

theorem node99_check : node99 =
    Integer.Sparse.merge node88 node98 := by decide +kernel

theorem node99_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node99 x = ((((((-3564906 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((303397 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) + (((3208427 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((-181761 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((3093541 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x))) + ((((792287 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + ((-2353153 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x) + (((-496914 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x + (((-366545 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + ((263008 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x)))) + (((((835313 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x + ((637100 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x) + (((3794703 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_12 x + (((-673257 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_13 x + ((1902740 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x))) + ((((-4006041 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_15 x + (((-316085 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_16 x + ((1025294 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x)) + (((-4308765 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_18 x + (((-921008 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_19 x + ((1327786 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_20 x))))) := by
  rw [node99_check, Integer.Sparse.eval_merge]
  rw [node88_eval, node98_eval]

theorem node120_check : node120 =
    Integer.Sparse.merge (Integer.Sparse.scale (2692899) entry_6_0) (Integer.Sparse.scale (-981918) entry_6_1) := by decide +kernel

theorem node120_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node120 x = (((2692899 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + ((-981918 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x) := by
  rw [node120_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node121_check : node121 =
    Integer.Sparse.merge (Integer.Sparse.scale (300328) entry_6_3) (Integer.Sparse.scale (-2353153) entry_6_4) := by decide +kernel

theorem node121_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node121 x = (((300328 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + ((-2353153 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x) := by
  rw [node121_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node122_check : node122 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1474042) entry_6_2) node121 := by decide +kernel

theorem node122_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node122 x = (((-1474042 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x + (((300328 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + ((-2353153 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x)) := by
  rw [node122_check, Integer.Sparse.eval_merge]
  rw [node121_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node123_check : node123 =
    Integer.Sparse.merge node120 node122 := by decide +kernel

theorem node123_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node123 x = ((((2692899 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + ((-981918 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x) + (((-1474042 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x + (((300328 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + ((-2353153 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x))) := by
  rw [node123_check, Integer.Sparse.eval_merge]
  rw [node120_eval, node122_eval]

theorem node124_check : node124 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2061591) entry_6_5) (Integer.Sparse.scale (3943670) entry_6_6) := by decide +kernel

theorem node124_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node124 x = (((-2061591 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x + ((3943670 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x) := by
  rw [node124_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node125_check : node125 =
    Integer.Sparse.merge (Integer.Sparse.scale (1112745) entry_6_8) (Integer.Sparse.scale (1793037) entry_6_9) := by decide +kernel

theorem node125_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node125 x = (((1112745 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x + ((1793037 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x) := by
  rw [node125_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node126_check : node126 =
    Integer.Sparse.merge (Integer.Sparse.scale (-132639) entry_6_7) node125 := by decide +kernel

theorem node126_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node126 x = (((-132639 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + (((1112745 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x + ((1793037 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x)) := by
  rw [node126_check, Integer.Sparse.eval_merge]
  rw [node125_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node127_check : node127 =
    Integer.Sparse.merge node124 node126 := by decide +kernel

theorem node127_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node127 x = ((((-2061591 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x + ((3943670 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x) + (((-132639 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + (((1112745 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x + ((1793037 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x))) := by
  rw [node127_check, Integer.Sparse.eval_merge]
  rw [node124_eval, node126_eval]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node128_check : node128 =
    Integer.Sparse.merge node123 node127 := by decide +kernel

theorem node128_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node128 x = (((((2692899 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + ((-981918 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x) + (((-1474042 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x + (((300328 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + ((-2353153 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x))) + ((((-2061591 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x + ((3943670 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x) + (((-132639 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + (((1112745 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x + ((1793037 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x)))) := by
  rw [node128_check, Integer.Sparse.eval_merge]
  rw [node123_eval, node127_eval]

theorem node129_check : node129 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1169740) entry_6_10) (Integer.Sparse.scale (-1576236) entry_6_11) := by decide +kernel

theorem node129_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node129 x = (((-1169740 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x + ((-1576236 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x) := by
  rw [node129_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node130_check : node130 =
    Integer.Sparse.merge (Integer.Sparse.scale (1211833) entry_6_13) (Integer.Sparse.scale (-2161046) entry_6_14) := by decide +kernel

theorem node130_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node130 x = (((1211833 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + ((-2161046 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x) := by
  rw [node130_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node131_check : node131 =
    Integer.Sparse.merge (Integer.Sparse.scale (-8279149) entry_6_12) node130 := by decide +kernel

theorem node131_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node131 x = (((-8279149 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x + (((1211833 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + ((-2161046 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x)) := by
  rw [node131_check, Integer.Sparse.eval_merge]
  rw [node130_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node132_check : node132 =
    Integer.Sparse.merge node129 node131 := by decide +kernel

theorem node132_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node132 x = ((((-1169740 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x + ((-1576236 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x) + (((-8279149 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x + (((1211833 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + ((-2161046 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x))) := by
  rw [node132_check, Integer.Sparse.eval_merge]
  rw [node129_eval, node131_eval]

theorem node133_check : node133 =
    Integer.Sparse.merge (Integer.Sparse.scale (1708504) entry_6_16) (Integer.Sparse.scale (-2418137) entry_6_17) := by decide +kernel

theorem node133_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node133 x = (((1708504 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + ((-2418137 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x) := by
  rw [node133_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node134_check : node134 =
    Integer.Sparse.merge (Integer.Sparse.scale (6223125) entry_6_15) node133 := by decide +kernel

theorem node134_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node134 x = (((6223125 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x + (((1708504 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + ((-2418137 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x)) := by
  rw [node134_check, Integer.Sparse.eval_merge]
  rw [node133_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node135_check : node135 =
    Integer.Sparse.merge (Integer.Sparse.scale (1712829) entry_6_19) (Integer.Sparse.scale (-299969) entry_6_20) := by decide +kernel

theorem node135_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node135 x = (((1712829 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x + ((-299969 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x) := by
  rw [node135_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node136_check : node136 =
    Integer.Sparse.merge (Integer.Sparse.scale (5095570) entry_6_18) node135 := by decide +kernel

theorem node136_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node136 x = (((5095570 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x + (((1712829 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x + ((-299969 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x)) := by
  rw [node136_check, Integer.Sparse.eval_merge]
  rw [node135_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node137_check : node137 =
    Integer.Sparse.merge node134 node136 := by decide +kernel

theorem node137_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node137 x = ((((6223125 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x + (((1708504 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + ((-2418137 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x)) + (((5095570 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x + (((1712829 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x + ((-299969 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x))) := by
  rw [node137_check, Integer.Sparse.eval_merge]
  rw [node134_eval, node136_eval]

theorem node138_check : node138 =
    Integer.Sparse.merge node132 node137 := by decide +kernel

theorem node138_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node138 x = (((((-1169740 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x + ((-1576236 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x) + (((-8279149 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x + (((1211833 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + ((-2161046 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x))) + ((((6223125 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x + (((1708504 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + ((-2418137 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x)) + (((5095570 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x + (((1712829 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x + ((-299969 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x)))) := by
  rw [node138_check, Integer.Sparse.eval_merge]
  rw [node132_eval, node137_eval]

theorem node139_check : node139 =
    Integer.Sparse.merge node128 node138 := by decide +kernel

theorem node139_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node139 x = ((((((2692899 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + ((-981918 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x) + (((-1474042 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x + (((300328 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + ((-2353153 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x))) + ((((-2061591 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x + ((3943670 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x) + (((-132639 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + (((1112745 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x + ((1793037 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x)))) + (((((-1169740 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x + ((-1576236 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x) + (((-8279149 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x + (((1211833 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + ((-2161046 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x))) + ((((6223125 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x + (((1708504 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + ((-2418137 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x)) + (((5095570 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x + (((1712829 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x + ((-299969 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x))))) := by
  rw [node139_check, Integer.Sparse.eval_merge]
  rw [node128_eval, node138_eval]

theorem node140_check : node140 =
    Integer.Sparse.merge (Integer.Sparse.scale (-164059) entry_7_0) (Integer.Sparse.scale (-162011) entry_7_1) := by decide +kernel

theorem node140_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node140 x = (((-164059 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + ((-162011 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x) := by
  rw [node140_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node141_check : node141 =
    Integer.Sparse.merge (Integer.Sparse.scale (-195608) entry_7_3) (Integer.Sparse.scale (-496914) entry_7_4) := by decide +kernel

theorem node141_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node141 x = (((-195608 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + ((-496914 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x) := by
  rw [node141_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node142_check : node142 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1709009) entry_7_2) node141 := by decide +kernel

theorem node142_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node142 x = (((-1709009 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x + (((-195608 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + ((-496914 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x)) := by
  rw [node142_check, Integer.Sparse.eval_merge]
  rw [node141_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node143_check : node143 =
    Integer.Sparse.merge node140 node142 := by decide +kernel

theorem node143_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node143 x = ((((-164059 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + ((-162011 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x) + (((-1709009 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x + (((-195608 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + ((-496914 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x))) := by
  rw [node143_check, Integer.Sparse.eval_merge]
  rw [node140_eval, node142_eval]

theorem node144_check : node144 =
    Integer.Sparse.merge (Integer.Sparse.scale (173690) entry_7_5) (Integer.Sparse.scale (-132639) entry_7_6) := by decide +kernel

theorem node144_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node144 x = (((173690 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x + ((-132639 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x) := by
  rw [node144_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node145_check : node145 =
    Integer.Sparse.merge (Integer.Sparse.scale (-199316) entry_7_8) (Integer.Sparse.scale (1053902) entry_7_9) := by decide +kernel

theorem node145_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node145 x = (((-199316 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x + ((1053902 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x) := by
  rw [node145_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node146_check : node146 =
    Integer.Sparse.merge (Integer.Sparse.scale (1557465) entry_7_7) node145 := by decide +kernel

theorem node146_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node146 x = (((1557465 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + (((-199316 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x + ((1053902 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x)) := by
  rw [node146_check, Integer.Sparse.eval_merge]
  rw [node145_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node147_check : node147 =
    Integer.Sparse.merge node144 node146 := by decide +kernel

theorem node147_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node147 x = ((((173690 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x + ((-132639 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x) + (((1557465 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + (((-199316 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x + ((1053902 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x))) := by
  rw [node147_check, Integer.Sparse.eval_merge]
  rw [node144_eval, node146_eval]

theorem node148_check : node148 =
    Integer.Sparse.merge node143 node147 := by decide +kernel

theorem node148_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node148 x = (((((-164059 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + ((-162011 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x) + (((-1709009 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x + (((-195608 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + ((-496914 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x))) + ((((173690 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x + ((-132639 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x) + (((1557465 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + (((-199316 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x + ((1053902 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x)))) := by
  rw [node148_check, Integer.Sparse.eval_merge]
  rw [node143_eval, node147_eval]

theorem node149_check : node149 =
    Integer.Sparse.merge (Integer.Sparse.scale (-85533) entry_7_10) (Integer.Sparse.scale (-178234) entry_7_11) := by decide +kernel

theorem node149_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node149 x = (((-85533 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x + ((-178234 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x) := by
  rw [node149_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node150_check : node150 =
    Integer.Sparse.merge (Integer.Sparse.scale (-133074) entry_7_13) (Integer.Sparse.scale (339938) entry_7_14) := by decide +kernel

theorem node150_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node150 x = (((-133074 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_13 x + ((339938 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x) := by
  rw [node150_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node151_check : node151 =
    Integer.Sparse.merge (Integer.Sparse.scale (1114705) entry_7_12) node150 := by decide +kernel

theorem node151_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node151 x = (((1114705 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x + (((-133074 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_13 x + ((339938 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x)) := by
  rw [node151_check, Integer.Sparse.eval_merge]
  rw [node150_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node152_check : node152 =
    Integer.Sparse.merge node149 node151 := by decide +kernel

theorem node152_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node152 x = ((((-85533 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x + ((-178234 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x) + (((1114705 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x + (((-133074 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_13 x + ((339938 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x))) := by
  rw [node152_check, Integer.Sparse.eval_merge]
  rw [node149_eval, node151_eval]

theorem node153_check : node153 =
    Integer.Sparse.merge (Integer.Sparse.scale (979706) entry_7_16) (Integer.Sparse.scale (808468) entry_7_17) := by decide +kernel

theorem node153_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node153 x = (((979706 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + ((808468 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x) := by
  rw [node153_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node154_check : node154 =
    Integer.Sparse.merge (Integer.Sparse.scale (-371680) entry_7_15) node153 := by decide +kernel

theorem node154_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node154 x = (((-371680 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x + (((979706 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + ((808468 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x)) := by
  rw [node154_check, Integer.Sparse.eval_merge]
  rw [node153_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node155_check : node155 =
    Integer.Sparse.merge (Integer.Sparse.scale (-403513) entry_7_19) (Integer.Sparse.scale (1677944) entry_7_20) := by decide +kernel

theorem node155_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node155 x = (((-403513 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x + ((1677944 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x) := by
  rw [node155_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node156_check : node156 =
    Integer.Sparse.merge (Integer.Sparse.scale (201825) entry_7_18) node155 := by decide +kernel

theorem node156_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node156 x = (((201825 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x + (((-403513 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x + ((1677944 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x)) := by
  rw [node156_check, Integer.Sparse.eval_merge]
  rw [node155_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node157_check : node157 =
    Integer.Sparse.merge node154 node156 := by decide +kernel

theorem node157_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node157 x = ((((-371680 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x + (((979706 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + ((808468 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x)) + (((201825 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x + (((-403513 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x + ((1677944 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x))) := by
  rw [node157_check, Integer.Sparse.eval_merge]
  rw [node154_eval, node156_eval]

theorem node158_check : node158 =
    Integer.Sparse.merge node152 node157 := by decide +kernel

theorem node158_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node158 x = (((((-85533 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x + ((-178234 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x) + (((1114705 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x + (((-133074 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_13 x + ((339938 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x))) + ((((-371680 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x + (((979706 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + ((808468 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x)) + (((201825 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x + (((-403513 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x + ((1677944 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x)))) := by
  rw [node158_check, Integer.Sparse.eval_merge]
  rw [node152_eval, node157_eval]

theorem node159_check : node159 =
    Integer.Sparse.merge node148 node158 := by decide +kernel

theorem node159_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node159 x = ((((((-164059 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + ((-162011 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x) + (((-1709009 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x + (((-195608 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + ((-496914 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x))) + ((((173690 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x + ((-132639 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x) + (((1557465 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + (((-199316 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x + ((1053902 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x)))) + (((((-85533 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x + ((-178234 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x) + (((1114705 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x + (((-133074 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_13 x + ((339938 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x))) + ((((-371680 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x + (((979706 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + ((808468 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x)) + (((201825 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x + (((-403513 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x + ((1677944 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x))))) := by
  rw [node159_check, Integer.Sparse.eval_merge]
  rw [node148_eval, node158_eval]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node160_check : node160 =
    Integer.Sparse.merge (Integer.Sparse.scale (144765) entry_8_0) (Integer.Sparse.scale (-485696) entry_8_1) := by decide +kernel

theorem node160_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node160 x = (((144765 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + ((-485696 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x) := by
  rw [node160_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node161_check : node161 =
    Integer.Sparse.merge (Integer.Sparse.scale (174240) entry_8_3) (Integer.Sparse.scale (-366545) entry_8_4) := by decide +kernel

theorem node161_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node161 x = (((174240 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((-366545 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x) := by
  rw [node161_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node162_check : node162 =
    Integer.Sparse.merge (Integer.Sparse.scale (445414) entry_8_2) node161 := by decide +kernel

theorem node162_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node162 x = (((445414 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x + (((174240 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((-366545 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x)) := by
  rw [node162_check, Integer.Sparse.eval_merge]
  rw [node161_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node163_check : node163 =
    Integer.Sparse.merge node160 node162 := by decide +kernel

theorem node163_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node163 x = ((((144765 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + ((-485696 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x) + (((445414 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x + (((174240 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((-366545 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x))) := by
  rw [node163_check, Integer.Sparse.eval_merge]
  rw [node160_eval, node162_eval]

theorem node164_check : node164 =
    Integer.Sparse.merge (Integer.Sparse.scale (-125916) entry_8_5) (Integer.Sparse.scale (1112745) entry_8_6) := by decide +kernel

theorem node164_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node164 x = (((-125916 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x + ((1112745 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x) := by
  rw [node164_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node165_check : node165 =
    Integer.Sparse.merge (Integer.Sparse.scale (574590) entry_8_8) (Integer.Sparse.scale (419757) entry_8_9) := by decide +kernel

theorem node165_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node165 x = (((574590 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x + ((419757 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x) := by
  rw [node165_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node166_check : node166 =
    Integer.Sparse.merge (Integer.Sparse.scale (-199316) entry_8_7) node165 := by decide +kernel

theorem node166_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node166 x = (((-199316 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + (((574590 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x + ((419757 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x)) := by
  rw [node166_check, Integer.Sparse.eval_merge]
  rw [node165_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node167_check : node167 =
    Integer.Sparse.merge node164 node166 := by decide +kernel

theorem node167_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node167 x = ((((-125916 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x + ((1112745 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x) + (((-199316 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + (((574590 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x + ((419757 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x))) := by
  rw [node167_check, Integer.Sparse.eval_merge]
  rw [node164_eval, node166_eval]

theorem node168_check : node168 =
    Integer.Sparse.merge node163 node167 := by decide +kernel

theorem node168_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node168 x = (((((144765 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + ((-485696 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x) + (((445414 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x + (((174240 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((-366545 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x))) + ((((-125916 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x + ((1112745 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x) + (((-199316 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + (((574590 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x + ((419757 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x)))) := by
  rw [node168_check, Integer.Sparse.eval_merge]
  rw [node163_eval, node167_eval]

theorem node169_check : node169 =
    Integer.Sparse.merge (Integer.Sparse.scale (-184323) entry_8_10) (Integer.Sparse.scale (-374293) entry_8_11) := by decide +kernel

theorem node169_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node169 x = (((-184323 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x + ((-374293 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x) := by
  rw [node169_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node170_check : node170 =
    Integer.Sparse.merge (Integer.Sparse.scale (175194) entry_8_13) (Integer.Sparse.scale (-218282) entry_8_14) := by decide +kernel

theorem node170_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node170 x = (((175194 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + ((-218282 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x) := by
  rw [node170_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node171_check : node171 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3151845) entry_8_12) node170 := by decide +kernel

theorem node171_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node171 x = (((-3151845 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x + (((175194 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + ((-218282 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x)) := by
  rw [node171_check, Integer.Sparse.eval_merge]
  rw [node170_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node172_check : node172 =
    Integer.Sparse.merge node169 node171 := by decide +kernel

theorem node172_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node172 x = ((((-184323 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x + ((-374293 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x) + (((-3151845 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x + (((175194 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + ((-218282 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x))) := by
  rw [node172_check, Integer.Sparse.eval_merge]
  rw [node169_eval, node171_eval]

theorem node173_check : node173 =
    Integer.Sparse.merge (Integer.Sparse.scale (691622) entry_8_16) (Integer.Sparse.scale (-213776) entry_8_17) := by decide +kernel

theorem node173_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node173 x = (((691622 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + ((-213776 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x) := by
  rw [node173_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node174_check : node174 =
    Integer.Sparse.merge (Integer.Sparse.scale (1575701) entry_8_15) node173 := by decide +kernel

theorem node174_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node174 x = (((1575701 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x + (((691622 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + ((-213776 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x)) := by
  rw [node174_check, Integer.Sparse.eval_merge]
  rw [node173_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node175_check : node175 =
    Integer.Sparse.merge (Integer.Sparse.scale (427205) entry_8_19) (Integer.Sparse.scale (660976) entry_8_20) := by decide +kernel

theorem node175_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node175 x = (((427205 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x + ((660976 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x) := by
  rw [node175_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node176_check : node176 =
    Integer.Sparse.merge (Integer.Sparse.scale (1306896) entry_8_18) node175 := by decide +kernel

theorem node176_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node176 x = (((1306896 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x + (((427205 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x + ((660976 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x)) := by
  rw [node176_check, Integer.Sparse.eval_merge]
  rw [node175_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node177_check : node177 =
    Integer.Sparse.merge node174 node176 := by decide +kernel

theorem node177_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node177 x = ((((1575701 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x + (((691622 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + ((-213776 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x)) + (((1306896 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x + (((427205 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x + ((660976 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x))) := by
  rw [node177_check, Integer.Sparse.eval_merge]
  rw [node174_eval, node176_eval]

theorem node178_check : node178 =
    Integer.Sparse.merge node172 node177 := by decide +kernel

theorem node178_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node178 x = (((((-184323 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x + ((-374293 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x) + (((-3151845 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x + (((175194 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + ((-218282 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x))) + ((((1575701 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x + (((691622 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + ((-213776 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x)) + (((1306896 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x + (((427205 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x + ((660976 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x)))) := by
  rw [node178_check, Integer.Sparse.eval_merge]
  rw [node172_eval, node177_eval]

theorem node179_check : node179 =
    Integer.Sparse.merge node168 node178 := by decide +kernel

theorem node179_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node179 x = ((((((144765 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + ((-485696 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x) + (((445414 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x + (((174240 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((-366545 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x))) + ((((-125916 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x + ((1112745 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x) + (((-199316 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + (((574590 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x + ((419757 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x)))) + (((((-184323 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x + ((-374293 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x) + (((-3151845 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x + (((175194 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + ((-218282 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x))) + ((((1575701 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x + (((691622 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + ((-213776 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x)) + (((1306896 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x + (((427205 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x + ((660976 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x))))) := by
  rw [node179_check, Integer.Sparse.eval_merge]
  rw [node168_eval, node178_eval]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node200_check : node200 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1632149) entry_10_0) (Integer.Sparse.scale (154981) entry_10_1) := by decide +kernel

theorem node200_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node200 x = (((-1632149 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + ((154981 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x) := by
  rw [node200_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node201_check : node201 =
    Integer.Sparse.merge (Integer.Sparse.scale (-69659) entry_10_3) (Integer.Sparse.scale (835313) entry_10_4) := by decide +kernel

theorem node201_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node201 x = (((-69659 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + ((835313 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x) := by
  rw [node201_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node202_check : node202 =
    Integer.Sparse.merge (Integer.Sparse.scale (581829) entry_10_2) node201 := by decide +kernel

theorem node202_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node202 x = (((581829 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x + (((-69659 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + ((835313 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x)) := by
  rw [node202_check, Integer.Sparse.eval_merge]
  rw [node201_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node203_check : node203 =
    Integer.Sparse.merge node200 node202 := by decide +kernel

theorem node203_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node203 x = ((((-1632149 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + ((154981 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x) + (((581829 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x + (((-69659 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + ((835313 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x))) := by
  rw [node203_check, Integer.Sparse.eval_merge]
  rw [node200_eval, node202_eval]

theorem node204_check : node204 =
    Integer.Sparse.merge (Integer.Sparse.scale (991536) entry_10_5) (Integer.Sparse.scale (-1169740) entry_10_6) := by decide +kernel

theorem node204_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node204 x = (((991536 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x + ((-1169740 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x) := by
  rw [node204_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node205_check : node205 =
    Integer.Sparse.merge (Integer.Sparse.scale (-184323) entry_10_8) (Integer.Sparse.scale (681453) entry_10_9) := by decide +kernel

theorem node205_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node205 x = (((-184323 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x + ((681453 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x) := by
  rw [node205_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node206_check : node206 =
    Integer.Sparse.merge (Integer.Sparse.scale (-85533) entry_10_7) node205 := by decide +kernel

theorem node206_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node206 x = (((-85533 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + (((-184323 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x + ((681453 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x)) := by
  rw [node206_check, Integer.Sparse.eval_merge]
  rw [node205_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node207_check : node207 =
    Integer.Sparse.merge node204 node206 := by decide +kernel

theorem node207_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node207 x = ((((991536 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x + ((-1169740 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x) + (((-85533 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + (((-184323 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x + ((681453 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x))) := by
  rw [node207_check, Integer.Sparse.eval_merge]
  rw [node204_eval, node206_eval]

theorem node208_check : node208 =
    Integer.Sparse.merge node203 node207 := by decide +kernel

theorem node208_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node208 x = (((((-1632149 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + ((154981 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x) + (((581829 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x + (((-69659 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + ((835313 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x))) + ((((991536 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x + ((-1169740 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x) + (((-85533 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + (((-184323 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x + ((681453 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x)))) := by
  rw [node208_check, Integer.Sparse.eval_merge]
  rw [node203_eval, node207_eval]

theorem node209_check : node209 =
    Integer.Sparse.merge (Integer.Sparse.scale (1080797) entry_10_10) (Integer.Sparse.scale (996503) entry_10_11) := by decide +kernel

theorem node209_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node209 x = (((1080797 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x + ((996503 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x) := by
  rw [node209_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node210_check : node210 =
    Integer.Sparse.merge (Integer.Sparse.scale (-343789) entry_10_13) (Integer.Sparse.scale (1767463) entry_10_14) := by decide +kernel

theorem node210_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node210 x = (((-343789 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_13 x + ((1767463 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_14 x) := by
  rw [node210_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node211_check : node211 =
    Integer.Sparse.merge (Integer.Sparse.scale (1912285) entry_10_12) node210 := by decide +kernel

theorem node211_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node211 x = (((1912285 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_12 x + (((-343789 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_13 x + ((1767463 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_14 x)) := by
  rw [node211_check, Integer.Sparse.eval_merge]
  rw [node210_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node212_check : node212 =
    Integer.Sparse.merge node209 node211 := by decide +kernel

theorem node212_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node212 x = ((((1080797 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x + ((996503 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x) + (((1912285 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_12 x + (((-343789 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_13 x + ((1767463 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_14 x))) := by
  rw [node212_check, Integer.Sparse.eval_merge]
  rw [node209_eval, node211_eval]

theorem node213_check : node213 =
    Integer.Sparse.merge (Integer.Sparse.scale (174111) entry_10_16) (Integer.Sparse.scale (1098524) entry_10_17) := by decide +kernel

theorem node213_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node213 x = (((174111 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_16 x + ((1098524 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_17 x) := by
  rw [node213_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node214_check : node214 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2335848) entry_10_15) node213 := by decide +kernel

theorem node214_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node214 x = (((-2335848 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_15 x + (((174111 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_16 x + ((1098524 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_17 x)) := by
  rw [node214_check, Integer.Sparse.eval_merge]
  rw [node213_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node215_check : node215 =
    Integer.Sparse.merge (Integer.Sparse.scale (-498704) entry_10_19) (Integer.Sparse.scale (1464376) entry_10_20) := by decide +kernel

theorem node215_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node215 x = (((-498704 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_19 x + ((1464376 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_20 x) := by
  rw [node215_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node216_check : node216 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1981023) entry_10_18) node215 := by decide +kernel

theorem node216_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node216 x = (((-1981023 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_18 x + (((-498704 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_19 x + ((1464376 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_20 x)) := by
  rw [node216_check, Integer.Sparse.eval_merge]
  rw [node215_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node217_check : node217 =
    Integer.Sparse.merge node214 node216 := by decide +kernel

theorem node217_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node217 x = ((((-2335848 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_15 x + (((174111 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_16 x + ((1098524 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_17 x)) + (((-1981023 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_18 x + (((-498704 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_19 x + ((1464376 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_20 x))) := by
  rw [node217_check, Integer.Sparse.eval_merge]
  rw [node214_eval, node216_eval]

theorem node218_check : node218 =
    Integer.Sparse.merge node212 node217 := by decide +kernel

theorem node218_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node218 x = (((((1080797 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x + ((996503 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x) + (((1912285 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_12 x + (((-343789 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_13 x + ((1767463 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_14 x))) + ((((-2335848 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_15 x + (((174111 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_16 x + ((1098524 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_17 x)) + (((-1981023 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_18 x + (((-498704 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_19 x + ((1464376 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_20 x)))) := by
  rw [node218_check, Integer.Sparse.eval_merge]
  rw [node212_eval, node217_eval]

theorem node219_check : node219 =
    Integer.Sparse.merge node208 node218 := by decide +kernel

theorem node219_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node219 x = ((((((-1632149 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + ((154981 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x) + (((581829 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x + (((-69659 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + ((835313 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x))) + ((((991536 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x + ((-1169740 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x) + (((-85533 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + (((-184323 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x + ((681453 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x)))) + (((((1080797 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x + ((996503 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x) + (((1912285 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_12 x + (((-343789 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_13 x + ((1767463 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_14 x))) + ((((-2335848 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_15 x + (((174111 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_16 x + ((1098524 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_17 x)) + (((-1981023 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_18 x + (((-498704 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_19 x + ((1464376 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_20 x))))) := by
  rw [node219_check, Integer.Sparse.eval_merge]
  rw [node208_eval, node218_eval]

theorem node220_check : node220 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1203380) entry_11_0) (Integer.Sparse.scale (419927) entry_11_1) := by decide +kernel

theorem node220_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node220 x = (((-1203380 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + ((419927 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x) := by
  rw [node220_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node221_check : node221 =
    Integer.Sparse.merge (Integer.Sparse.scale (-55345) entry_11_3) (Integer.Sparse.scale (637100) entry_11_4) := by decide +kernel

theorem node221_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node221 x = (((-55345 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + ((637100 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x) := by
  rw [node221_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node222_check : node222 =
    Integer.Sparse.merge (Integer.Sparse.scale (158367) entry_11_2) node221 := by decide +kernel

theorem node222_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node222 x = (((158367 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x + (((-55345 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + ((637100 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x)) := by
  rw [node222_check, Integer.Sparse.eval_merge]
  rw [node221_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node223_check : node223 =
    Integer.Sparse.merge node220 node222 := by decide +kernel

theorem node223_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node223 x = ((((-1203380 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + ((419927 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x) + (((158367 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x + (((-55345 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + ((637100 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x))) := by
  rw [node223_check, Integer.Sparse.eval_merge]
  rw [node220_eval, node222_eval]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node224_check : node224 =
    Integer.Sparse.merge (Integer.Sparse.scale (1695692) entry_11_5) (Integer.Sparse.scale (-1576236) entry_11_6) := by decide +kernel

theorem node224_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node224 x = (((1695692 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x + ((-1576236 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x) := by
  rw [node224_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node225_check : node225 =
    Integer.Sparse.merge (Integer.Sparse.scale (-374293) entry_11_8) (Integer.Sparse.scale (-488773) entry_11_9) := by decide +kernel

theorem node225_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node225 x = (((-374293 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x + ((-488773 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x) := by
  rw [node225_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node226_check : node226 =
    Integer.Sparse.merge (Integer.Sparse.scale (-178234) entry_11_7) node225 := by decide +kernel

theorem node226_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node226 x = (((-178234 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + (((-374293 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x + ((-488773 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x)) := by
  rw [node226_check, Integer.Sparse.eval_merge]
  rw [node225_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node227_check : node227 =
    Integer.Sparse.merge node224 node226 := by decide +kernel

theorem node227_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node227 x = ((((1695692 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x + ((-1576236 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x) + (((-178234 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + (((-374293 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x + ((-488773 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x))) := by
  rw [node227_check, Integer.Sparse.eval_merge]
  rw [node224_eval, node226_eval]

theorem node228_check : node228 =
    Integer.Sparse.merge node223 node227 := by decide +kernel

theorem node228_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node228 x = (((((-1203380 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + ((419927 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x) + (((158367 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x + (((-55345 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + ((637100 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x))) + ((((1695692 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x + ((-1576236 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x) + (((-178234 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + (((-374293 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x + ((-488773 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x)))) := by
  rw [node228_check, Integer.Sparse.eval_merge]
  rw [node223_eval, node227_eval]

theorem node229_check : node229 =
    Integer.Sparse.merge (Integer.Sparse.scale (996503) entry_11_10) (Integer.Sparse.scale (1840985) entry_11_11) := by decide +kernel

theorem node229_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node229 x = (((996503 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x + ((1840985 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x) := by
  rw [node229_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node230_check : node230 =
    Integer.Sparse.merge (Integer.Sparse.scale (-606873) entry_11_13) (Integer.Sparse.scale (1777812) entry_11_14) := by decide +kernel

theorem node230_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node230 x = (((-606873 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + ((1777812 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x) := by
  rw [node230_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node231_check : node231 =
    Integer.Sparse.merge (Integer.Sparse.scale (3483873) entry_11_12) node230 := by decide +kernel

theorem node231_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node231 x = (((3483873 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x + (((-606873 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + ((1777812 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x)) := by
  rw [node231_check, Integer.Sparse.eval_merge]
  rw [node230_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node232_check : node232 =
    Integer.Sparse.merge node229 node231 := by decide +kernel

theorem node232_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node232 x = ((((996503 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x + ((1840985 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x) + (((3483873 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x + (((-606873 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + ((1777812 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x))) := by
  rw [node232_check, Integer.Sparse.eval_merge]
  rw [node229_eval, node231_eval]

theorem node233_check : node233 =
    Integer.Sparse.merge (Integer.Sparse.scale (-757413) entry_11_16) (Integer.Sparse.scale (1395572) entry_11_17) := by decide +kernel

theorem node233_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node233 x = (((-757413 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + ((1395572 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x) := by
  rw [node233_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node234_check : node234 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3265860) entry_11_15) node233 := by decide +kernel

theorem node234_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node234 x = (((-3265860 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x + (((-757413 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + ((1395572 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x)) := by
  rw [node234_check, Integer.Sparse.eval_merge]
  rw [node233_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node235_check : node235 =
    Integer.Sparse.merge (Integer.Sparse.scale (-838818) entry_11_19) (Integer.Sparse.scale (905478) entry_11_20) := by decide +kernel

theorem node235_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node235 x = (((-838818 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x + ((905478 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x) := by
  rw [node235_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node236_check : node236 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2418328) entry_11_18) node235 := by decide +kernel

theorem node236_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node236 x = (((-2418328 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x + (((-838818 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x + ((905478 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x)) := by
  rw [node236_check, Integer.Sparse.eval_merge]
  rw [node235_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node237_check : node237 =
    Integer.Sparse.merge node234 node236 := by decide +kernel

theorem node237_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node237 x = ((((-3265860 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x + (((-757413 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + ((1395572 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x)) + (((-2418328 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x + (((-838818 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x + ((905478 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x))) := by
  rw [node237_check, Integer.Sparse.eval_merge]
  rw [node234_eval, node236_eval]

theorem node238_check : node238 =
    Integer.Sparse.merge node232 node237 := by decide +kernel

theorem node238_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node238 x = (((((996503 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x + ((1840985 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x) + (((3483873 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x + (((-606873 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + ((1777812 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x))) + ((((-3265860 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x + (((-757413 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + ((1395572 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x)) + (((-2418328 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x + (((-838818 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x + ((905478 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x)))) := by
  rw [node238_check, Integer.Sparse.eval_merge]
  rw [node232_eval, node237_eval]

theorem node239_check : node239 =
    Integer.Sparse.merge node228 node238 := by decide +kernel

theorem node239_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node239 x = ((((((-1203380 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + ((419927 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x) + (((158367 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x + (((-55345 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + ((637100 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x))) + ((((1695692 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x + ((-1576236 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x) + (((-178234 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + (((-374293 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x + ((-488773 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x)))) + (((((996503 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x + ((1840985 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x) + (((3483873 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x + (((-606873 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + ((1777812 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x))) + ((((-3265860 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x + (((-757413 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + ((1395572 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x)) + (((-2418328 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x + (((-838818 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x + ((905478 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x))))) := by
  rw [node239_check, Integer.Sparse.eval_merge]
  rw [node228_eval, node238_eval]

theorem node240_check : node240 =
    Integer.Sparse.merge (Integer.Sparse.scale (208493) entry_12_0) (Integer.Sparse.scale (3385699) entry_12_1) := by decide +kernel

theorem node240_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node240 x = (((208493 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_0 x + ((3385699 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_1 x) := by
  rw [node240_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node241_check : node241 =
    Integer.Sparse.merge (Integer.Sparse.scale (-724852) entry_12_3) (Integer.Sparse.scale (3794703) entry_12_4) := by decide +kernel

theorem node241_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node241 x = (((-724852 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_3 x + ((3794703 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x) := by
  rw [node241_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node242_check : node242 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2343572) entry_12_2) node241 := by decide +kernel

theorem node242_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node242 x = (((-2343572 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_2 x + (((-724852 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_3 x + ((3794703 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x)) := by
  rw [node242_check, Integer.Sparse.eval_merge]
  rw [node241_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node243_check : node243 =
    Integer.Sparse.merge node240 node242 := by decide +kernel

theorem node243_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node243 x = ((((208493 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_0 x + ((3385699 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_1 x) + (((-2343572 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_2 x + (((-724852 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_3 x + ((3794703 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x))) := by
  rw [node243_check, Integer.Sparse.eval_merge]
  rw [node240_eval, node242_eval]

theorem node244_check : node244 =
    Integer.Sparse.merge (Integer.Sparse.scale (1212441) entry_12_5) (Integer.Sparse.scale (-8279149) entry_12_6) := by decide +kernel

theorem node244_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node244 x = (((1212441 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_5 x + ((-8279149 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_6 x) := by
  rw [node244_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node245_check : node245 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3151845) entry_12_8) (Integer.Sparse.scale (-9664796) entry_12_9) := by decide +kernel

theorem node245_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node245 x = (((-3151845 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_8 x + ((-9664796 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_9 x) := by
  rw [node245_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node246_check : node246 =
    Integer.Sparse.merge (Integer.Sparse.scale (1114705) entry_12_7) node245 := by decide +kernel

theorem node246_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node246 x = (((1114705 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_7 x + (((-3151845 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_8 x + ((-9664796 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_9 x)) := by
  rw [node246_check, Integer.Sparse.eval_merge]
  rw [node245_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node247_check : node247 =
    Integer.Sparse.merge node244 node246 := by decide +kernel

theorem node247_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node247 x = ((((1212441 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_5 x + ((-8279149 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_6 x) + (((1114705 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_7 x + (((-3151845 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_8 x + ((-9664796 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_9 x))) := by
  rw [node247_check, Integer.Sparse.eval_merge]
  rw [node244_eval, node246_eval]

theorem node248_check : node248 =
    Integer.Sparse.merge node243 node247 := by decide +kernel

theorem node248_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node248 x = (((((208493 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_0 x + ((3385699 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_1 x) + (((-2343572 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_2 x + (((-724852 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_3 x + ((3794703 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x))) + ((((1212441 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_5 x + ((-8279149 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_6 x) + (((1114705 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_7 x + (((-3151845 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_8 x + ((-9664796 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_9 x)))) := by
  rw [node248_check, Integer.Sparse.eval_merge]
  rw [node243_eval, node247_eval]

theorem node249_check : node249 =
    Integer.Sparse.merge (Integer.Sparse.scale (1912285) entry_12_10) (Integer.Sparse.scale (3483873) entry_12_11) := by decide +kernel

theorem node249_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node249 x = (((1912285 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_10 x + ((3483873 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_11 x) := by
  rw [node249_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node250_check : node250 =
    Integer.Sparse.merge (Integer.Sparse.scale (-474182) entry_12_13) (Integer.Sparse.scale (3152718) entry_12_14) := by decide +kernel

theorem node250_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node250 x = (((-474182 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_13 x + ((3152718 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_14 x) := by
  rw [node250_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node251_check : node251 =
    Integer.Sparse.merge (Integer.Sparse.scale (33924189) entry_12_12) node250 := by decide +kernel

theorem node251_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node251 x = (((33924189 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_12 x + (((-474182 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_13 x + ((3152718 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_14 x)) := by
  rw [node251_check, Integer.Sparse.eval_merge]
  rw [node250_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node252_check : node252 =
    Integer.Sparse.merge node249 node251 := by decide +kernel

theorem node252_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node252 x = ((((1912285 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_10 x + ((3483873 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_11 x) + (((33924189 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_12 x + (((-474182 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_13 x + ((3152718 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_14 x))) := by
  rw [node252_check, Integer.Sparse.eval_merge]
  rw [node249_eval, node251_eval]

theorem node253_check : node253 =
    Integer.Sparse.merge (Integer.Sparse.scale (-13773212) entry_12_16) (Integer.Sparse.scale (-390763) entry_12_17) := by decide +kernel

theorem node253_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node253 x = (((-13773212 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_16 x + ((-390763 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_17 x) := by
  rw [node253_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node254_check : node254 =
    Integer.Sparse.merge (Integer.Sparse.scale (-16306805) entry_12_15) node253 := by decide +kernel

theorem node254_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node254 x = (((-16306805 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_15 x + (((-13773212 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_16 x + ((-390763 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_17 x)) := by
  rw [node254_check, Integer.Sparse.eval_merge]
  rw [node253_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node255_check : node255 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3874823) entry_12_19) (Integer.Sparse.scale (-9593464) entry_12_20) := by decide +kernel

theorem node255_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node255 x = (((-3874823 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_19 x + ((-9593464 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_20 x) := by
  rw [node255_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node256_check : node256 =
    Integer.Sparse.merge (Integer.Sparse.scale (-23030655) entry_12_18) node255 := by decide +kernel

theorem node256_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node256 x = (((-23030655 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_18 x + (((-3874823 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_19 x + ((-9593464 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_20 x)) := by
  rw [node256_check, Integer.Sparse.eval_merge]
  rw [node255_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node257_check : node257 =
    Integer.Sparse.merge node254 node256 := by decide +kernel

theorem node257_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node257 x = ((((-16306805 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_15 x + (((-13773212 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_16 x + ((-390763 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_17 x)) + (((-23030655 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_18 x + (((-3874823 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_19 x + ((-9593464 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_20 x))) := by
  rw [node257_check, Integer.Sparse.eval_merge]
  rw [node254_eval, node256_eval]

theorem node258_check : node258 =
    Integer.Sparse.merge node252 node257 := by decide +kernel

theorem node258_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node258 x = (((((1912285 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_10 x + ((3483873 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_11 x) + (((33924189 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_12 x + (((-474182 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_13 x + ((3152718 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_14 x))) + ((((-16306805 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_15 x + (((-13773212 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_16 x + ((-390763 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_17 x)) + (((-23030655 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_18 x + (((-3874823 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_19 x + ((-9593464 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_20 x)))) := by
  rw [node258_check, Integer.Sparse.eval_merge]
  rw [node252_eval, node257_eval]

theorem node259_check : node259 =
    Integer.Sparse.merge node248 node258 := by decide +kernel

theorem node259_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node259 x = ((((((208493 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_0 x + ((3385699 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_1 x) + (((-2343572 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_2 x + (((-724852 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_3 x + ((3794703 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x))) + ((((1212441 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_5 x + ((-8279149 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_6 x) + (((1114705 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_7 x + (((-3151845 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_8 x + ((-9664796 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_9 x)))) + (((((1912285 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_10 x + ((3483873 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_11 x) + (((33924189 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_12 x + (((-474182 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_13 x + ((3152718 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_14 x))) + ((((-16306805 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_15 x + (((-13773212 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_16 x + ((-390763 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_17 x)) + (((-23030655 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_18 x + (((-3874823 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_19 x + ((-9593464 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_20 x))))) := by
  rw [node259_check, Integer.Sparse.eval_merge]
  rw [node248_eval, node258_eval]

theorem node260_check : node260 =
    Integer.Sparse.merge (Integer.Sparse.scale (1265023) entry_13_0) (Integer.Sparse.scale (-52654) entry_13_1) := by decide +kernel

theorem node260_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node260 x = (((1265023 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_0 x + ((-52654 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_1 x) := by
  rw [node260_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node261_check : node261 =
    Integer.Sparse.merge (Integer.Sparse.scale (26271) entry_13_3) (Integer.Sparse.scale (-673257) entry_13_4) := by decide +kernel

theorem node261_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node261 x = (((26271 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_3 x + ((-673257 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_4 x) := by
  rw [node261_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node262_check : node262 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1105957) entry_13_2) node261 := by decide +kernel

theorem node262_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node262 x = (((-1105957 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_2 x + (((26271 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_3 x + ((-673257 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_4 x)) := by
  rw [node262_check, Integer.Sparse.eval_merge]
  rw [node261_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node263_check : node263 =
    Integer.Sparse.merge node260 node262 := by decide +kernel

theorem node263_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node263 x = ((((1265023 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_0 x + ((-52654 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_1 x) + (((-1105957 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_2 x + (((26271 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_3 x + ((-673257 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_4 x))) := by
  rw [node263_check, Integer.Sparse.eval_merge]
  rw [node260_eval, node262_eval]

theorem node264_check : node264 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2053220) entry_13_5) (Integer.Sparse.scale (1211833) entry_13_6) := by decide +kernel

theorem node264_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node264 x = (((-2053220 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_5 x + ((1211833 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_6 x) := by
  rw [node264_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node265_check : node265 =
    Integer.Sparse.merge (Integer.Sparse.scale (175194) entry_13_8) (Integer.Sparse.scale (1241050) entry_13_9) := by decide +kernel

theorem node265_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node265 x = (((175194 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_8 x + ((1241050 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_9 x) := by
  rw [node265_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node266_check : node266 =
    Integer.Sparse.merge (Integer.Sparse.scale (-133074) entry_13_7) node265 := by decide +kernel

theorem node266_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node266 x = (((-133074 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_7 x + (((175194 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_8 x + ((1241050 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_9 x)) := by
  rw [node266_check, Integer.Sparse.eval_merge]
  rw [node265_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node267_check : node267 =
    Integer.Sparse.merge node264 node266 := by decide +kernel

theorem node267_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node267 x = ((((-2053220 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_5 x + ((1211833 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_6 x) + (((-133074 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_7 x + (((175194 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_8 x + ((1241050 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_9 x))) := by
  rw [node267_check, Integer.Sparse.eval_merge]
  rw [node264_eval, node266_eval]

theorem node268_check : node268 =
    Integer.Sparse.merge node263 node267 := by decide +kernel

theorem node268_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node268 x = (((((1265023 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_0 x + ((-52654 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_1 x) + (((-1105957 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_2 x + (((26271 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_3 x + ((-673257 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_4 x))) + ((((-2053220 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_5 x + ((1211833 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_6 x) + (((-133074 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_7 x + (((175194 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_8 x + ((1241050 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_9 x)))) := by
  rw [node268_check, Integer.Sparse.eval_merge]
  rw [node263_eval, node267_eval]

theorem node269_check : node269 =
    Integer.Sparse.merge (Integer.Sparse.scale (-343789) entry_13_10) (Integer.Sparse.scale (-606873) entry_13_11) := by decide +kernel

theorem node269_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node269 x = (((-343789 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_10 x + ((-606873 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_11 x) := by
  rw [node269_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node270_check : node270 =
    Integer.Sparse.merge (Integer.Sparse.scale (1191495) entry_13_13) (Integer.Sparse.scale (-785273) entry_13_14) := by decide +kernel

theorem node270_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node270 x = (((1191495 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_13 x + ((-785273 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x) := by
  rw [node270_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node271_check : node271 =
    Integer.Sparse.merge (Integer.Sparse.scale (-474182) entry_13_12) node270 := by decide +kernel

theorem node271_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node271 x = (((-474182 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_12 x + (((1191495 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_13 x + ((-785273 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x)) := by
  rw [node271_check, Integer.Sparse.eval_merge]
  rw [node270_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node272_check : node272 =
    Integer.Sparse.merge node269 node271 := by decide +kernel

theorem node272_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node272 x = ((((-343789 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_10 x + ((-606873 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_11 x) + (((-474182 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_12 x + (((1191495 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_13 x + ((-785273 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x))) := by
  rw [node272_check, Integer.Sparse.eval_merge]
  rw [node269_eval, node271_eval]

theorem node273_check : node273 =
    Integer.Sparse.merge (Integer.Sparse.scale (-563678) entry_13_16) (Integer.Sparse.scale (-2506791) entry_13_17) := by decide +kernel

theorem node273_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node273 x = (((-563678 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + ((-2506791 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x) := by
  rw [node273_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node274_check : node274 =
    Integer.Sparse.merge (Integer.Sparse.scale (1774465) entry_13_15) node273 := by decide +kernel

theorem node274_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node274 x = (((1774465 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x + (((-563678 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + ((-2506791 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x)) := by
  rw [node274_check, Integer.Sparse.eval_merge]
  rw [node273_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node275_check : node275 =
    Integer.Sparse.merge (Integer.Sparse.scale (897209) entry_13_19) (Integer.Sparse.scale (-1728565) entry_13_20) := by decide +kernel

theorem node275_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node275 x = (((897209 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x + ((-1728565 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x) := by
  rw [node275_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node276_check : node276 =
    Integer.Sparse.merge (Integer.Sparse.scale (-760335) entry_13_18) node275 := by decide +kernel

theorem node276_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node276 x = (((-760335 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x + (((897209 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x + ((-1728565 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x)) := by
  rw [node276_check, Integer.Sparse.eval_merge]
  rw [node275_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node277_check : node277 =
    Integer.Sparse.merge node274 node276 := by decide +kernel

theorem node277_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node277 x = ((((1774465 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x + (((-563678 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + ((-2506791 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x)) + (((-760335 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x + (((897209 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x + ((-1728565 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x))) := by
  rw [node277_check, Integer.Sparse.eval_merge]
  rw [node274_eval, node276_eval]

theorem node278_check : node278 =
    Integer.Sparse.merge node272 node277 := by decide +kernel

theorem node278_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node278 x = (((((-343789 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_10 x + ((-606873 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_11 x) + (((-474182 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_12 x + (((1191495 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_13 x + ((-785273 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x))) + ((((1774465 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x + (((-563678 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + ((-2506791 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x)) + (((-760335 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x + (((897209 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x + ((-1728565 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x)))) := by
  rw [node278_check, Integer.Sparse.eval_merge]
  rw [node272_eval, node277_eval]

theorem node279_check : node279 =
    Integer.Sparse.merge node268 node278 := by decide +kernel

theorem node279_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node279 x = ((((((1265023 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_0 x + ((-52654 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_1 x) + (((-1105957 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_2 x + (((26271 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_3 x + ((-673257 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_4 x))) + ((((-2053220 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_5 x + ((1211833 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_6 x) + (((-133074 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_7 x + (((175194 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_8 x + ((1241050 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_9 x)))) + (((((-343789 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_10 x + ((-606873 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_11 x) + (((-474182 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_12 x + (((1191495 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_13 x + ((-785273 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x))) + ((((1774465 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x + (((-563678 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + ((-2506791 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x)) + (((-760335 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x + (((897209 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x + ((-1728565 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x))))) := by
  rw [node279_check, Integer.Sparse.eval_merge]
  rw [node268_eval, node278_eval]

theorem node280_check : node280 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3980129) entry_14_0) (Integer.Sparse.scale (-72835) entry_14_1) := by decide +kernel

theorem node280_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node280 x = (((-3980129 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_0 x + ((-72835 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x) := by
  rw [node280_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node281_check : node281 =
    Integer.Sparse.merge (Integer.Sparse.scale (-167456) entry_14_3) (Integer.Sparse.scale (1902740) entry_14_4) := by decide +kernel

theorem node281_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node281 x = (((-167456 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + ((1902740 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x) := by
  rw [node281_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node282_check : node282 =
    Integer.Sparse.merge (Integer.Sparse.scale (1559599) entry_14_2) node281 := by decide +kernel

theorem node282_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node282 x = (((1559599 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x + (((-167456 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + ((1902740 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x)) := by
  rw [node282_check, Integer.Sparse.eval_merge]
  rw [node281_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node283_check : node283 =
    Integer.Sparse.merge node280 node282 := by decide +kernel

theorem node283_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node283 x = ((((-3980129 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_0 x + ((-72835 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x) + (((1559599 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x + (((-167456 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + ((1902740 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x))) := by
  rw [node283_check, Integer.Sparse.eval_merge]
  rw [node280_eval, node282_eval]

theorem node284_check : node284 =
    Integer.Sparse.merge (Integer.Sparse.scale (2143288) entry_14_5) (Integer.Sparse.scale (-2161046) entry_14_6) := by decide +kernel

theorem node284_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node284 x = (((2143288 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x + ((-2161046 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_6 x) := by
  rw [node284_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node285_check : node285 =
    Integer.Sparse.merge (Integer.Sparse.scale (-218282) entry_14_8) (Integer.Sparse.scale (2081231) entry_14_9) := by decide +kernel

theorem node285_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node285 x = (((-218282 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x + ((2081231 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x) := by
  rw [node285_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node286_check : node286 =
    Integer.Sparse.merge (Integer.Sparse.scale (339938) entry_14_7) node285 := by decide +kernel

theorem node286_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node286 x = (((339938 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x + (((-218282 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x + ((2081231 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x)) := by
  rw [node286_check, Integer.Sparse.eval_merge]
  rw [node285_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node287_check : node287 =
    Integer.Sparse.merge node284 node286 := by decide +kernel

theorem node287_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node287 x = ((((2143288 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x + ((-2161046 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_6 x) + (((339938 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x + (((-218282 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x + ((2081231 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x))) := by
  rw [node287_check, Integer.Sparse.eval_merge]
  rw [node284_eval, node286_eval]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node288_check : node288 =
    Integer.Sparse.merge node283 node287 := by decide +kernel

theorem node288_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node288 x = (((((-3980129 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_0 x + ((-72835 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x) + (((1559599 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x + (((-167456 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + ((1902740 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x))) + ((((2143288 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x + ((-2161046 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_6 x) + (((339938 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x + (((-218282 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x + ((2081231 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x)))) := by
  rw [node288_check, Integer.Sparse.eval_merge]
  rw [node283_eval, node287_eval]

theorem node289_check : node289 =
    Integer.Sparse.merge (Integer.Sparse.scale (1767463) entry_14_10) (Integer.Sparse.scale (1777812) entry_14_11) := by decide +kernel

theorem node289_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node289 x = (((1767463 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x + ((1777812 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x) := by
  rw [node289_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node290_check : node290 =
    Integer.Sparse.merge (Integer.Sparse.scale (-785273) entry_14_13) (Integer.Sparse.scale (4167901) entry_14_14) := by decide +kernel

theorem node290_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node290 x = (((-785273 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_13 x + ((4167901 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x) := by
  rw [node290_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node291_check : node291 =
    Integer.Sparse.merge (Integer.Sparse.scale (3152718) entry_14_12) node290 := by decide +kernel

theorem node291_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node291 x = (((3152718 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x + (((-785273 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_13 x + ((4167901 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x)) := by
  rw [node291_check, Integer.Sparse.eval_merge]
  rw [node290_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node292_check : node292 =
    Integer.Sparse.merge node289 node291 := by decide +kernel

theorem node292_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node292 x = ((((1767463 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x + ((1777812 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x) + (((3152718 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x + (((-785273 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_13 x + ((4167901 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x))) := by
  rw [node292_check, Integer.Sparse.eval_merge]
  rw [node289_eval, node291_eval]

theorem node293_check : node293 =
    Integer.Sparse.merge (Integer.Sparse.scale (1019431) entry_14_16) (Integer.Sparse.scale (2549610) entry_14_17) := by decide +kernel

theorem node293_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node293 x = (((1019431 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + ((2549610 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x) := by
  rw [node293_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node294_check : node294 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4625257) entry_14_15) node293 := by decide +kernel

theorem node294_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node294 x = (((-4625257 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x + (((1019431 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + ((2549610 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x)) := by
  rw [node294_check, Integer.Sparse.eval_merge]
  rw [node293_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node295_check : node295 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1143525) entry_14_19) (Integer.Sparse.scale (4379858) entry_14_20) := by decide +kernel

theorem node295_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node295 x = (((-1143525 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x + ((4379858 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_20 x) := by
  rw [node295_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node296_check : node296 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4161086) entry_14_18) node295 := by decide +kernel

theorem node296_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node296 x = (((-4161086 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x + (((-1143525 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x + ((4379858 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_20 x)) := by
  rw [node296_check, Integer.Sparse.eval_merge]
  rw [node295_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node297_check : node297 =
    Integer.Sparse.merge node294 node296 := by decide +kernel

theorem node297_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node297 x = ((((-4625257 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x + (((1019431 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + ((2549610 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x)) + (((-4161086 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x + (((-1143525 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x + ((4379858 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_20 x))) := by
  rw [node297_check, Integer.Sparse.eval_merge]
  rw [node294_eval, node296_eval]

theorem node298_check : node298 =
    Integer.Sparse.merge node292 node297 := by decide +kernel

theorem node298_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node298 x = (((((1767463 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x + ((1777812 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x) + (((3152718 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x + (((-785273 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_13 x + ((4167901 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x))) + ((((-4625257 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x + (((1019431 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + ((2549610 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x)) + (((-4161086 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x + (((-1143525 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x + ((4379858 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_20 x)))) := by
  rw [node298_check, Integer.Sparse.eval_merge]
  rw [node292_eval, node297_eval]

theorem node299_check : node299 =
    Integer.Sparse.merge node288 node298 := by decide +kernel

theorem node299_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node299 x = ((((((-3980129 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_0 x + ((-72835 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x) + (((1559599 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x + (((-167456 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + ((1902740 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x))) + ((((2143288 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x + ((-2161046 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_6 x) + (((339938 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x + (((-218282 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x + ((2081231 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x)))) + (((((1767463 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x + ((1777812 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x) + (((3152718 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x + (((-785273 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_13 x + ((4167901 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x))) + ((((-4625257 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x + (((1019431 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + ((2549610 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x)) + (((-4161086 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x + (((-1143525 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x + ((4379858 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_20 x))))) := by
  rw [node299_check, Integer.Sparse.eval_merge]
  rw [node288_eval, node298_eval]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node320_check : node320 =
    Integer.Sparse.merge (Integer.Sparse.scale (-5318840) entry_16_0) (Integer.Sparse.scale (-1304244) entry_16_1) := by decide +kernel

theorem node320_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node320 x = (((-5318840 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_0 x + ((-1304244 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_1 x) := by
  rw [node320_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node321_check : node321 =
    Integer.Sparse.merge (Integer.Sparse.scale (-578406) entry_16_3) (Integer.Sparse.scale (-316085) entry_16_4) := by decide +kernel

theorem node321_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node321 x = (((-578406 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_3 x + ((-316085 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_4 x) := by
  rw [node321_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node322_check : node322 =
    Integer.Sparse.merge (Integer.Sparse.scale (940149) entry_16_2) node321 := by decide +kernel

theorem node322_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node322 x = (((940149 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_2 x + (((-578406 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_3 x + ((-316085 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_4 x)) := by
  rw [node322_check, Integer.Sparse.eval_merge]
  rw [node321_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node323_check : node323 =
    Integer.Sparse.merge node320 node322 := by decide +kernel

theorem node323_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node323 x = ((((-5318840 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_0 x + ((-1304244 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_1 x) + (((940149 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_2 x + (((-578406 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_3 x + ((-316085 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_4 x))) := by
  rw [node323_check, Integer.Sparse.eval_merge]
  rw [node320_eval, node322_eval]

theorem node324_check : node324 =
    Integer.Sparse.merge (Integer.Sparse.scale (-137926) entry_16_5) (Integer.Sparse.scale (1708504) entry_16_6) := by decide +kernel

theorem node324_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node324 x = (((-137926 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_5 x + ((1708504 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_6 x) := by
  rw [node324_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node325_check : node325 =
    Integer.Sparse.merge (Integer.Sparse.scale (691622) entry_16_8) (Integer.Sparse.scale (11353138) entry_16_9) := by decide +kernel

theorem node325_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node325 x = (((691622 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_8 x + ((11353138 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_9 x) := by
  rw [node325_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node326_check : node326 =
    Integer.Sparse.merge (Integer.Sparse.scale (979706) entry_16_7) node325 := by decide +kernel

theorem node326_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node326 x = (((979706 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_7 x + (((691622 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_8 x + ((11353138 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_9 x)) := by
  rw [node326_check, Integer.Sparse.eval_merge]
  rw [node325_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node327_check : node327 =
    Integer.Sparse.merge node324 node326 := by decide +kernel

theorem node327_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node327 x = ((((-137926 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_5 x + ((1708504 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_6 x) + (((979706 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_7 x + (((691622 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_8 x + ((11353138 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_9 x))) := by
  rw [node327_check, Integer.Sparse.eval_merge]
  rw [node324_eval, node326_eval]

theorem node328_check : node328 =
    Integer.Sparse.merge node323 node327 := by decide +kernel

theorem node328_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node328 x = (((((-5318840 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_0 x + ((-1304244 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_1 x) + (((940149 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_2 x + (((-578406 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_3 x + ((-316085 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_4 x))) + ((((-137926 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_5 x + ((1708504 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_6 x) + (((979706 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_7 x + (((691622 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_8 x + ((11353138 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_9 x)))) := by
  rw [node328_check, Integer.Sparse.eval_merge]
  rw [node323_eval, node327_eval]

theorem node329_check : node329 =
    Integer.Sparse.merge (Integer.Sparse.scale (174111) entry_16_10) (Integer.Sparse.scale (-757413) entry_16_11) := by decide +kernel

theorem node329_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node329 x = (((174111 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_10 x + ((-757413 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_11 x) := by
  rw [node329_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node330_check : node330 =
    Integer.Sparse.merge (Integer.Sparse.scale (-563678) entry_16_13) (Integer.Sparse.scale (1019431) entry_16_14) := by decide +kernel

theorem node330_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node330 x = (((-563678 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_13 x + ((1019431 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_14 x) := by
  rw [node330_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node331_check : node331 =
    Integer.Sparse.merge (Integer.Sparse.scale (-13773212) entry_16_12) node330 := by decide +kernel

theorem node331_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node331 x = (((-13773212 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_12 x + (((-563678 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_13 x + ((1019431 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_14 x)) := by
  rw [node331_check, Integer.Sparse.eval_merge]
  rw [node330_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node332_check : node332 =
    Integer.Sparse.merge node329 node331 := by decide +kernel

theorem node332_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node332 x = ((((174111 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_10 x + ((-757413 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_11 x) + (((-13773212 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_12 x + (((-563678 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_13 x + ((1019431 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_14 x))) := by
  rw [node332_check, Integer.Sparse.eval_merge]
  rw [node329_eval, node331_eval]

theorem node333_check : node333 =
    Integer.Sparse.merge (Integer.Sparse.scale (12230833) entry_16_16) (Integer.Sparse.scale (1826615) entry_16_17) := by decide +kernel

theorem node333_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node333 x = (((12230833 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_16 x + ((1826615 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_17 x) := by
  rw [node333_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node334_check : node334 =
    Integer.Sparse.merge (Integer.Sparse.scale (3981236) entry_16_15) node333 := by decide +kernel

theorem node334_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node334 x = (((3981236 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_15 x + (((12230833 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_16 x + ((1826615 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_17 x)) := by
  rw [node334_check, Integer.Sparse.eval_merge]
  rw [node333_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node335_check : node335 =
    Integer.Sparse.merge (Integer.Sparse.scale (842121) entry_16_19) (Integer.Sparse.scale (10905753) entry_16_20) := by decide +kernel

theorem node335_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node335 x = (((842121 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_19 x + ((10905753 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_20 x) := by
  rw [node335_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node336_check : node336 =
    Integer.Sparse.merge (Integer.Sparse.scale (10606059) entry_16_18) node335 := by decide +kernel

theorem node336_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node336 x = (((10606059 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_18 x + (((842121 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_19 x + ((10905753 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_20 x)) := by
  rw [node336_check, Integer.Sparse.eval_merge]
  rw [node335_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node337_check : node337 =
    Integer.Sparse.merge node334 node336 := by decide +kernel

theorem node337_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node337 x = ((((3981236 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_15 x + (((12230833 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_16 x + ((1826615 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_17 x)) + (((10606059 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_18 x + (((842121 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_19 x + ((10905753 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_20 x))) := by
  rw [node337_check, Integer.Sparse.eval_merge]
  rw [node334_eval, node336_eval]

theorem node338_check : node338 =
    Integer.Sparse.merge node332 node337 := by decide +kernel

theorem node338_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node338 x = (((((174111 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_10 x + ((-757413 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_11 x) + (((-13773212 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_12 x + (((-563678 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_13 x + ((1019431 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_14 x))) + ((((3981236 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_15 x + (((12230833 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_16 x + ((1826615 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_17 x)) + (((10606059 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_18 x + (((842121 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_19 x + ((10905753 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_20 x)))) := by
  rw [node338_check, Integer.Sparse.eval_merge]
  rw [node332_eval, node337_eval]

theorem node339_check : node339 =
    Integer.Sparse.merge node328 node338 := by decide +kernel

theorem node339_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node339 x = ((((((-5318840 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_0 x + ((-1304244 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_1 x) + (((940149 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_2 x + (((-578406 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_3 x + ((-316085 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_4 x))) + ((((-137926 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_5 x + ((1708504 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_6 x) + (((979706 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_7 x + (((691622 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_8 x + ((11353138 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_9 x)))) + (((((174111 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_10 x + ((-757413 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_11 x) + (((-13773212 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_12 x + (((-563678 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_13 x + ((1019431 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_14 x))) + ((((3981236 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_15 x + (((12230833 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_16 x + ((1826615 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_17 x)) + (((10606059 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_18 x + (((842121 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_19 x + ((10905753 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_20 x))))) := by
  rw [node339_check, Integer.Sparse.eval_merge]
  rw [node328_eval, node338_eval]

theorem node340_check : node340 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2763722) entry_17_0) (Integer.Sparse.scale (-320066) entry_17_1) := by decide +kernel

theorem node340_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node340 x = (((-2763722 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_0 x + ((-320066 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_1 x) := by
  rw [node340_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node341_check : node341 =
    Integer.Sparse.merge (Integer.Sparse.scale (64222) entry_17_3) (Integer.Sparse.scale (1025294) entry_17_4) := by decide +kernel

theorem node341_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node341 x = (((64222 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_3 x + ((1025294 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_4 x) := by
  rw [node341_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node342_check : node342 =
    Integer.Sparse.merge (Integer.Sparse.scale (2067282) entry_17_2) node341 := by decide +kernel

theorem node342_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node342 x = (((2067282 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_2 x + (((64222 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_3 x + ((1025294 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_4 x)) := by
  rw [node342_check, Integer.Sparse.eval_merge]
  rw [node341_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node343_check : node343 =
    Integer.Sparse.merge node340 node342 := by decide +kernel

theorem node343_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node343 x = ((((-2763722 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_0 x + ((-320066 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_1 x) + (((2067282 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_2 x + (((64222 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_3 x + ((1025294 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_4 x))) := by
  rw [node343_check, Integer.Sparse.eval_merge]
  rw [node340_eval, node342_eval]

theorem node344_check : node344 =
    Integer.Sparse.merge (Integer.Sparse.scale (5235805) entry_17_5) (Integer.Sparse.scale (-2418137) entry_17_6) := by decide +kernel

theorem node344_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node344 x = (((5235805 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_5 x + ((-2418137 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_6 x) := by
  rw [node344_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node345_check : node345 =
    Integer.Sparse.merge (Integer.Sparse.scale (-213776) entry_17_8) (Integer.Sparse.scale (-1846105) entry_17_9) := by decide +kernel

theorem node345_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node345 x = (((-213776 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_8 x + ((-1846105 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_9 x) := by
  rw [node345_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node346_check : node346 =
    Integer.Sparse.merge (Integer.Sparse.scale (808468) entry_17_7) node345 := by decide +kernel

theorem node346_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node346 x = (((808468 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_7 x + (((-213776 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_8 x + ((-1846105 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_9 x)) := by
  rw [node346_check, Integer.Sparse.eval_merge]
  rw [node345_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node347_check : node347 =
    Integer.Sparse.merge node344 node346 := by decide +kernel

theorem node347_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node347 x = ((((5235805 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_5 x + ((-2418137 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_6 x) + (((808468 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_7 x + (((-213776 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_8 x + ((-1846105 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_9 x))) := by
  rw [node347_check, Integer.Sparse.eval_merge]
  rw [node344_eval, node346_eval]

theorem node348_check : node348 =
    Integer.Sparse.merge node343 node347 := by decide +kernel

theorem node348_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node348 x = (((((-2763722 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_0 x + ((-320066 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_1 x) + (((2067282 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_2 x + (((64222 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_3 x + ((1025294 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_4 x))) + ((((5235805 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_5 x + ((-2418137 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_6 x) + (((808468 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_7 x + (((-213776 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_8 x + ((-1846105 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_9 x)))) := by
  rw [node348_check, Integer.Sparse.eval_merge]
  rw [node343_eval, node347_eval]

theorem node349_check : node349 =
    Integer.Sparse.merge (Integer.Sparse.scale (1098524) entry_17_10) (Integer.Sparse.scale (1395572) entry_17_11) := by decide +kernel

theorem node349_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node349 x = (((1098524 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_10 x + ((1395572 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_11 x) := by
  rw [node349_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node350_check : node350 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2506791) entry_17_13) (Integer.Sparse.scale (2549610) entry_17_14) := by decide +kernel

theorem node350_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node350 x = (((-2506791 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_13 x + ((2549610 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_14 x) := by
  rw [node350_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node351_check : node351 =
    Integer.Sparse.merge (Integer.Sparse.scale (-390763) entry_17_12) node350 := by decide +kernel

theorem node351_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node351 x = (((-390763 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_12 x + (((-2506791 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_13 x + ((2549610 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_14 x)) := by
  rw [node351_check, Integer.Sparse.eval_merge]
  rw [node350_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node352_check : node352 =
    Integer.Sparse.merge node349 node351 := by decide +kernel

theorem node352_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node352 x = ((((1098524 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_10 x + ((1395572 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_11 x) + (((-390763 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_12 x + (((-2506791 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_13 x + ((2549610 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_14 x))) := by
  rw [node352_check, Integer.Sparse.eval_merge]
  rw [node349_eval, node351_eval]

theorem node353_check : node353 =
    Integer.Sparse.merge (Integer.Sparse.scale (1826615) entry_17_16) (Integer.Sparse.scale (6914992) entry_17_17) := by decide +kernel

theorem node353_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node353 x = (((1826615 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_16 x + ((6914992 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_17 x) := by
  rw [node353_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node354_check : node354 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3562699) entry_17_15) node353 := by decide +kernel

theorem node354_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node354 x = (((-3562699 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_15 x + (((1826615 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_16 x + ((6914992 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_17 x)) := by
  rw [node354_check, Integer.Sparse.eval_merge]
  rw [node353_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node355_check : node355 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2100658) entry_17_19) (Integer.Sparse.scale (5534083) entry_17_20) := by decide +kernel

theorem node355_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node355 x = (((-2100658 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_19 x + ((5534083 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_20 x) := by
  rw [node355_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node356_check : node356 =
    Integer.Sparse.merge (Integer.Sparse.scale (1990541) entry_17_18) node355 := by decide +kernel

theorem node356_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node356 x = (((1990541 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_18 x + (((-2100658 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_19 x + ((5534083 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_20 x)) := by
  rw [node356_check, Integer.Sparse.eval_merge]
  rw [node355_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node357_check : node357 =
    Integer.Sparse.merge node354 node356 := by decide +kernel

theorem node357_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node357 x = ((((-3562699 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_15 x + (((1826615 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_16 x + ((6914992 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_17 x)) + (((1990541 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_18 x + (((-2100658 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_19 x + ((5534083 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_20 x))) := by
  rw [node357_check, Integer.Sparse.eval_merge]
  rw [node354_eval, node356_eval]

theorem node358_check : node358 =
    Integer.Sparse.merge node352 node357 := by decide +kernel

theorem node358_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node358 x = (((((1098524 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_10 x + ((1395572 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_11 x) + (((-390763 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_12 x + (((-2506791 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_13 x + ((2549610 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_14 x))) + ((((-3562699 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_15 x + (((1826615 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_16 x + ((6914992 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_17 x)) + (((1990541 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_18 x + (((-2100658 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_19 x + ((5534083 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_20 x)))) := by
  rw [node358_check, Integer.Sparse.eval_merge]
  rw [node352_eval, node357_eval]

theorem node359_check : node359 =
    Integer.Sparse.merge node348 node358 := by decide +kernel

theorem node359_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node359 x = ((((((-2763722 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_0 x + ((-320066 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_1 x) + (((2067282 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_2 x + (((64222 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_3 x + ((1025294 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_4 x))) + ((((5235805 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_5 x + ((-2418137 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_6 x) + (((808468 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_7 x + (((-213776 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_8 x + ((-1846105 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_9 x)))) + (((((1098524 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_10 x + ((1395572 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_11 x) + (((-390763 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_12 x + (((-2506791 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_13 x + ((2549610 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_14 x))) + ((((-3562699 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_15 x + (((1826615 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_16 x + ((6914992 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_17 x)) + (((1990541 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_18 x + (((-2100658 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_19 x + ((5534083 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_20 x))))) := by
  rw [node359_check, Integer.Sparse.eval_merge]
  rw [node348_eval, node358_eval]

theorem node380_check : node380 =
    Integer.Sparse.merge (Integer.Sparse.scale (1101122) entry_19_0) (Integer.Sparse.scale (-252593) entry_19_1) := by decide +kernel

theorem node380_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node380 x = (((1101122 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + ((-252593 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x) := by
  rw [node380_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node381_check : node381 =
    Integer.Sparse.merge (Integer.Sparse.scale (153302) entry_19_3) (Integer.Sparse.scale (-921008) entry_19_4) := by decide +kernel

theorem node381_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node381 x = (((153302 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + ((-921008 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x) := by
  rw [node381_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node382_check : node382 =
    Integer.Sparse.merge (Integer.Sparse.scale (-678125) entry_19_2) node381 := by decide +kernel

theorem node382_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node382 x = (((-678125 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x + (((153302 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + ((-921008 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x)) := by
  rw [node382_check, Integer.Sparse.eval_merge]
  rw [node381_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node383_check : node383 =
    Integer.Sparse.merge node380 node382 := by decide +kernel

theorem node383_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node383 x = ((((1101122 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + ((-252593 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x) + (((-678125 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x + (((153302 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + ((-921008 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x))) := by
  rw [node383_check, Integer.Sparse.eval_merge]
  rw [node380_eval, node382_eval]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node384_check : node384 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1888253) entry_19_5) (Integer.Sparse.scale (1712829) entry_19_6) := by decide +kernel

theorem node384_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node384 x = (((-1888253 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x + ((1712829 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x) := by
  rw [node384_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node385_check : node385 =
    Integer.Sparse.merge (Integer.Sparse.scale (427205) entry_19_8) (Integer.Sparse.scale (1567125) entry_19_9) := by decide +kernel

theorem node385_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node385 x = (((427205 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x + ((1567125 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x) := by
  rw [node385_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node386_check : node386 =
    Integer.Sparse.merge (Integer.Sparse.scale (-403513) entry_19_7) node385 := by decide +kernel

theorem node386_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node386 x = (((-403513 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x + (((427205 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x + ((1567125 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x)) := by
  rw [node386_check, Integer.Sparse.eval_merge]
  rw [node385_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node387_check : node387 =
    Integer.Sparse.merge node384 node386 := by decide +kernel

theorem node387_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node387 x = ((((-1888253 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x + ((1712829 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x) + (((-403513 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x + (((427205 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x + ((1567125 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x))) := by
  rw [node387_check, Integer.Sparse.eval_merge]
  rw [node384_eval, node386_eval]

theorem node388_check : node388 =
    Integer.Sparse.merge node383 node387 := by decide +kernel

theorem node388_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node388 x = (((((1101122 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + ((-252593 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x) + (((-678125 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x + (((153302 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + ((-921008 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x))) + ((((-1888253 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x + ((1712829 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x) + (((-403513 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x + (((427205 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x + ((1567125 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x)))) := by
  rw [node388_check, Integer.Sparse.eval_merge]
  rw [node383_eval, node387_eval]

theorem node389_check : node389 =
    Integer.Sparse.merge (Integer.Sparse.scale (-498704) entry_19_10) (Integer.Sparse.scale (-838818) entry_19_11) := by decide +kernel

theorem node389_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node389 x = (((-498704 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x + ((-838818 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x) := by
  rw [node389_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node390_check : node390 =
    Integer.Sparse.merge (Integer.Sparse.scale (897209) entry_19_13) (Integer.Sparse.scale (-1143525) entry_19_14) := by decide +kernel

theorem node390_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node390 x = (((897209 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + ((-1143525 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x) := by
  rw [node390_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node391_check : node391 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3874823) entry_19_12) node390 := by decide +kernel

theorem node391_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node391 x = (((-3874823 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x + (((897209 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + ((-1143525 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x)) := by
  rw [node391_check, Integer.Sparse.eval_merge]
  rw [node390_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node392_check : node392 =
    Integer.Sparse.merge node389 node391 := by decide +kernel

theorem node392_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node392 x = ((((-498704 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x + ((-838818 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x) + (((-3874823 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x + (((897209 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + ((-1143525 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x))) := by
  rw [node392_check, Integer.Sparse.eval_merge]
  rw [node389_eval, node391_eval]

theorem node393_check : node393 =
    Integer.Sparse.merge (Integer.Sparse.scale (842121) entry_19_16) (Integer.Sparse.scale (-2100658) entry_19_17) := by decide +kernel

theorem node393_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node393 x = (((842121 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + ((-2100658 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x) := by
  rw [node393_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node394_check : node394 =
    Integer.Sparse.merge (Integer.Sparse.scale (3263582) entry_19_15) node393 := by decide +kernel

theorem node394_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node394 x = (((3263582 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x + (((842121 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + ((-2100658 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x)) := by
  rw [node394_check, Integer.Sparse.eval_merge]
  rw [node393_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node395_check : node395 =
    Integer.Sparse.merge (Integer.Sparse.scale (1293251) entry_19_19) (Integer.Sparse.scale (-963816) entry_19_20) := by decide +kernel

theorem node395_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node395 x = (((1293251 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x + ((-963816 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x) := by
  rw [node395_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node396_check : node396 =
    Integer.Sparse.merge (Integer.Sparse.scale (2123881) entry_19_18) node395 := by decide +kernel

theorem node396_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node396 x = (((2123881 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x + (((1293251 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x + ((-963816 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x)) := by
  rw [node396_check, Integer.Sparse.eval_merge]
  rw [node395_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node397_check : node397 =
    Integer.Sparse.merge node394 node396 := by decide +kernel

theorem node397_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node397 x = ((((3263582 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x + (((842121 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + ((-2100658 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x)) + (((2123881 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x + (((1293251 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x + ((-963816 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x))) := by
  rw [node397_check, Integer.Sparse.eval_merge]
  rw [node394_eval, node396_eval]

theorem node398_check : node398 =
    Integer.Sparse.merge node392 node397 := by decide +kernel

theorem node398_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node398 x = (((((-498704 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x + ((-838818 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x) + (((-3874823 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x + (((897209 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + ((-1143525 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x))) + ((((3263582 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x + (((842121 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + ((-2100658 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x)) + (((2123881 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x + (((1293251 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x + ((-963816 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x)))) := by
  rw [node398_check, Integer.Sparse.eval_merge]
  rw [node392_eval, node397_eval]

theorem node399_check : node399 =
    Integer.Sparse.merge node388 node398 := by decide +kernel

theorem node399_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node399 x = ((((((1101122 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + ((-252593 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x) + (((-678125 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x + (((153302 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + ((-921008 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x))) + ((((-1888253 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x + ((1712829 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x) + (((-403513 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x + (((427205 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x + ((1567125 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x)))) + (((((-498704 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x + ((-838818 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x) + (((-3874823 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x + (((897209 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + ((-1143525 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x))) + ((((3263582 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x + (((842121 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + ((-2100658 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x)) + (((2123881 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x + (((1293251 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x + ((-963816 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x))))) := by
  rw [node399_check, Integer.Sparse.eval_merge]
  rw [node388_eval, node398_eval]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_FiniteSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balanced finite sums for assembling the exact Gram certificate. -/

open scoped BigOperators

namespace MUB6.Certificate.GramAssembly

theorem sum_expand_21 {R : Type*} [AddCommMonoid R] (F : Fin 21 → R) :
    (∑ i, F i) = ((((F 0 + F 1) + (F 2 + (F 3 + F 4))) + ((F 5 + F 6) + (F 7 + (F 8 + F 9)))) + (((F 10 + F 11) + (F 12 + (F 13 + F 14))) + ((F 15 + (F 16 + F 17)) + (F 18 + (F 19 + F 20))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F 0 + (F 1 + (F 2 + (F 3 + (F 4 + (F 5 + (F 6 + (F 7 + (F 8 + (F 9 + (F 10 + (F 11 + (F 12 + (F 13 + (F 14 + (F 15 + (F 16 + (F 17 + (F 18 + (F 19 + (F 20 + 0))))))))))))))))))))) = ((((F 0 + F 1) + (F 2 + (F 3 + F 4))) + ((F 5 + F 6) + (F 7 + (F 8 + F 9)))) + (((F 10 + F 11) + (F 12 + (F 13 + F 14))) + ((F 15 + (F 16 + F 17)) + (F 18 + (F 19 + F 20)))))
  simp only [add_zero, add_assoc]

end MUB6.Certificate.GramAssembly

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

open scoped BigOperators

theorem row_eval_1 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node39 x =
      ∑ j : Fin 21, (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x := by
  rw [node39_eval]
  exact (sum_expand_21 (fun j => (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x)).symm

theorem row_eval_3 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node79 x =
      ∑ j : Fin 21, (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x := by
  rw [node79_eval]
  exact (sum_expand_21 (fun j => (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x)).symm

theorem row_eval_4 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node99 x =
      ∑ j : Fin 21, (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x := by
  rw [node99_eval]
  exact (sum_expand_21 (fun j => (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x)).symm

theorem row_eval_6 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node139 x =
      ∑ j : Fin 21, (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x := by
  rw [node139_eval]
  exact (sum_expand_21 (fun j => (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x)).symm

theorem row_eval_7 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node159 x =
      ∑ j : Fin 21, (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x := by
  rw [node159_eval]
  exact (sum_expand_21 (fun j => (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x)).symm

theorem row_eval_8 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node179 x =
      ∑ j : Fin 21, (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x := by
  rw [node179_eval]
  exact (sum_expand_21 (fun j => (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x)).symm

theorem row_eval_10 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node219 x =
      ∑ j : Fin 21, (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x := by
  rw [node219_eval]
  exact (sum_expand_21 (fun j => (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x)).symm

theorem row_eval_11 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node239 x =
      ∑ j : Fin 21, (weights 11 j : ℝ) * Integer.Sparse.eval (entries 11 j) x := by
  rw [node239_eval]
  exact (sum_expand_21 (fun j => (weights 11 j : ℝ) * Integer.Sparse.eval (entries 11 j) x)).symm

theorem row_eval_12 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node259 x =
      ∑ j : Fin 21, (weights 12 j : ℝ) * Integer.Sparse.eval (entries 12 j) x := by
  rw [node259_eval]
  exact (sum_expand_21 (fun j => (weights 12 j : ℝ) * Integer.Sparse.eval (entries 12 j) x)).symm

theorem row_eval_13 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node279 x =
      ∑ j : Fin 21, (weights 13 j : ℝ) * Integer.Sparse.eval (entries 13 j) x := by
  rw [node279_eval]
  exact (sum_expand_21 (fun j => (weights 13 j : ℝ) * Integer.Sparse.eval (entries 13 j) x)).symm

theorem row_eval_14 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node299 x =
      ∑ j : Fin 21, (weights 14 j : ℝ) * Integer.Sparse.eval (entries 14 j) x := by
  rw [node299_eval]
  exact (sum_expand_21 (fun j => (weights 14 j : ℝ) * Integer.Sparse.eval (entries 14 j) x)).symm

theorem row_eval_16 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node339 x =
      ∑ j : Fin 21, (weights 16 j : ℝ) * Integer.Sparse.eval (entries 16 j) x := by
  rw [node339_eval]
  exact (sum_expand_21 (fun j => (weights 16 j : ℝ) * Integer.Sparse.eval (entries 16 j) x)).symm

theorem row_eval_17 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node359 x =
      ∑ j : Fin 21, (weights 17 j : ℝ) * Integer.Sparse.eval (entries 17 j) x := by
  rw [node359_eval]
  exact (sum_expand_21 (fun j => (weights 17 j : ℝ) * Integer.Sparse.eval (entries 17 j) x)).symm

theorem row_eval_19 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node399 x =
      ∑ j : Fin 21, (weights 19 j : ℝ) * Integer.Sparse.eval (entries 19 j) x := by
  rw [node399_eval]
  exact (sum_expand_21 (fun j => (weights 19 j : ℝ) * Integer.Sparse.eval (entries 19 j) x)).symm

theorem rows_eval_e_oai (i : Fin 21) (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval (rows i) x =
      ∑ j : Fin 21, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  fin_cases i
  · exact row_eval_0_e x
  · exact row_eval_1 x
  · exact row_eval_2_e x
  · exact row_eval_3 x
  · exact row_eval_4 x
  · exact row_eval_5_e x
  · exact row_eval_6 x
  · exact row_eval_7 x
  · exact row_eval_8 x
  · exact row_eval_9_e x
  · exact row_eval_10 x
  · exact row_eval_11 x
  · exact row_eval_12 x
  · exact row_eval_13 x
  · exact row_eval_14 x
  · exact row_eval_15_e x
  · exact row_eval_16 x
  · exact row_eval_17 x
  · exact row_eval_18_e x
  · exact row_eval_19 x
  · exact row_eval_20_e x

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block1.rows_eval_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block1.rows_eval_e_oai
