-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.interpretation_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:19:53.650866+00:00
-- url     : https://prove2.me/submissions/072fe1a9-1f92-49a4-bffe-29d831ec7c0a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E004
import Definitions.Def_OAIQ106E012
import Definitions.Def_OAIQ106E042
import Definitions.Def_OAIQ106E043
import Definitions.Def_OAIQ106E151
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block0_polynomial_interpretation_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block1_polynomial_interpretation_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block2_polynomial_interpretation_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block3_polynomial_interpretation_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block4_polynomial_interpretation_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block5_indexed_entry_eval_e

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

open scoped BigOperators

theorem weights_cast_0 (j : Fin 12) :
    (weights 0 j : ℚ) = GramData.Block5.Z 0 j := by
  revert j
  decide +kernel

theorem weights_cast_1 (j : Fin 12) :
    (weights 1 j : ℚ) = GramData.Block5.Z 1 j := by
  revert j
  decide +kernel

theorem weights_cast_2 (j : Fin 12) :
    (weights 2 j : ℚ) = GramData.Block5.Z 2 j := by
  revert j
  decide +kernel

theorem weights_cast_3 (j : Fin 12) :
    (weights 3 j : ℚ) = GramData.Block5.Z 3 j := by
  revert j
  decide +kernel

theorem weights_cast_4 (j : Fin 12) :
    (weights 4 j : ℚ) = GramData.Block5.Z 4 j := by
  revert j
  decide +kernel

theorem weights_cast_5 (j : Fin 12) :
    (weights 5 j : ℚ) = GramData.Block5.Z 5 j := by
  revert j
  decide +kernel

theorem weights_cast_6 (j : Fin 12) :
    (weights 6 j : ℚ) = GramData.Block5.Z 6 j := by
  revert j
  decide +kernel

theorem weights_cast_7 (j : Fin 12) :
    (weights 7 j : ℚ) = GramData.Block5.Z 7 j := by
  revert j
  decide +kernel

theorem weights_cast_8 (j : Fin 12) :
    (weights 8 j : ℚ) = GramData.Block5.Z 8 j := by
  revert j
  decide +kernel

theorem weights_cast_9 (j : Fin 12) :
    (weights 9 j : ℚ) = GramData.Block5.Z 9 j := by
  revert j
  decide +kernel

theorem weights_cast_10 (j : Fin 12) :
    (weights 10 j : ℚ) = GramData.Block5.Z 10 j := by
  revert j
  decide +kernel

theorem weights_cast_11 (j : Fin 12) :
    (weights 11 j : ℚ) = GramData.Block5.Z 11 j := by
  revert j
  decide +kernel

theorem weights_cast (i j : Fin 12) :
    (weights i j : ℚ) = GramData.Block5.Z i j := by
  fin_cases i
  · exact weights_cast_0 j
  · exact weights_cast_1 j
  · exact weights_cast_2 j
  · exact weights_cast_3 j
  · exact weights_cast_4 j
  · exact weights_cast_5 j
  · exact weights_cast_6 j
  · exact weights_cast_7 j
  · exact weights_cast_8 j
  · exact weights_cast_9 j
  · exact weights_cast_10 j
  · exact weights_cast_11 j

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Part0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem node0_check : node0 =
    Integer.Sparse.merge (Integer.Sparse.scale (-219419) entry_0_1) (Integer.Sparse.scale (1005407) entry_0_2) := by decide +kernel

theorem node0_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node0 x = (((-219419 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x + ((1005407 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x) := by
  rw [node0_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node1_check : node1 =
    Integer.Sparse.merge (Integer.Sparse.scale (3616397) entry_0_0) node0 := by decide +kernel

theorem node1_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node1 x = (((3616397 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + (((-219419 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x + ((1005407 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x)) := by
  rw [node1_check, Integer.Sparse.eval_merge]
  rw [node0_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node2_check : node2 =
    Integer.Sparse.merge (Integer.Sparse.scale (186248) entry_0_4) (Integer.Sparse.scale (5630326) entry_0_5) := by decide +kernel

theorem node2_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node2 x = (((186248 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x + ((5630326 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x) := by
  rw [node2_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node3_check : node3 =
    Integer.Sparse.merge (Integer.Sparse.scale (842091) entry_0_3) node2 := by decide +kernel

theorem node3_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node3 x = (((842091 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + (((186248 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x + ((5630326 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x)) := by
  rw [node3_check, Integer.Sparse.eval_merge]
  rw [node2_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node4_check : node4 =
    Integer.Sparse.merge node1 node3 := by decide +kernel

theorem node4_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node4 x = ((((3616397 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + (((-219419 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x + ((1005407 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x)) + (((842091 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + (((186248 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x + ((5630326 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x))) := by
  rw [node4_check, Integer.Sparse.eval_merge]
  rw [node1_eval, node3_eval]

theorem node5_check : node5 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2799721) entry_0_7) (Integer.Sparse.scale (-212971) entry_0_8) := by decide +kernel

theorem node5_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node5 x = (((-2799721 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x + ((-212971 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x) := by
  rw [node5_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node6_check : node6 =
    Integer.Sparse.merge (Integer.Sparse.scale (3598595) entry_0_6) node5 := by decide +kernel

theorem node6_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node6 x = (((3598595 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x + (((-2799721 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x + ((-212971 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x)) := by
  rw [node6_check, Integer.Sparse.eval_merge]
  rw [node5_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node7_check : node7 =
    Integer.Sparse.merge (Integer.Sparse.scale (919824) entry_0_10) (Integer.Sparse.scale (-418081) entry_0_11) := by decide +kernel

theorem node7_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node7 x = (((919824 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x + ((-418081 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x) := by
  rw [node7_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node8_check : node8 =
    Integer.Sparse.merge (Integer.Sparse.scale (17130) entry_0_9) node7 := by decide +kernel

theorem node8_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node8 x = (((17130 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + (((919824 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x + ((-418081 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x)) := by
  rw [node8_check, Integer.Sparse.eval_merge]
  rw [node7_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node9_check : node9 =
    Integer.Sparse.merge node6 node8 := by decide +kernel

theorem node9_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node9 x = ((((3598595 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x + (((-2799721 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x + ((-212971 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x)) + (((17130 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + (((919824 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x + ((-418081 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x))) := by
  rw [node9_check, Integer.Sparse.eval_merge]
  rw [node6_eval, node8_eval]

theorem node10_check : node10 =
    Integer.Sparse.merge node4 node9 := by decide +kernel

theorem node10_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node10 x = (((((3616397 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + (((-219419 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x + ((1005407 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x)) + (((842091 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + (((186248 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x + ((5630326 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x))) + ((((3598595 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x + (((-2799721 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x + ((-212971 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x)) + (((17130 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + (((919824 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x + ((-418081 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x)))) := by
  rw [node10_check, Integer.Sparse.eval_merge]
  rw [node4_eval, node9_eval]

theorem node11_check : node11 =
    Integer.Sparse.merge (Integer.Sparse.scale (858064) entry_1_1) (Integer.Sparse.scale (-20456) entry_1_2) := by decide +kernel

theorem node11_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node11 x = (((858064 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x + ((-20456 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x) := by
  rw [node11_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node12_check : node12 =
    Integer.Sparse.merge (Integer.Sparse.scale (-219419) entry_1_0) node11 := by decide +kernel

theorem node12_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node12 x = (((-219419 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + (((858064 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x + ((-20456 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x)) := by
  rw [node12_check, Integer.Sparse.eval_merge]
  rw [node11_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node13_check : node13 =
    Integer.Sparse.merge (Integer.Sparse.scale (8632) entry_1_4) (Integer.Sparse.scale (-668374) entry_1_5) := by decide +kernel

theorem node13_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node13 x = (((8632 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x + ((-668374 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x) := by
  rw [node13_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node14_check : node14 =
    Integer.Sparse.merge (Integer.Sparse.scale (-237640) entry_1_3) node13 := by decide +kernel

theorem node14_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node14 x = (((-237640 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + (((8632 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x + ((-668374 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x)) := by
  rw [node14_check, Integer.Sparse.eval_merge]
  rw [node13_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node15_check : node15 =
    Integer.Sparse.merge node12 node14 := by decide +kernel

theorem node15_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node15 x = ((((-219419 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + (((858064 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x + ((-20456 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x)) + (((-237640 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + (((8632 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x + ((-668374 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x))) := by
  rw [node15_check, Integer.Sparse.eval_merge]
  rw [node12_eval, node14_eval]

theorem node16_check : node16 =
    Integer.Sparse.merge (Integer.Sparse.scale (1972640) entry_1_7) (Integer.Sparse.scale (472837) entry_1_8) := by decide +kernel

theorem node16_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node16 x = (((1972640 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + ((472837 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x) := by
  rw [node16_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node17_check : node17 =
    Integer.Sparse.merge (Integer.Sparse.scale (-719533) entry_1_6) node16 := by decide +kernel

theorem node17_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node17 x = (((-719533 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + (((1972640 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + ((472837 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x)) := by
  rw [node17_check, Integer.Sparse.eval_merge]
  rw [node16_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node18_check : node18 =
    Integer.Sparse.merge (Integer.Sparse.scale (-551864) entry_1_10) (Integer.Sparse.scale (-740155) entry_1_11) := by decide +kernel

theorem node18_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node18 x = (((-551864 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x + ((-740155 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x) := by
  rw [node18_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node19_check : node19 =
    Integer.Sparse.merge (Integer.Sparse.scale (-55599) entry_1_9) node18 := by decide +kernel

theorem node19_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node19 x = (((-55599 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + (((-551864 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x + ((-740155 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x)) := by
  rw [node19_check, Integer.Sparse.eval_merge]
  rw [node18_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node20_check : node20 =
    Integer.Sparse.merge node17 node19 := by decide +kernel

theorem node20_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node20 x = ((((-719533 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + (((1972640 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + ((472837 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x)) + (((-55599 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + (((-551864 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x + ((-740155 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x))) := by
  rw [node20_check, Integer.Sparse.eval_merge]
  rw [node17_eval, node19_eval]

theorem node21_check : node21 =
    Integer.Sparse.merge node15 node20 := by decide +kernel

theorem node21_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node21 x = (((((-219419 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + (((858064 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x + ((-20456 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x)) + (((-237640 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + (((8632 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x + ((-668374 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x))) + ((((-719533 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + (((1972640 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + ((472837 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x)) + (((-55599 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + (((-551864 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x + ((-740155 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x)))) := by
  rw [node21_check, Integer.Sparse.eval_merge]
  rw [node15_eval, node20_eval]

theorem node22_check : node22 =
    Integer.Sparse.merge (Integer.Sparse.scale (-20456) entry_2_1) (Integer.Sparse.scale (3980209) entry_2_2) := by decide +kernel

theorem node22_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node22 x = (((-20456 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x + ((3980209 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x) := by
  rw [node22_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node23_check : node23 =
    Integer.Sparse.merge (Integer.Sparse.scale (1005407) entry_2_0) node22 := by decide +kernel

theorem node23_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node23 x = (((1005407 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + (((-20456 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x + ((3980209 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x)) := by
  rw [node23_check, Integer.Sparse.eval_merge]
  rw [node22_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node24_check : node24 =
    Integer.Sparse.merge (Integer.Sparse.scale (1228704) entry_2_4) (Integer.Sparse.scale (3015305) entry_2_5) := by decide +kernel

theorem node24_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node24 x = (((1228704 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x + ((3015305 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x) := by
  rw [node24_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node25_check : node25 =
    Integer.Sparse.merge (Integer.Sparse.scale (-871566) entry_2_3) node24 := by decide +kernel

theorem node25_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node25 x = (((-871566 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + (((1228704 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x + ((3015305 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x)) := by
  rw [node25_check, Integer.Sparse.eval_merge]
  rw [node24_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node26_check : node26 =
    Integer.Sparse.merge node23 node25 := by decide +kernel

theorem node26_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node26 x = ((((1005407 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + (((-20456 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x + ((3980209 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x)) + (((-871566 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + (((1228704 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x + ((3015305 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x))) := by
  rw [node26_check, Integer.Sparse.eval_merge]
  rw [node23_eval, node25_eval]

theorem node27_check : node27 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4624965) entry_2_7) (Integer.Sparse.scale (-846239) entry_2_8) := by decide +kernel

theorem node27_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node27 x = (((-4624965 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + ((-846239 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x) := by
  rw [node27_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node28_check : node28 =
    Integer.Sparse.merge (Integer.Sparse.scale (-741592) entry_2_6) node27 := by decide +kernel

theorem node28_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node28 x = (((-741592 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + (((-4624965 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + ((-846239 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x)) := by
  rw [node28_check, Integer.Sparse.eval_merge]
  rw [node27_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node29_check : node29 =
    Integer.Sparse.merge (Integer.Sparse.scale (946245) entry_2_10) (Integer.Sparse.scale (-2217477) entry_2_11) := by decide +kernel

theorem node29_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node29 x = (((946245 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x + ((-2217477 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x) := by
  rw [node29_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node30_check : node30 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3742225) entry_2_9) node29 := by decide +kernel

theorem node30_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node30 x = (((-3742225 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + (((946245 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x + ((-2217477 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x)) := by
  rw [node30_check, Integer.Sparse.eval_merge]
  rw [node29_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node31_check : node31 =
    Integer.Sparse.merge node28 node30 := by decide +kernel

theorem node31_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node31 x = ((((-741592 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + (((-4624965 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + ((-846239 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x)) + (((-3742225 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + (((946245 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x + ((-2217477 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x))) := by
  rw [node31_check, Integer.Sparse.eval_merge]
  rw [node28_eval, node30_eval]

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Part1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem node32_check : node32 =
    Integer.Sparse.merge node26 node31 := by decide +kernel

theorem node32_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node32 x = (((((1005407 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + (((-20456 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x + ((3980209 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x)) + (((-871566 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + (((1228704 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x + ((3015305 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x))) + ((((-741592 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + (((-4624965 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + ((-846239 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x)) + (((-3742225 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + (((946245 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x + ((-2217477 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x)))) := by
  rw [node32_check, Integer.Sparse.eval_merge]
  rw [node26_eval, node31_eval]

theorem node33_check : node33 =
    Integer.Sparse.merge (Integer.Sparse.scale (-237640) entry_3_1) (Integer.Sparse.scale (-871566) entry_3_2) := by decide +kernel

theorem node33_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node33 x = (((-237640 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x + ((-871566 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x) := by
  rw [node33_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node34_check : node34 =
    Integer.Sparse.merge (Integer.Sparse.scale (842091) entry_3_0) node33 := by decide +kernel

theorem node34_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node34 x = (((842091 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + (((-237640 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x + ((-871566 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x)) := by
  rw [node34_check, Integer.Sparse.eval_merge]
  rw [node33_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node35_check : node35 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1032886) entry_3_4) (Integer.Sparse.scale (1787740) entry_3_5) := by decide +kernel

theorem node35_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node35 x = (((-1032886 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x + ((1787740 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x) := by
  rw [node35_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node36_check : node36 =
    Integer.Sparse.merge (Integer.Sparse.scale (1225103) entry_3_3) node35 := by decide +kernel

theorem node36_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node36 x = (((1225103 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + (((-1032886 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x + ((1787740 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x)) := by
  rw [node36_check, Integer.Sparse.eval_merge]
  rw [node35_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node37_check : node37 =
    Integer.Sparse.merge node34 node36 := by decide +kernel

theorem node37_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node37 x = ((((842091 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + (((-237640 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x + ((-871566 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x)) + (((1225103 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + (((-1032886 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x + ((1787740 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x))) := by
  rw [node37_check, Integer.Sparse.eval_merge]
  rw [node34_eval, node36_eval]

theorem node38_check : node38 =
    Integer.Sparse.merge (Integer.Sparse.scale (1845322) entry_3_7) (Integer.Sparse.scale (193740) entry_3_8) := by decide +kernel

theorem node38_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node38 x = (((1845322 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + ((193740 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x) := by
  rw [node38_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node39_check : node39 =
    Integer.Sparse.merge (Integer.Sparse.scale (2550956) entry_3_6) node38 := by decide +kernel

theorem node39_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node39 x = (((2550956 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + (((1845322 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + ((193740 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x)) := by
  rw [node39_check, Integer.Sparse.eval_merge]
  rw [node38_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node40_check : node40 =
    Integer.Sparse.merge (Integer.Sparse.scale (-537616) entry_3_10) (Integer.Sparse.scale (2123549) entry_3_11) := by decide +kernel

theorem node40_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node40 x = (((-537616 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x + ((2123549 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x) := by
  rw [node40_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node41_check : node41 =
    Integer.Sparse.merge (Integer.Sparse.scale (3000641) entry_3_9) node40 := by decide +kernel

theorem node41_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node41 x = (((3000641 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + (((-537616 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x + ((2123549 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x)) := by
  rw [node41_check, Integer.Sparse.eval_merge]
  rw [node40_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node42_check : node42 =
    Integer.Sparse.merge node39 node41 := by decide +kernel

theorem node42_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node42 x = ((((2550956 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + (((1845322 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + ((193740 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x)) + (((3000641 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + (((-537616 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x + ((2123549 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x))) := by
  rw [node42_check, Integer.Sparse.eval_merge]
  rw [node39_eval, node41_eval]

theorem node43_check : node43 =
    Integer.Sparse.merge node37 node42 := by decide +kernel

theorem node43_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node43 x = (((((842091 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + (((-237640 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x + ((-871566 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x)) + (((1225103 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + (((-1032886 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x + ((1787740 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x))) + ((((2550956 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + (((1845322 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + ((193740 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x)) + (((3000641 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + (((-537616 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x + ((2123549 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x)))) := by
  rw [node43_check, Integer.Sparse.eval_merge]
  rw [node37_eval, node42_eval]

theorem node44_check : node44 =
    Integer.Sparse.merge (Integer.Sparse.scale (8632) entry_4_1) (Integer.Sparse.scale (1228704) entry_4_2) := by decide +kernel

theorem node44_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node44 x = (((8632 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x + ((1228704 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x) := by
  rw [node44_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node45_check : node45 =
    Integer.Sparse.merge (Integer.Sparse.scale (186248) entry_4_0) node44 := by decide +kernel

theorem node45_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node45 x = (((186248 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + (((8632 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x + ((1228704 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x)) := by
  rw [node45_check, Integer.Sparse.eval_merge]
  rw [node44_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node46_check : node46 =
    Integer.Sparse.merge (Integer.Sparse.scale (2523431) entry_4_4) (Integer.Sparse.scale (415506) entry_4_5) := by decide +kernel

theorem node46_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node46 x = (((2523431 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x + ((415506 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x) := by
  rw [node46_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node47_check : node47 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1032886) entry_4_3) node46 := by decide +kernel

theorem node47_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node47 x = (((-1032886 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + (((2523431 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x + ((415506 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x)) := by
  rw [node47_check, Integer.Sparse.eval_merge]
  rw [node46_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node48_check : node48 =
    Integer.Sparse.merge node45 node47 := by decide +kernel

theorem node48_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node48 x = ((((186248 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + (((8632 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x + ((1228704 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x)) + (((-1032886 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + (((2523431 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x + ((415506 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x))) := by
  rw [node48_check, Integer.Sparse.eval_merge]
  rw [node45_eval, node47_eval]

theorem node49_check : node49 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4715938) entry_4_7) (Integer.Sparse.scale (-791330) entry_4_8) := by decide +kernel

theorem node49_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node49 x = (((-4715938 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x + ((-791330 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x) := by
  rw [node49_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node50_check : node50 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2373762) entry_4_6) node49 := by decide +kernel

theorem node50_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node50 x = (((-2373762 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + (((-4715938 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x + ((-791330 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x)) := by
  rw [node50_check, Integer.Sparse.eval_merge]
  rw [node49_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node51_check : node51 =
    Integer.Sparse.merge (Integer.Sparse.scale (1140990) entry_4_10) (Integer.Sparse.scale (-3681887) entry_4_11) := by decide +kernel

theorem node51_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node51 x = (((1140990 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x + ((-3681887 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x) := by
  rw [node51_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node52_check : node52 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4758384) entry_4_9) node51 := by decide +kernel

theorem node52_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node52 x = (((-4758384 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + (((1140990 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x + ((-3681887 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x)) := by
  rw [node52_check, Integer.Sparse.eval_merge]
  rw [node51_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node53_check : node53 =
    Integer.Sparse.merge node50 node52 := by decide +kernel

theorem node53_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node53 x = ((((-2373762 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + (((-4715938 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x + ((-791330 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x)) + (((-4758384 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + (((1140990 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x + ((-3681887 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x))) := by
  rw [node53_check, Integer.Sparse.eval_merge]
  rw [node50_eval, node52_eval]

theorem node54_check : node54 =
    Integer.Sparse.merge node48 node53 := by decide +kernel

theorem node54_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node54 x = (((((186248 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + (((8632 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x + ((1228704 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x)) + (((-1032886 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + (((2523431 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x + ((415506 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x))) + ((((-2373762 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + (((-4715938 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x + ((-791330 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x)) + (((-4758384 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + (((1140990 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x + ((-3681887 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x)))) := by
  rw [node54_check, Integer.Sparse.eval_merge]
  rw [node48_eval, node53_eval]

theorem node55_check : node55 =
    Integer.Sparse.merge (Integer.Sparse.scale (-668374) entry_5_1) (Integer.Sparse.scale (3015305) entry_5_2) := by decide +kernel

theorem node55_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node55 x = (((-668374 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x + ((3015305 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x) := by
  rw [node55_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node56_check : node56 =
    Integer.Sparse.merge (Integer.Sparse.scale (5630326) entry_5_0) node55 := by decide +kernel

theorem node56_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node56 x = (((5630326 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + (((-668374 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x + ((3015305 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x)) := by
  rw [node56_check, Integer.Sparse.eval_merge]
  rw [node55_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node57_check : node57 =
    Integer.Sparse.merge (Integer.Sparse.scale (415506) entry_5_4) (Integer.Sparse.scale (14075688) entry_5_5) := by decide +kernel

theorem node57_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node57 x = (((415506 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x + ((14075688 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x) := by
  rw [node57_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node58_check : node58 =
    Integer.Sparse.merge (Integer.Sparse.scale (1787740) entry_5_3) node57 := by decide +kernel

theorem node58_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node58 x = (((1787740 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + (((415506 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x + ((14075688 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x)) := by
  rw [node58_check, Integer.Sparse.eval_merge]
  rw [node57_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node59_check : node59 =
    Integer.Sparse.merge node56 node58 := by decide +kernel

theorem node59_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node59 x = ((((5630326 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + (((-668374 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x + ((3015305 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x)) + (((1787740 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + (((415506 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x + ((14075688 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x))) := by
  rw [node59_check, Integer.Sparse.eval_merge]
  rw [node56_eval, node58_eval]

theorem node60_check : node60 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6536077) entry_5_7) (Integer.Sparse.scale (-885101) entry_5_8) := by decide +kernel

theorem node60_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node60 x = (((-6536077 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x + ((-885101 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x) := by
  rw [node60_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node61_check : node61 =
    Integer.Sparse.merge (Integer.Sparse.scale (6490324) entry_5_6) node60 := by decide +kernel

theorem node61_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node61 x = (((6490324 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + (((-6536077 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x + ((-885101 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x)) := by
  rw [node61_check, Integer.Sparse.eval_merge]
  rw [node60_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node62_check : node62 =
    Integer.Sparse.merge (Integer.Sparse.scale (1366079) entry_5_10) (Integer.Sparse.scale (-804) entry_5_11) := by decide +kernel

theorem node62_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node62 x = (((1366079 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x + ((-804 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x) := by
  rw [node62_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node63_check : node63 =
    Integer.Sparse.merge (Integer.Sparse.scale (729531) entry_5_9) node62 := by decide +kernel

theorem node63_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node63 x = (((729531 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + (((1366079 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x + ((-804 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x)) := by
  rw [node63_check, Integer.Sparse.eval_merge]
  rw [node62_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Part2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem node64_check : node64 =
    Integer.Sparse.merge node61 node63 := by decide +kernel

theorem node64_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node64 x = ((((6490324 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + (((-6536077 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x + ((-885101 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x)) + (((729531 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + (((1366079 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x + ((-804 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x))) := by
  rw [node64_check, Integer.Sparse.eval_merge]
  rw [node61_eval, node63_eval]

theorem node65_check : node65 =
    Integer.Sparse.merge node59 node64 := by decide +kernel

theorem node65_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node65 x = (((((5630326 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + (((-668374 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x + ((3015305 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x)) + (((1787740 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + (((415506 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x + ((14075688 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x))) + ((((6490324 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + (((-6536077 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x + ((-885101 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x)) + (((729531 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + (((1366079 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x + ((-804 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x)))) := by
  rw [node65_check, Integer.Sparse.eval_merge]
  rw [node59_eval, node64_eval]

theorem node66_check : node66 =
    Integer.Sparse.merge (Integer.Sparse.scale (-719533) entry_6_1) (Integer.Sparse.scale (-741592) entry_6_2) := by decide +kernel

theorem node66_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node66 x = (((-719533 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x + ((-741592 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x) := by
  rw [node66_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node67_check : node67 =
    Integer.Sparse.merge (Integer.Sparse.scale (3598595) entry_6_0) node66 := by decide +kernel

theorem node67_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node67 x = (((3598595 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + (((-719533 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x + ((-741592 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x)) := by
  rw [node67_check, Integer.Sparse.eval_merge]
  rw [node66_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node68_check : node68 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2373762) entry_6_4) (Integer.Sparse.scale (6490324) entry_6_5) := by decide +kernel

theorem node68_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node68 x = (((-2373762 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x + ((6490324 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x) := by
  rw [node68_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node69_check : node69 =
    Integer.Sparse.merge (Integer.Sparse.scale (2550956) entry_6_3) node68 := by decide +kernel

theorem node69_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node69 x = (((2550956 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + (((-2373762 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x + ((6490324 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x)) := by
  rw [node69_check, Integer.Sparse.eval_merge]
  rw [node68_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node70_check : node70 =
    Integer.Sparse.merge node67 node69 := by decide +kernel

theorem node70_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node70 x = ((((3598595 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + (((-719533 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x + ((-741592 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x)) + (((2550956 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + (((-2373762 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x + ((6490324 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x))) := by
  rw [node70_check, Integer.Sparse.eval_merge]
  rw [node67_eval, node69_eval]

theorem node71_check : node71 =
    Integer.Sparse.merge (Integer.Sparse.scale (2309105) entry_6_7) (Integer.Sparse.scale (-369038) entry_6_8) := by decide +kernel

theorem node71_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node71 x = (((2309105 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((-369038 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x) := by
  rw [node71_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node72_check : node72 =
    Integer.Sparse.merge (Integer.Sparse.scale (11111814) entry_6_6) node71 := by decide +kernel

theorem node72_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node72 x = (((11111814 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + (((2309105 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((-369038 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x)) := by
  rw [node72_check, Integer.Sparse.eval_merge]
  rw [node71_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node73_check : node73 =
    Integer.Sparse.merge (Integer.Sparse.scale (-149445) entry_6_10) (Integer.Sparse.scale (5321306) entry_6_11) := by decide +kernel

theorem node73_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node73 x = (((-149445 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x + ((5321306 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x) := by
  rw [node73_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node74_check : node74 =
    Integer.Sparse.merge (Integer.Sparse.scale (7029198) entry_6_9) node73 := by decide +kernel

theorem node74_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node74 x = (((7029198 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + (((-149445 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x + ((5321306 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x)) := by
  rw [node74_check, Integer.Sparse.eval_merge]
  rw [node73_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node75_check : node75 =
    Integer.Sparse.merge node72 node74 := by decide +kernel

theorem node75_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node75 x = ((((11111814 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + (((2309105 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((-369038 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x)) + (((7029198 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + (((-149445 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x + ((5321306 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x))) := by
  rw [node75_check, Integer.Sparse.eval_merge]
  rw [node72_eval, node74_eval]

theorem node76_check : node76 =
    Integer.Sparse.merge node70 node75 := by decide +kernel

theorem node76_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node76 x = (((((3598595 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + (((-719533 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x + ((-741592 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x)) + (((2550956 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + (((-2373762 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x + ((6490324 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x))) + ((((11111814 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + (((2309105 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((-369038 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x)) + (((7029198 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + (((-149445 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x + ((5321306 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x)))) := by
  rw [node76_check, Integer.Sparse.eval_merge]
  rw [node70_eval, node75_eval]

theorem node77_check : node77 =
    Integer.Sparse.merge (Integer.Sparse.scale (1972640) entry_7_1) (Integer.Sparse.scale (-4624965) entry_7_2) := by decide +kernel

theorem node77_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node77 x = (((1972640 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x + ((-4624965 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x) := by
  rw [node77_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node78_check : node78 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2799721) entry_7_0) node77 := by decide +kernel

theorem node78_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node78 x = (((-2799721 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + (((1972640 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x + ((-4624965 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x)) := by
  rw [node78_check, Integer.Sparse.eval_merge]
  rw [node77_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node79_check : node79 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4715938) entry_7_4) (Integer.Sparse.scale (-6536077) entry_7_5) := by decide +kernel

theorem node79_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node79 x = (((-4715938 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x + ((-6536077 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x) := by
  rw [node79_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node80_check : node80 =
    Integer.Sparse.merge (Integer.Sparse.scale (1845322) entry_7_3) node79 := by decide +kernel

theorem node80_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node80 x = (((1845322 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + (((-4715938 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x + ((-6536077 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x)) := by
  rw [node80_check, Integer.Sparse.eval_merge]
  rw [node79_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node81_check : node81 =
    Integer.Sparse.merge node78 node80 := by decide +kernel

theorem node81_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node81 x = ((((-2799721 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + (((1972640 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x + ((-4624965 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x)) + (((1845322 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + (((-4715938 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x + ((-6536077 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x))) := by
  rw [node81_check, Integer.Sparse.eval_merge]
  rw [node78_eval, node80_eval]

theorem node82_check : node82 =
    Integer.Sparse.merge (Integer.Sparse.scale (20933543) entry_7_7) (Integer.Sparse.scale (2515724) entry_7_8) := by decide +kernel

theorem node82_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node82 x = (((20933543 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + ((2515724 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x) := by
  rw [node82_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node83_check : node83 =
    Integer.Sparse.merge (Integer.Sparse.scale (2309105) entry_7_6) node82 := by decide +kernel

theorem node83_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node83 x = (((2309105 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + (((20933543 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + ((2515724 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x)) := by
  rw [node83_check, Integer.Sparse.eval_merge]
  rw [node82_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node84_check : node84 =
    Integer.Sparse.merge (Integer.Sparse.scale (-5705771) entry_7_10) (Integer.Sparse.scale (8194820) entry_7_11) := by decide +kernel

theorem node84_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node84 x = (((-5705771 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x + ((8194820 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x) := by
  rw [node84_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node85_check : node85 =
    Integer.Sparse.merge (Integer.Sparse.scale (11792046) entry_7_9) node84 := by decide +kernel

theorem node85_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node85 x = (((11792046 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + (((-5705771 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x + ((8194820 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x)) := by
  rw [node85_check, Integer.Sparse.eval_merge]
  rw [node84_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node86_check : node86 =
    Integer.Sparse.merge node83 node85 := by decide +kernel

theorem node86_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node86 x = ((((2309105 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + (((20933543 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + ((2515724 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x)) + (((11792046 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + (((-5705771 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x + ((8194820 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x))) := by
  rw [node86_check, Integer.Sparse.eval_merge]
  rw [node83_eval, node85_eval]

theorem node87_check : node87 =
    Integer.Sparse.merge node81 node86 := by decide +kernel

theorem node87_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node87 x = (((((-2799721 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + (((1972640 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x + ((-4624965 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x)) + (((1845322 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + (((-4715938 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x + ((-6536077 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x))) + ((((2309105 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + (((20933543 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + ((2515724 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x)) + (((11792046 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + (((-5705771 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x + ((8194820 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x)))) := by
  rw [node87_check, Integer.Sparse.eval_merge]
  rw [node81_eval, node86_eval]

theorem node88_check : node88 =
    Integer.Sparse.merge (Integer.Sparse.scale (472837) entry_8_1) (Integer.Sparse.scale (-846239) entry_8_2) := by decide +kernel

theorem node88_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node88 x = (((472837 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x + ((-846239 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x) := by
  rw [node88_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node89_check : node89 =
    Integer.Sparse.merge (Integer.Sparse.scale (-212971) entry_8_0) node88 := by decide +kernel

theorem node89_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node89 x = (((-212971 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + (((472837 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x + ((-846239 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x)) := by
  rw [node89_check, Integer.Sparse.eval_merge]
  rw [node88_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node90_check : node90 =
    Integer.Sparse.merge (Integer.Sparse.scale (-791330) entry_8_4) (Integer.Sparse.scale (-885101) entry_8_5) := by decide +kernel

theorem node90_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node90 x = (((-791330 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x + ((-885101 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x) := by
  rw [node90_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node91_check : node91 =
    Integer.Sparse.merge (Integer.Sparse.scale (193740) entry_8_3) node90 := by decide +kernel

theorem node91_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node91 x = (((193740 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + (((-791330 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x + ((-885101 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x)) := by
  rw [node91_check, Integer.Sparse.eval_merge]
  rw [node90_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node92_check : node92 =
    Integer.Sparse.merge node89 node91 := by decide +kernel

theorem node92_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node92 x = ((((-212971 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + (((472837 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x + ((-846239 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x)) + (((193740 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + (((-791330 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x + ((-885101 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x))) := by
  rw [node92_check, Integer.Sparse.eval_merge]
  rw [node89_eval, node91_eval]

theorem node93_check : node93 =
    Integer.Sparse.merge (Integer.Sparse.scale (2515724) entry_8_7) (Integer.Sparse.scale (1454109) entry_8_8) := by decide +kernel

theorem node93_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node93 x = (((2515724 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + ((1454109 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x) := by
  rw [node93_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node94_check : node94 =
    Integer.Sparse.merge (Integer.Sparse.scale (-369038) entry_8_6) node93 := by decide +kernel

theorem node94_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node94 x = (((-369038 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + (((2515724 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + ((1454109 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x)) := by
  rw [node94_check, Integer.Sparse.eval_merge]
  rw [node93_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node95_check : node95 =
    Integer.Sparse.merge (Integer.Sparse.scale (-502420) entry_8_10) (Integer.Sparse.scale (-325129) entry_8_11) := by decide +kernel

theorem node95_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node95 x = (((-502420 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x + ((-325129 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x) := by
  rw [node95_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Part3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem node96_check : node96 =
    Integer.Sparse.merge (Integer.Sparse.scale (1090081) entry_8_9) node95 := by decide +kernel

theorem node96_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node96 x = (((1090081 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + (((-502420 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x + ((-325129 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x)) := by
  rw [node96_check, Integer.Sparse.eval_merge]
  rw [node95_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node97_check : node97 =
    Integer.Sparse.merge node94 node96 := by decide +kernel

theorem node97_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node97 x = ((((-369038 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + (((2515724 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + ((1454109 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x)) + (((1090081 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + (((-502420 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x + ((-325129 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x))) := by
  rw [node97_check, Integer.Sparse.eval_merge]
  rw [node94_eval, node96_eval]

theorem node98_check : node98 =
    Integer.Sparse.merge node92 node97 := by decide +kernel

theorem node98_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node98 x = (((((-212971 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + (((472837 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x + ((-846239 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x)) + (((193740 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + (((-791330 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x + ((-885101 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x))) + ((((-369038 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + (((2515724 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + ((1454109 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x)) + (((1090081 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + (((-502420 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x + ((-325129 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x)))) := by
  rw [node98_check, Integer.Sparse.eval_merge]
  rw [node92_eval, node97_eval]

theorem node99_check : node99 =
    Integer.Sparse.merge (Integer.Sparse.scale (-55599) entry_9_1) (Integer.Sparse.scale (-3742225) entry_9_2) := by decide +kernel

theorem node99_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node99 x = (((-55599 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x + ((-3742225 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x) := by
  rw [node99_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node100_check : node100 =
    Integer.Sparse.merge (Integer.Sparse.scale (17130) entry_9_0) node99 := by decide +kernel

theorem node100_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node100 x = (((17130 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + (((-55599 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x + ((-3742225 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x)) := by
  rw [node100_check, Integer.Sparse.eval_merge]
  rw [node99_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node101_check : node101 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4758384) entry_9_4) (Integer.Sparse.scale (729531) entry_9_5) := by decide +kernel

theorem node101_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node101 x = (((-4758384 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x + ((729531 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x) := by
  rw [node101_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node102_check : node102 =
    Integer.Sparse.merge (Integer.Sparse.scale (3000641) entry_9_3) node101 := by decide +kernel

theorem node102_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node102 x = (((3000641 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + (((-4758384 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x + ((729531 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x)) := by
  rw [node102_check, Integer.Sparse.eval_merge]
  rw [node101_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node103_check : node103 =
    Integer.Sparse.merge node100 node102 := by decide +kernel

theorem node103_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node103 x = ((((17130 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + (((-55599 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x + ((-3742225 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x)) + (((3000641 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + (((-4758384 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x + ((729531 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x))) := by
  rw [node103_check, Integer.Sparse.eval_merge]
  rw [node100_eval, node102_eval]

theorem node104_check : node104 =
    Integer.Sparse.merge (Integer.Sparse.scale (11792046) entry_9_7) (Integer.Sparse.scale (1090081) entry_9_8) := by decide +kernel

theorem node104_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node104 x = (((11792046 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + ((1090081 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x) := by
  rw [node104_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node105_check : node105 =
    Integer.Sparse.merge (Integer.Sparse.scale (7029198) entry_9_6) node104 := by decide +kernel

theorem node105_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node105 x = (((7029198 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + (((11792046 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + ((1090081 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x)) := by
  rw [node105_check, Integer.Sparse.eval_merge]
  rw [node104_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node106_check : node106 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4206760) entry_9_10) (Integer.Sparse.scale (10354295) entry_9_11) := by decide +kernel

theorem node106_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node106 x = (((-4206760 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x + ((10354295 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x) := by
  rw [node106_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node107_check : node107 =
    Integer.Sparse.merge (Integer.Sparse.scale (14915142) entry_9_9) node106 := by decide +kernel

theorem node107_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node107 x = (((14915142 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + (((-4206760 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x + ((10354295 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x)) := by
  rw [node107_check, Integer.Sparse.eval_merge]
  rw [node106_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node108_check : node108 =
    Integer.Sparse.merge node105 node107 := by decide +kernel

theorem node108_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node108 x = ((((7029198 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + (((11792046 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + ((1090081 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x)) + (((14915142 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + (((-4206760 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x + ((10354295 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x))) := by
  rw [node108_check, Integer.Sparse.eval_merge]
  rw [node105_eval, node107_eval]

theorem node109_check : node109 =
    Integer.Sparse.merge node103 node108 := by decide +kernel

theorem node109_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node109 x = (((((17130 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + (((-55599 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x + ((-3742225 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x)) + (((3000641 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + (((-4758384 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x + ((729531 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x))) + ((((7029198 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + (((11792046 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + ((1090081 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x)) + (((14915142 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + (((-4206760 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x + ((10354295 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x)))) := by
  rw [node109_check, Integer.Sparse.eval_merge]
  rw [node103_eval, node108_eval]

theorem node110_check : node110 =
    Integer.Sparse.merge (Integer.Sparse.scale (-551864) entry_10_1) (Integer.Sparse.scale (946245) entry_10_2) := by decide +kernel

theorem node110_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node110 x = (((-551864 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x + ((946245 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x) := by
  rw [node110_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node111_check : node111 =
    Integer.Sparse.merge (Integer.Sparse.scale (919824) entry_10_0) node110 := by decide +kernel

theorem node111_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node111 x = (((919824 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + (((-551864 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x + ((946245 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x)) := by
  rw [node111_check, Integer.Sparse.eval_merge]
  rw [node110_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node112_check : node112 =
    Integer.Sparse.merge (Integer.Sparse.scale (1140990) entry_10_4) (Integer.Sparse.scale (1366079) entry_10_5) := by decide +kernel

theorem node112_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node112 x = (((1140990 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x + ((1366079 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x) := by
  rw [node112_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node113_check : node113 =
    Integer.Sparse.merge (Integer.Sparse.scale (-537616) entry_10_3) node112 := by decide +kernel

theorem node113_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node113 x = (((-537616 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + (((1140990 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x + ((1366079 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x)) := by
  rw [node113_check, Integer.Sparse.eval_merge]
  rw [node112_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node114_check : node114 =
    Integer.Sparse.merge node111 node113 := by decide +kernel

theorem node114_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node114 x = ((((919824 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + (((-551864 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x + ((946245 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x)) + (((-537616 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + (((1140990 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x + ((1366079 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x))) := by
  rw [node114_check, Integer.Sparse.eval_merge]
  rw [node111_eval, node113_eval]

theorem node115_check : node115 =
    Integer.Sparse.merge (Integer.Sparse.scale (-5705771) entry_10_7) (Integer.Sparse.scale (-502420) entry_10_8) := by decide +kernel

theorem node115_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node115 x = (((-5705771 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + ((-502420 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x) := by
  rw [node115_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node116_check : node116 =
    Integer.Sparse.merge (Integer.Sparse.scale (-149445) entry_10_6) node115 := by decide +kernel

theorem node116_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node116 x = (((-149445 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + (((-5705771 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + ((-502420 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x)) := by
  rw [node116_check, Integer.Sparse.eval_merge]
  rw [node115_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node117_check : node117 =
    Integer.Sparse.merge (Integer.Sparse.scale (3573400) entry_10_10) (Integer.Sparse.scale (-4063238) entry_10_11) := by decide +kernel

theorem node117_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node117 x = (((3573400 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x + ((-4063238 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x) := by
  rw [node117_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node118_check : node118 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4206760) entry_10_9) node117 := by decide +kernel

theorem node118_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node118 x = (((-4206760 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + (((3573400 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x + ((-4063238 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x)) := by
  rw [node118_check, Integer.Sparse.eval_merge]
  rw [node117_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node119_check : node119 =
    Integer.Sparse.merge node116 node118 := by decide +kernel

theorem node119_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node119 x = ((((-149445 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + (((-5705771 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + ((-502420 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x)) + (((-4206760 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + (((3573400 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x + ((-4063238 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x))) := by
  rw [node119_check, Integer.Sparse.eval_merge]
  rw [node116_eval, node118_eval]

theorem node120_check : node120 =
    Integer.Sparse.merge node114 node119 := by decide +kernel

theorem node120_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node120 x = (((((919824 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + (((-551864 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x + ((946245 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x)) + (((-537616 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + (((1140990 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x + ((1366079 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x))) + ((((-149445 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + (((-5705771 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + ((-502420 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x)) + (((-4206760 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + (((3573400 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x + ((-4063238 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x)))) := by
  rw [node120_check, Integer.Sparse.eval_merge]
  rw [node114_eval, node119_eval]

theorem node121_check : node121 =
    Integer.Sparse.merge (Integer.Sparse.scale (-740155) entry_11_1) (Integer.Sparse.scale (-2217477) entry_11_2) := by decide +kernel

theorem node121_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node121 x = (((-740155 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x + ((-2217477 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x) := by
  rw [node121_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node122_check : node122 =
    Integer.Sparse.merge (Integer.Sparse.scale (-418081) entry_11_0) node121 := by decide +kernel

theorem node122_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node122 x = (((-418081 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + (((-740155 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x + ((-2217477 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x)) := by
  rw [node122_check, Integer.Sparse.eval_merge]
  rw [node121_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node123_check : node123 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3681887) entry_11_4) (Integer.Sparse.scale (-804) entry_11_5) := by decide +kernel

theorem node123_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node123 x = (((-3681887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-804 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x) := by
  rw [node123_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node124_check : node124 =
    Integer.Sparse.merge (Integer.Sparse.scale (2123549) entry_11_3) node123 := by decide +kernel

theorem node124_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node124 x = (((2123549 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + (((-3681887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-804 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x)) := by
  rw [node124_check, Integer.Sparse.eval_merge]
  rw [node123_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node125_check : node125 =
    Integer.Sparse.merge node122 node124 := by decide +kernel

theorem node125_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node125 x = ((((-418081 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + (((-740155 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x + ((-2217477 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x)) + (((2123549 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + (((-3681887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-804 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x))) := by
  rw [node125_check, Integer.Sparse.eval_merge]
  rw [node122_eval, node124_eval]

theorem node126_check : node126 =
    Integer.Sparse.merge (Integer.Sparse.scale (8194820) entry_11_7) (Integer.Sparse.scale (-325129) entry_11_8) := by decide +kernel

theorem node126_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node126 x = (((8194820 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + ((-325129 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x) := by
  rw [node126_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node127_check : node127 =
    Integer.Sparse.merge (Integer.Sparse.scale (5321306) entry_11_6) node126 := by decide +kernel

theorem node127_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node127 x = (((5321306 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + (((8194820 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + ((-325129 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x)) := by
  rw [node127_check, Integer.Sparse.eval_merge]
  rw [node126_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Part4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

theorem node128_check : node128 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4063238) entry_11_10) (Integer.Sparse.scale (10569070) entry_11_11) := by decide +kernel

theorem node128_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node128 x = (((-4063238 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x + ((10569070 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x) := by
  rw [node128_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node129_check : node129 =
    Integer.Sparse.merge (Integer.Sparse.scale (10354295) entry_11_9) node128 := by decide +kernel

theorem node129_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node129 x = (((10354295 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + (((-4063238 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x + ((10569070 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x)) := by
  rw [node129_check, Integer.Sparse.eval_merge]
  rw [node128_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node130_check : node130 =
    Integer.Sparse.merge node127 node129 := by decide +kernel

theorem node130_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node130 x = ((((5321306 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + (((8194820 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + ((-325129 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x)) + (((10354295 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + (((-4063238 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x + ((10569070 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x))) := by
  rw [node130_check, Integer.Sparse.eval_merge]
  rw [node127_eval, node129_eval]

theorem node131_check : node131 =
    Integer.Sparse.merge node125 node130 := by decide +kernel

theorem node131_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node131 x = (((((-418081 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + (((-740155 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x + ((-2217477 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x)) + (((2123549 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + (((-3681887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-804 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x))) + ((((5321306 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + (((8194820 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + ((-325129 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x)) + (((10354295 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + (((-4063238 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x + ((10569070 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x)))) := by
  rw [node131_check, Integer.Sparse.eval_merge]
  rw [node125_eval, node130_eval]

theorem node132_check : node132 =
    Integer.Sparse.merge node21 node32 := by decide +kernel

theorem node132_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node132 x = (Integer.Sparse.eval node21 x + Integer.Sparse.eval node32 x) := by
  rw [node132_check, Integer.Sparse.eval_merge]

theorem node133_check : node133 =
    Integer.Sparse.merge node10 node132 := by decide +kernel

theorem node133_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node133 x = (Integer.Sparse.eval node10 x + (Integer.Sparse.eval node21 x + Integer.Sparse.eval node32 x)) := by
  rw [node133_check, Integer.Sparse.eval_merge]
  rw [node132_eval]

theorem node134_check : node134 =
    Integer.Sparse.merge node54 node65 := by decide +kernel

theorem node134_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node134 x = (Integer.Sparse.eval node54 x + Integer.Sparse.eval node65 x) := by
  rw [node134_check, Integer.Sparse.eval_merge]

theorem node135_check : node135 =
    Integer.Sparse.merge node43 node134 := by decide +kernel

theorem node135_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node135 x = (Integer.Sparse.eval node43 x + (Integer.Sparse.eval node54 x + Integer.Sparse.eval node65 x)) := by
  rw [node135_check, Integer.Sparse.eval_merge]
  rw [node134_eval]

theorem node136_check : node136 =
    Integer.Sparse.merge node133 node135 := by decide +kernel

theorem node136_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node136 x = ((Integer.Sparse.eval node10 x + (Integer.Sparse.eval node21 x + Integer.Sparse.eval node32 x)) + (Integer.Sparse.eval node43 x + (Integer.Sparse.eval node54 x + Integer.Sparse.eval node65 x))) := by
  rw [node136_check, Integer.Sparse.eval_merge]
  rw [node133_eval, node135_eval]

theorem node137_check : node137 =
    Integer.Sparse.merge node87 node98 := by decide +kernel

theorem node137_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node137 x = (Integer.Sparse.eval node87 x + Integer.Sparse.eval node98 x) := by
  rw [node137_check, Integer.Sparse.eval_merge]

theorem node138_check : node138 =
    Integer.Sparse.merge node76 node137 := by decide +kernel

theorem node138_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node138 x = (Integer.Sparse.eval node76 x + (Integer.Sparse.eval node87 x + Integer.Sparse.eval node98 x)) := by
  rw [node138_check, Integer.Sparse.eval_merge]
  rw [node137_eval]

theorem node139_check : node139 =
    Integer.Sparse.merge node120 node131 := by decide +kernel

theorem node139_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node139 x = (Integer.Sparse.eval node120 x + Integer.Sparse.eval node131 x) := by
  rw [node139_check, Integer.Sparse.eval_merge]

theorem node140_check : node140 =
    Integer.Sparse.merge node109 node139 := by decide +kernel

theorem node140_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node140 x = (Integer.Sparse.eval node109 x + (Integer.Sparse.eval node120 x + Integer.Sparse.eval node131 x)) := by
  rw [node140_check, Integer.Sparse.eval_merge]
  rw [node139_eval]

theorem node141_check : node141 =
    Integer.Sparse.merge node138 node140 := by decide +kernel

theorem node141_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node141 x = ((Integer.Sparse.eval node76 x + (Integer.Sparse.eval node87 x + Integer.Sparse.eval node98 x)) + (Integer.Sparse.eval node109 x + (Integer.Sparse.eval node120 x + Integer.Sparse.eval node131 x))) := by
  rw [node141_check, Integer.Sparse.eval_merge]
  rw [node138_eval, node140_eval]

theorem node142_check : node142 =
    Integer.Sparse.merge node136 node141 := by decide +kernel

theorem node142_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node142 x = (((Integer.Sparse.eval node10 x + (Integer.Sparse.eval node21 x + Integer.Sparse.eval node32 x)) + (Integer.Sparse.eval node43 x + (Integer.Sparse.eval node54 x + Integer.Sparse.eval node65 x))) + ((Integer.Sparse.eval node76 x + (Integer.Sparse.eval node87 x + Integer.Sparse.eval node98 x)) + (Integer.Sparse.eval node109 x + (Integer.Sparse.eval node120 x + Integer.Sparse.eval node131 x)))) := by
  rw [node142_check, Integer.Sparse.eval_merge]
  rw [node136_eval, node141_eval]

end MUB6.Certificate.GramAssembly.Block5

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

theorem sum_expand_12 {R : Type*} [AddCommMonoid R] (F : Fin 12 → R) :
    (∑ i, F i) = (((F 0 + (F 1 + F 2)) + (F 3 + (F 4 + F 5))) + ((F 6 + (F 7 + F 8)) + (F 9 + (F 10 + F 11)))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F 0 + (F 1 + (F 2 + (F 3 + (F 4 + (F 5 + (F 6 + (F 7 + (F 8 + (F 9 + (F 10 + (F 11 + 0)))))))))))) = (((F 0 + (F 1 + F 2)) + (F 3 + (F 4 + F 5))) + ((F 6 + (F 7 + F 8)) + (F 9 + (F 10 + F 11))))
  simp only [add_zero, add_assoc]

end MUB6.Certificate.GramAssembly

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

open scoped BigOperators

theorem row_eval_0 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node10 x =
      ∑ j : Fin 12, (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x := by
  rw [node10_eval]
  exact (sum_expand_12 (fun j => (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x)).symm

theorem row_eval_1 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node21 x =
      ∑ j : Fin 12, (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x := by
  rw [node21_eval]
  exact (sum_expand_12 (fun j => (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x)).symm

theorem row_eval_2 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node32 x =
      ∑ j : Fin 12, (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x := by
  rw [node32_eval]
  exact (sum_expand_12 (fun j => (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x)).symm

theorem row_eval_3 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node43 x =
      ∑ j : Fin 12, (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x := by
  rw [node43_eval]
  exact (sum_expand_12 (fun j => (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x)).symm

theorem row_eval_4 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node54 x =
      ∑ j : Fin 12, (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x := by
  rw [node54_eval]
  exact (sum_expand_12 (fun j => (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x)).symm

theorem row_eval_5 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node65 x =
      ∑ j : Fin 12, (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x := by
  rw [node65_eval]
  exact (sum_expand_12 (fun j => (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x)).symm

theorem row_eval_6 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node76 x =
      ∑ j : Fin 12, (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x := by
  rw [node76_eval]
  exact (sum_expand_12 (fun j => (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x)).symm

theorem row_eval_7 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node87 x =
      ∑ j : Fin 12, (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x := by
  rw [node87_eval]
  exact (sum_expand_12 (fun j => (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x)).symm

theorem row_eval_8 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node98 x =
      ∑ j : Fin 12, (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x := by
  rw [node98_eval]
  exact (sum_expand_12 (fun j => (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x)).symm

theorem row_eval_9 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node109 x =
      ∑ j : Fin 12, (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x := by
  rw [node109_eval]
  exact (sum_expand_12 (fun j => (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x)).symm

theorem row_eval_10 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node120 x =
      ∑ j : Fin 12, (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x := by
  rw [node120_eval]
  exact (sum_expand_12 (fun j => (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x)).symm

theorem row_eval_11 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node131 x =
      ∑ j : Fin 12, (weights 11 j : ℝ) * Integer.Sparse.eval (entries 11 j) x := by
  rw [node131_eval]
  exact (sum_expand_12 (fun j => (weights 11 j : ℝ) * Integer.Sparse.eval (entries 11 j) x)).symm

theorem rows_eval (i : Fin 12) (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval (rows i) x =
      ∑ j : Fin 12, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  fin_cases i
  · exact row_eval_0 x
  · exact row_eval_1 x
  · exact row_eval_2 x
  · exact row_eval_3 x
  · exact row_eval_4 x
  · exact row_eval_5 x
  · exact row_eval_6 x
  · exact row_eval_7 x
  · exact row_eval_8 x
  · exact row_eval_9 x
  · exact row_eval_10 x
  · exact row_eval_11 x

theorem polynomial_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval polynomial x =
      ∑ i : Fin 12, ∑ j : Fin 12, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  calc
    _ = ∑ i : Fin 12, Integer.Sparse.eval (rows i) x := by
      rw [polynomial, node142_eval]
      exact (sum_expand_12 (fun i => Integer.Sparse.eval (rows i) x)).symm
    _ = _ := by simp_rw [rows_eval]

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Semantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.GramAssembly.Block5

theorem weights_real (i j : Fin 12) :
    (weights i j : ℝ) = realMatrix GramData.Block5.Z i j := by
  change (weights i j : ℝ) = (GramData.Block5.Z i j : ℝ)
  exact_mod_cast weights_cast i j

theorem polynomial_interpretation (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval polynomial (fun k => GramNormalization.eval B (key k)) =
      GramNonnegative.quadratic5 B := by
  rw [polynomial_eval]
  unfold GramNonnegative.quadratic5
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [indexed_entry_eval_e i j B hB, weights_real]

end MUB6.Certificate.GramAssembly.Block5

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Combined
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly

theorem combined0_check : combined0 =
    Integer.Sparse.merge (Integer.Sparse.scale 100 Block1.polynomial) (Integer.Sparse.scale 100 Block2.polynomial) := by decide +kernel

theorem combined0_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval combined0 x = ((100 : ℝ) * Integer.Sparse.eval Block1.polynomial x + (100 : ℝ) * Integer.Sparse.eval Block2.polynomial x) := by
  rw [combined0_check, Integer.Sparse.eval_merge]
  all_goals norm_num only [Integer.Sparse.eval_scale]

theorem combined1_check : combined1 =
    Integer.Sparse.merge (Integer.Sparse.scale 10 Block0.polynomial) combined0 := by decide +kernel

theorem combined1_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval combined1 x = ((10 : ℝ) * Integer.Sparse.eval Block0.polynomial x + ((100 : ℝ) * Integer.Sparse.eval Block1.polynomial x + (100 : ℝ) * Integer.Sparse.eval Block2.polynomial x)) := by
  rw [combined1_check, Integer.Sparse.eval_merge]
  rw [combined0_eval]
  all_goals norm_num only [Integer.Sparse.eval_scale]

theorem combined2_check : combined2 =
    Integer.Sparse.merge (Integer.Sparse.scale 10 Block4.polynomial) (Integer.Sparse.scale 1 Block5.polynomial) := by decide +kernel

theorem combined2_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval combined2 x = ((10 : ℝ) * Integer.Sparse.eval Block4.polynomial x + (1 : ℝ) * Integer.Sparse.eval Block5.polynomial x) := by
  rw [combined2_check, Integer.Sparse.eval_merge]
  all_goals norm_num only [Integer.Sparse.eval_scale]

theorem combined3_check : combined3 =
    Integer.Sparse.merge (Integer.Sparse.scale 10 Block3.polynomial) combined2 := by decide +kernel

theorem combined3_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval combined3 x = ((10 : ℝ) * Integer.Sparse.eval Block3.polynomial x + ((10 : ℝ) * Integer.Sparse.eval Block4.polynomial x + (1 : ℝ) * Integer.Sparse.eval Block5.polynomial x)) := by
  rw [combined3_check, Integer.Sparse.eval_merge]
  rw [combined2_eval]
  all_goals norm_num only [Integer.Sparse.eval_scale]

theorem combined4_check : combined4 =
    Integer.Sparse.merge combined1 combined3 := by decide +kernel

theorem combined4_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval combined4 x = (((10 : ℝ) * Integer.Sparse.eval Block0.polynomial x + ((100 : ℝ) * Integer.Sparse.eval Block1.polynomial x + (100 : ℝ) * Integer.Sparse.eval Block2.polynomial x)) + ((10 : ℝ) * Integer.Sparse.eval Block3.polynomial x + ((10 : ℝ) * Integer.Sparse.eval Block4.polynomial x + (1 : ℝ) * Integer.Sparse.eval Block5.polynomial x))) := by
  rw [combined4_check, Integer.Sparse.eval_merge]
  rw [combined1_eval, combined3_eval]

end MUB6.Certificate.GramAssembly

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Semantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.GramAssembly

theorem interpretation_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * Integer.Sparse.eval polynomial (fun k => GramNormalization.eval B (key k)) =
      GramNonnegative.sourceGram B := by
  rw [polynomial, combined4_eval]
  rw [Block0.polynomial_interpretation_e B hB, Block1.polynomial_interpretation_e B hB, Block2.polynomial_interpretation_e B hB, Block3.polynomial_interpretation_e B hB, Block4.polynomial_interpretation_e B hB, Block5.polynomial_interpretation B hB]
  norm_num only [GramNonnegative.sourceGram, GramFunctions.Block0.decimalExponent, GramFunctions.Block1.decimalExponent, GramFunctions.Block2.decimalExponent, GramFunctions.Block3.decimalExponent, GramFunctions.Block4.decimalExponent, GramFunctions.Block5.decimalExponent]
  all_goals ring

end MUB6.Certificate.GramAssembly

end

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.interpretation_e_oai := @OAI.MUB6.Certificate.GramAssembly.interpretation_e_oai
