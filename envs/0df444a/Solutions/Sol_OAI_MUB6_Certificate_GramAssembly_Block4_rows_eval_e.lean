-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block4.rows_eval_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T12:22:10.992487+00:00
-- url     : https://prove2.me/submissions/aa4bbaae-9f0f-4517-8ffc-d8671907b239

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E012
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block4_row_eval_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block4_row_eval_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block4_row_eval_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block4_row_eval_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block4_row_eval_6_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node0_check : node0 =
    Integer.Sparse.merge (Integer.Sparse.scale (17001745) entry_0_0) (Integer.Sparse.scale (2527050) entry_0_1) := by decide +kernel

theorem node0_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node0 x = (((17001745 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + ((2527050 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x) := by
  rw [node0_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node1_check : node1 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6681691) entry_0_3) (Integer.Sparse.scale (1894258) entry_0_4) := by decide +kernel

theorem node1_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node1 x = (((-6681691 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((1894258 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x) := by
  rw [node1_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node2_check : node2 =
    Integer.Sparse.merge (Integer.Sparse.scale (5536296) entry_0_2) node1 := by decide +kernel

theorem node2_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node2 x = (((5536296 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x + (((-6681691 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((1894258 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x)) := by
  rw [node2_check, Integer.Sparse.eval_merge]
  rw [node1_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node3_check : node3 =
    Integer.Sparse.merge node0 node2 := by decide +kernel

theorem node3_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node3 x = ((((17001745 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + ((2527050 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x) + (((5536296 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x + (((-6681691 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((1894258 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x))) := by
  rw [node3_check, Integer.Sparse.eval_merge]
  rw [node0_eval, node2_eval]

theorem node4_check : node4 =
    Integer.Sparse.merge (Integer.Sparse.scale (2181374) entry_0_6) (Integer.Sparse.scale (2283451) entry_0_7) := by decide +kernel

theorem node4_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node4 x = (((2181374 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x + ((2283451 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x) := by
  rw [node4_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node5_check : node5 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1068497) entry_0_5) node4 := by decide +kernel

theorem node5_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node5 x = (((-1068497 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x + (((2181374 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x + ((2283451 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x)) := by
  rw [node5_check, Integer.Sparse.eval_merge]
  rw [node4_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node6_check : node6 =
    Integer.Sparse.merge (Integer.Sparse.scale (5122348) entry_0_9) (Integer.Sparse.scale (11944156) entry_0_10) := by decide +kernel

theorem node6_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node6 x = (((5122348 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + ((11944156 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x) := by
  rw [node6_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node7_check : node7 =
    Integer.Sparse.merge (Integer.Sparse.scale (5870760) entry_0_8) node6 := by decide +kernel

theorem node7_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node7 x = (((5870760 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x + (((5122348 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + ((11944156 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x)) := by
  rw [node7_check, Integer.Sparse.eval_merge]
  rw [node6_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node8_check : node8 =
    Integer.Sparse.merge node5 node7 := by decide +kernel

theorem node8_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node8 x = ((((-1068497 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x + (((2181374 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x + ((2283451 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x)) + (((5870760 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x + (((5122348 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + ((11944156 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x))) := by
  rw [node8_check, Integer.Sparse.eval_merge]
  rw [node5_eval, node7_eval]

theorem node9_check : node9 =
    Integer.Sparse.merge node3 node8 := by decide +kernel

theorem node9_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node9 x = (((((17001745 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + ((2527050 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x) + (((5536296 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x + (((-6681691 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((1894258 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x))) + ((((-1068497 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x + (((2181374 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x + ((2283451 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x)) + (((5870760 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x + (((5122348 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + ((11944156 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x)))) := by
  rw [node9_check, Integer.Sparse.eval_merge]
  rw [node3_eval, node8_eval]

theorem node10_check : node10 =
    Integer.Sparse.merge (Integer.Sparse.scale (4278803) entry_0_11) (Integer.Sparse.scale (-12939117) entry_0_12) := by decide +kernel

theorem node10_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node10 x = (((4278803 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x + ((-12939117 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_12 x) := by
  rw [node10_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node11_check : node11 =
    Integer.Sparse.merge (Integer.Sparse.scale (12048267) entry_0_14) (Integer.Sparse.scale (-1896215) entry_0_15) := by decide +kernel

theorem node11_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node11 x = (((12048267 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_14 x + ((-1896215 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_15 x) := by
  rw [node11_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node12_check : node12 =
    Integer.Sparse.merge (Integer.Sparse.scale (-653324) entry_0_13) node11 := by decide +kernel

theorem node12_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node12 x = (((-653324 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_13 x + (((12048267 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_14 x + ((-1896215 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_15 x)) := by
  rw [node12_check, Integer.Sparse.eval_merge]
  rw [node11_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node13_check : node13 =
    Integer.Sparse.merge node10 node12 := by decide +kernel

theorem node13_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node13 x = ((((4278803 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x + ((-12939117 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_12 x) + (((-653324 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_13 x + (((12048267 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_14 x + ((-1896215 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_15 x))) := by
  rw [node13_check, Integer.Sparse.eval_merge]
  rw [node10_eval, node12_eval]

theorem node14_check : node14 =
    Integer.Sparse.merge (Integer.Sparse.scale (-814376) entry_0_17) (Integer.Sparse.scale (-2263423) entry_0_18) := by decide +kernel

theorem node14_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node14 x = (((-814376 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_17 x + ((-2263423 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_18 x) := by
  rw [node14_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node15_check : node15 =
    Integer.Sparse.merge (Integer.Sparse.scale (4000099) entry_0_16) node14 := by decide +kernel

theorem node15_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node15 x = (((4000099 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_16 x + (((-814376 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_17 x + ((-2263423 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_18 x)) := by
  rw [node15_check, Integer.Sparse.eval_merge]
  rw [node14_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node16_check : node16 =
    Integer.Sparse.merge (Integer.Sparse.scale (-7748966) entry_0_20) (Integer.Sparse.scale (-15099711) entry_0_21) := by decide +kernel

theorem node16_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node16 x = (((-7748966 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_20 x + ((-15099711 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_21 x) := by
  rw [node16_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node17_check : node17 =
    Integer.Sparse.merge (Integer.Sparse.scale (-227986) entry_0_19) node16 := by decide +kernel

theorem node17_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node17 x = (((-227986 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_19 x + (((-7748966 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_20 x + ((-15099711 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_21 x)) := by
  rw [node17_check, Integer.Sparse.eval_merge]
  rw [node16_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node18_check : node18 =
    Integer.Sparse.merge node15 node17 := by decide +kernel

theorem node18_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node18 x = ((((4000099 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_16 x + (((-814376 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_17 x + ((-2263423 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_18 x)) + (((-227986 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_19 x + (((-7748966 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_20 x + ((-15099711 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_21 x))) := by
  rw [node18_check, Integer.Sparse.eval_merge]
  rw [node15_eval, node17_eval]

theorem node19_check : node19 =
    Integer.Sparse.merge node13 node18 := by decide +kernel

theorem node19_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node19 x = (((((4278803 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x + ((-12939117 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_12 x) + (((-653324 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_13 x + (((12048267 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_14 x + ((-1896215 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_15 x))) + ((((4000099 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_16 x + (((-814376 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_17 x + ((-2263423 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_18 x)) + (((-227986 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_19 x + (((-7748966 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_20 x + ((-15099711 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_21 x)))) := by
  rw [node19_check, Integer.Sparse.eval_merge]
  rw [node13_eval, node18_eval]

theorem node20_check : node20 =
    Integer.Sparse.merge node9 node19 := by decide +kernel

theorem node20_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node20 x = ((((((17001745 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + ((2527050 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x) + (((5536296 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x + (((-6681691 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((1894258 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x))) + ((((-1068497 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x + (((2181374 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x + ((2283451 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x)) + (((5870760 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x + (((5122348 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + ((11944156 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x)))) + (((((4278803 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x + ((-12939117 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_12 x) + (((-653324 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_13 x + (((12048267 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_14 x + ((-1896215 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_15 x))) + ((((4000099 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_16 x + (((-814376 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_17 x + ((-2263423 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_18 x)) + (((-227986 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_19 x + (((-7748966 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_20 x + ((-15099711 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_21 x))))) := by
  rw [node20_check, Integer.Sparse.eval_merge]
  rw [node9_eval, node19_eval]

theorem node21_check : node21 =
    Integer.Sparse.merge (Integer.Sparse.scale (2527050) entry_1_0) (Integer.Sparse.scale (4519314) entry_1_1) := by decide +kernel

theorem node21_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node21 x = (((2527050 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + ((4519314 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x) := by
  rw [node21_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node22_check : node22 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1483567) entry_1_3) (Integer.Sparse.scale (3743702) entry_1_4) := by decide +kernel

theorem node22_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node22 x = (((-1483567 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((3743702 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x) := by
  rw [node22_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node23_check : node23 =
    Integer.Sparse.merge (Integer.Sparse.scale (4041704) entry_1_2) node22 := by decide +kernel

theorem node23_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node23 x = (((4041704 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x + (((-1483567 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((3743702 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x)) := by
  rw [node23_check, Integer.Sparse.eval_merge]
  rw [node22_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node24_check : node24 =
    Integer.Sparse.merge node21 node23 := by decide +kernel

theorem node24_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node24 x = ((((2527050 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + ((4519314 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x) + (((4041704 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x + (((-1483567 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((3743702 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x))) := by
  rw [node24_check, Integer.Sparse.eval_merge]
  rw [node21_eval, node23_eval]

theorem node25_check : node25 =
    Integer.Sparse.merge (Integer.Sparse.scale (6647397) entry_1_6) (Integer.Sparse.scale (-394829) entry_1_7) := by decide +kernel

theorem node25_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node25 x = (((6647397 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + ((-394829 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x) := by
  rw [node25_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node26_check : node26 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2156927) entry_1_5) node25 := by decide +kernel

theorem node26_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node26 x = (((-2156927 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x + (((6647397 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + ((-394829 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x)) := by
  rw [node26_check, Integer.Sparse.eval_merge]
  rw [node25_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node27_check : node27 =
    Integer.Sparse.merge (Integer.Sparse.scale (-292814) entry_1_9) (Integer.Sparse.scale (8387639) entry_1_10) := by decide +kernel

theorem node27_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node27 x = (((-292814 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((8387639 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x) := by
  rw [node27_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node28_check : node28 =
    Integer.Sparse.merge (Integer.Sparse.scale (5057136) entry_1_8) node27 := by decide +kernel

theorem node28_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node28 x = (((5057136 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x + (((-292814 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((8387639 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x)) := by
  rw [node28_check, Integer.Sparse.eval_merge]
  rw [node27_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node29_check : node29 =
    Integer.Sparse.merge node26 node28 := by decide +kernel

theorem node29_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node29 x = ((((-2156927 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x + (((6647397 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + ((-394829 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x)) + (((5057136 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x + (((-292814 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((8387639 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x))) := by
  rw [node29_check, Integer.Sparse.eval_merge]
  rw [node26_eval, node28_eval]

theorem node30_check : node30 =
    Integer.Sparse.merge node24 node29 := by decide +kernel

theorem node30_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node30 x = (((((2527050 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + ((4519314 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x) + (((4041704 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x + (((-1483567 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((3743702 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x))) + ((((-2156927 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x + (((6647397 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + ((-394829 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x)) + (((5057136 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x + (((-292814 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((8387639 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x)))) := by
  rw [node30_check, Integer.Sparse.eval_merge]
  rw [node24_eval, node29_eval]

theorem node31_check : node31 =
    Integer.Sparse.merge (Integer.Sparse.scale (3154912) entry_1_11) (Integer.Sparse.scale (-8313712) entry_1_12) := by decide +kernel

theorem node31_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node31 x = (((3154912 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x + ((-8313712 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x) := by
  rw [node31_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node32_check : node32 =
    Integer.Sparse.merge (Integer.Sparse.scale (10815796) entry_1_14) (Integer.Sparse.scale (10377904) entry_1_15) := by decide +kernel

theorem node32_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node32 x = (((10815796 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x + ((10377904 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x) := by
  rw [node32_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node33_check : node33 =
    Integer.Sparse.merge (Integer.Sparse.scale (3042363) entry_1_13) node32 := by decide +kernel

theorem node33_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node33 x = (((3042363 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + (((10815796 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x + ((10377904 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x)) := by
  rw [node33_check, Integer.Sparse.eval_merge]
  rw [node32_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node34_check : node34 =
    Integer.Sparse.merge node31 node33 := by decide +kernel

theorem node34_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node34 x = ((((3154912 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x + ((-8313712 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x) + (((3042363 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + (((10815796 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x + ((10377904 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x))) := by
  rw [node34_check, Integer.Sparse.eval_merge]
  rw [node31_eval, node33_eval]

theorem node35_check : node35 =
    Integer.Sparse.merge (Integer.Sparse.scale (1579557) entry_1_17) (Integer.Sparse.scale (804909) entry_1_18) := by decide +kernel

theorem node35_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node35 x = (((1579557 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x + ((804909 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x) := by
  rw [node35_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node36_check : node36 =
    Integer.Sparse.merge (Integer.Sparse.scale (-11676267) entry_1_16) node35 := by decide +kernel

theorem node36_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node36 x = (((-11676267 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + (((1579557 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x + ((804909 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x)) := by
  rw [node36_check, Integer.Sparse.eval_merge]
  rw [node35_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node37_check : node37 =
    Integer.Sparse.merge (Integer.Sparse.scale (236179) entry_1_20) (Integer.Sparse.scale (6258575) entry_1_21) := by decide +kernel

theorem node37_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node37 x = (((236179 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x + ((6258575 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_21 x) := by
  rw [node37_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node38_check : node38 =
    Integer.Sparse.merge (Integer.Sparse.scale (-14681) entry_1_19) node37 := by decide +kernel

theorem node38_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node38 x = (((-14681 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x + (((236179 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x + ((6258575 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_21 x)) := by
  rw [node38_check, Integer.Sparse.eval_merge]
  rw [node37_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node39_check : node39 =
    Integer.Sparse.merge node36 node38 := by decide +kernel

theorem node39_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node39 x = ((((-11676267 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + (((1579557 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x + ((804909 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x)) + (((-14681 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x + (((236179 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x + ((6258575 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_21 x))) := by
  rw [node39_check, Integer.Sparse.eval_merge]
  rw [node36_eval, node38_eval]

theorem node40_check : node40 =
    Integer.Sparse.merge node34 node39 := by decide +kernel

theorem node40_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node40 x = (((((3154912 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x + ((-8313712 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x) + (((3042363 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + (((10815796 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x + ((10377904 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x))) + ((((-11676267 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + (((1579557 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x + ((804909 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x)) + (((-14681 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x + (((236179 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x + ((6258575 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_21 x)))) := by
  rw [node40_check, Integer.Sparse.eval_merge]
  rw [node34_eval, node39_eval]

theorem node41_check : node41 =
    Integer.Sparse.merge node30 node40 := by decide +kernel

theorem node41_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node41 x = ((((((2527050 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + ((4519314 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x) + (((4041704 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x + (((-1483567 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((3743702 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x))) + ((((-2156927 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x + (((6647397 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + ((-394829 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x)) + (((5057136 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x + (((-292814 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((8387639 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x)))) + (((((3154912 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x + ((-8313712 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x) + (((3042363 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + (((10815796 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x + ((10377904 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x))) + ((((-11676267 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + (((1579557 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x + ((804909 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x)) + (((-14681 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x + (((236179 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x + ((6258575 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_21 x))))) := by
  rw [node41_check, Integer.Sparse.eval_merge]
  rw [node30_eval, node40_eval]

theorem node42_check : node42 =
    Integer.Sparse.merge (Integer.Sparse.scale (5536296) entry_2_0) (Integer.Sparse.scale (4041704) entry_2_1) := by decide +kernel

theorem node42_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node42 x = (((5536296 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + ((4041704 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x) := by
  rw [node42_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node43_check : node43 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6443349) entry_2_3) (Integer.Sparse.scale (4926450) entry_2_4) := by decide +kernel

theorem node43_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node43 x = (((-6443349 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((4926450 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x) := by
  rw [node43_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node44_check : node44 =
    Integer.Sparse.merge (Integer.Sparse.scale (9649493) entry_2_2) node43 := by decide +kernel

theorem node44_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node44 x = (((9649493 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x + (((-6443349 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((4926450 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x)) := by
  rw [node44_check, Integer.Sparse.eval_merge]
  rw [node43_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node45_check : node45 =
    Integer.Sparse.merge node42 node44 := by decide +kernel

theorem node45_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node45 x = ((((5536296 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + ((4041704 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x) + (((9649493 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x + (((-6443349 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((4926450 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x))) := by
  rw [node45_check, Integer.Sparse.eval_merge]
  rw [node42_eval, node44_eval]

theorem node46_check : node46 =
    Integer.Sparse.merge (Integer.Sparse.scale (8255371) entry_2_6) (Integer.Sparse.scale (1999663) entry_2_7) := by decide +kernel

theorem node46_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node46 x = (((8255371 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + ((1999663 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x) := by
  rw [node46_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node47_check : node47 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2350703) entry_2_5) node46 := by decide +kernel

theorem node47_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node47 x = (((-2350703 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x + (((8255371 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + ((1999663 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x)) := by
  rw [node47_check, Integer.Sparse.eval_merge]
  rw [node46_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node48_check : node48 =
    Integer.Sparse.merge (Integer.Sparse.scale (1200964) entry_2_9) (Integer.Sparse.scale (9488222) entry_2_10) := by decide +kernel

theorem node48_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node48 x = (((1200964 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((9488222 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x) := by
  rw [node48_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node49_check : node49 =
    Integer.Sparse.merge (Integer.Sparse.scale (9422497) entry_2_8) node48 := by decide +kernel

theorem node49_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node49 x = (((9422497 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x + (((1200964 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((9488222 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x)) := by
  rw [node49_check, Integer.Sparse.eval_merge]
  rw [node48_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node50_check : node50 =
    Integer.Sparse.merge node47 node49 := by decide +kernel

theorem node50_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node50 x = ((((-2350703 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x + (((8255371 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + ((1999663 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x)) + (((9422497 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x + (((1200964 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((9488222 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x))) := by
  rw [node50_check, Integer.Sparse.eval_merge]
  rw [node47_eval, node49_eval]

theorem node51_check : node51 =
    Integer.Sparse.merge node45 node50 := by decide +kernel

theorem node51_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node51 x = (((((5536296 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + ((4041704 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x) + (((9649493 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x + (((-6443349 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((4926450 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x))) + ((((-2350703 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x + (((8255371 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + ((1999663 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x)) + (((9422497 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x + (((1200964 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((9488222 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x)))) := by
  rw [node51_check, Integer.Sparse.eval_merge]
  rw [node45_eval, node50_eval]

theorem node52_check : node52 =
    Integer.Sparse.merge (Integer.Sparse.scale (3809106) entry_2_11) (Integer.Sparse.scale (-16699012) entry_2_12) := by decide +kernel

theorem node52_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node52 x = (((3809106 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x + ((-16699012 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x) := by
  rw [node52_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node53_check : node53 =
    Integer.Sparse.merge (Integer.Sparse.scale (15992020) entry_2_14) (Integer.Sparse.scale (16606019) entry_2_15) := by decide +kernel

theorem node53_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node53 x = (((15992020 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x + ((16606019 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x) := by
  rw [node53_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node54_check : node54 =
    Integer.Sparse.merge (Integer.Sparse.scale (533958) entry_2_13) node53 := by decide +kernel

theorem node54_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node54 x = (((533958 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + (((15992020 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x + ((16606019 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x)) := by
  rw [node54_check, Integer.Sparse.eval_merge]
  rw [node53_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node55_check : node55 =
    Integer.Sparse.merge node52 node54 := by decide +kernel

theorem node55_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node55 x = ((((3809106 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x + ((-16699012 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x) + (((533958 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + (((15992020 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x + ((16606019 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x))) := by
  rw [node55_check, Integer.Sparse.eval_merge]
  rw [node52_eval, node54_eval]

theorem node56_check : node56 =
    Integer.Sparse.merge (Integer.Sparse.scale (1552071) entry_2_17) (Integer.Sparse.scale (1207709) entry_2_18) := by decide +kernel

theorem node56_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node56 x = (((1552071 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x + ((1207709 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x) := by
  rw [node56_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node57_check : node57 =
    Integer.Sparse.merge (Integer.Sparse.scale (-11528195) entry_2_16) node56 := by decide +kernel

theorem node57_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node57 x = (((-11528195 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + (((1552071 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x + ((1207709 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x)) := by
  rw [node57_check, Integer.Sparse.eval_merge]
  rw [node56_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node58_check : node58 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2753502) entry_2_20) (Integer.Sparse.scale (220430) entry_2_21) := by decide +kernel

theorem node58_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node58 x = (((-2753502 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x + ((220430 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_21 x) := by
  rw [node58_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node59_check : node59 =
    Integer.Sparse.merge (Integer.Sparse.scale (97824) entry_2_19) node58 := by decide +kernel

theorem node59_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node59 x = (((97824 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x + (((-2753502 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x + ((220430 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_21 x)) := by
  rw [node59_check, Integer.Sparse.eval_merge]
  rw [node58_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node60_check : node60 =
    Integer.Sparse.merge node57 node59 := by decide +kernel

theorem node60_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node60 x = ((((-11528195 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + (((1552071 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x + ((1207709 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x)) + (((97824 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x + (((-2753502 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x + ((220430 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_21 x))) := by
  rw [node60_check, Integer.Sparse.eval_merge]
  rw [node57_eval, node59_eval]

theorem node61_check : node61 =
    Integer.Sparse.merge node55 node60 := by decide +kernel

theorem node61_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node61 x = (((((3809106 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x + ((-16699012 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x) + (((533958 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + (((15992020 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x + ((16606019 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x))) + ((((-11528195 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + (((1552071 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x + ((1207709 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x)) + (((97824 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x + (((-2753502 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x + ((220430 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_21 x)))) := by
  rw [node61_check, Integer.Sparse.eval_merge]
  rw [node55_eval, node60_eval]

theorem node62_check : node62 =
    Integer.Sparse.merge node51 node61 := by decide +kernel

theorem node62_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node62 x = ((((((5536296 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + ((4041704 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x) + (((9649493 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x + (((-6443349 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((4926450 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x))) + ((((-2350703 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x + (((8255371 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + ((1999663 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x)) + (((9422497 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x + (((1200964 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((9488222 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x)))) + (((((3809106 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x + ((-16699012 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x) + (((533958 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + (((15992020 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x + ((16606019 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x))) + ((((-11528195 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + (((1552071 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x + ((1207709 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x)) + (((97824 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x + (((-2753502 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x + ((220430 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_21 x))))) := by
  rw [node62_check, Integer.Sparse.eval_merge]
  rw [node51_eval, node61_eval]

theorem node63_check : node63 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6681691) entry_3_0) (Integer.Sparse.scale (-1483567) entry_3_1) := by decide +kernel

theorem node63_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node63 x = (((-6681691 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-1483567 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) := by
  rw [node63_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node64_check : node64 =
    Integer.Sparse.merge (Integer.Sparse.scale (10582467) entry_3_3) (Integer.Sparse.scale (-4013447) entry_3_4) := by decide +kernel

theorem node64_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node64 x = (((10582467 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x) := by
  rw [node64_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node65_check : node65 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6443349) entry_3_2) node64 := by decide +kernel

theorem node65_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node65 x = (((-6443349 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((10582467 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x)) := by
  rw [node65_check, Integer.Sparse.eval_merge]
  rw [node64_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node66_check : node66 =
    Integer.Sparse.merge node63 node65 := by decide +kernel

theorem node66_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node66 x = ((((-6681691 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-1483567 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) + (((-6443349 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((10582467 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x))) := by
  rw [node66_check, Integer.Sparse.eval_merge]
  rw [node63_eval, node65_eval]

theorem node67_check : node67 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4628999) entry_3_6) (Integer.Sparse.scale (-2274383) entry_3_7) := by decide +kernel

theorem node67_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node67 x = (((-4628999 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + ((-2274383 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x) := by
  rw [node67_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node68_check : node68 =
    Integer.Sparse.merge (Integer.Sparse.scale (507536) entry_3_5) node67 := by decide +kernel

theorem node68_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node68 x = (((507536 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + (((-4628999 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + ((-2274383 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x)) := by
  rw [node68_check, Integer.Sparse.eval_merge]
  rw [node67_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node69_check : node69 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2349413) entry_3_9) (Integer.Sparse.scale (-3559336) entry_3_10) := by decide +kernel

theorem node69_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node69 x = (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((-3559336 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x) := by
  rw [node69_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node70_check : node70 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3889906) entry_3_8) node69 := by decide +kernel

theorem node70_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node70 x = (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((-3559336 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x)) := by
  rw [node70_check, Integer.Sparse.eval_merge]
  rw [node69_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node71_check : node71 =
    Integer.Sparse.merge node68 node70 := by decide +kernel

theorem node71_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node71 x = ((((507536 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + (((-4628999 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + ((-2274383 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x)) + (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((-3559336 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x))) := by
  rw [node71_check, Integer.Sparse.eval_merge]
  rw [node68_eval, node70_eval]

theorem node72_check : node72 =
    Integer.Sparse.merge node66 node71 := by decide +kernel

theorem node72_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node72 x = (((((-6681691 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-1483567 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) + (((-6443349 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((10582467 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x))) + ((((507536 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + (((-4628999 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + ((-2274383 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x)) + (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((-3559336 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x)))) := by
  rw [node72_check, Integer.Sparse.eval_merge]
  rw [node66_eval, node71_eval]

theorem node73_check : node73 =
    Integer.Sparse.merge (Integer.Sparse.scale (112700) entry_3_11) (Integer.Sparse.scale (12695356) entry_3_12) := by decide +kernel

theorem node73_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node73 x = (((112700 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((12695356 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x) := by
  rw [node73_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node74_check : node74 =
    Integer.Sparse.merge (Integer.Sparse.scale (-7453387) entry_3_14) (Integer.Sparse.scale (-14511117) entry_3_15) := by decide +kernel

theorem node74_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node74 x = (((-7453387 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-14511117 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x) := by
  rw [node74_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node75_check : node75 =
    Integer.Sparse.merge (Integer.Sparse.scale (3371581) entry_3_13) node74 := by decide +kernel

theorem node75_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node75 x = (((3371581 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + (((-7453387 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-14511117 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x)) := by
  rw [node75_check, Integer.Sparse.eval_merge]
  rw [node74_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node76_check : node76 =
    Integer.Sparse.merge node73 node75 := by decide +kernel

theorem node76_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node76 x = ((((112700 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((12695356 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x) + (((3371581 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + (((-7453387 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-14511117 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x))) := by
  rw [node76_check, Integer.Sparse.eval_merge]
  rw [node73_eval, node75_eval]

theorem node77_check : node77 =
    Integer.Sparse.merge (Integer.Sparse.scale (189281) entry_3_17) (Integer.Sparse.scale (-767850) entry_3_18) := by decide +kernel

theorem node77_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node77 x = (((189281 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x + ((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x) := by
  rw [node77_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node78_check : node78 =
    Integer.Sparse.merge (Integer.Sparse.scale (-146963) entry_3_16) node77 := by decide +kernel

theorem node78_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node78 x = (((-146963 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + (((189281 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x + ((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x)) := by
  rw [node78_check, Integer.Sparse.eval_merge]
  rw [node77_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node79_check : node79 =
    Integer.Sparse.merge (Integer.Sparse.scale (4576468) entry_3_20) (Integer.Sparse.scale (7350062) entry_3_21) := by decide +kernel

theorem node79_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node79 x = (((4576468 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x + ((7350062 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_21 x) := by
  rw [node79_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node80_check : node80 =
    Integer.Sparse.merge (Integer.Sparse.scale (318017) entry_3_19) node79 := by decide +kernel

theorem node80_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node80 x = (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + (((4576468 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x + ((7350062 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_21 x)) := by
  rw [node80_check, Integer.Sparse.eval_merge]
  rw [node79_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node81_check : node81 =
    Integer.Sparse.merge node78 node80 := by decide +kernel

theorem node81_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node81 x = ((((-146963 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + (((189281 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x + ((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x)) + (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + (((4576468 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x + ((7350062 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_21 x))) := by
  rw [node81_check, Integer.Sparse.eval_merge]
  rw [node78_eval, node80_eval]

theorem node82_check : node82 =
    Integer.Sparse.merge node76 node81 := by decide +kernel

theorem node82_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node82 x = (((((112700 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((12695356 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x) + (((3371581 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + (((-7453387 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-14511117 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x))) + ((((-146963 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + (((189281 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x + ((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x)) + (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + (((4576468 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x + ((7350062 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_21 x)))) := by
  rw [node82_check, Integer.Sparse.eval_merge]
  rw [node76_eval, node81_eval]

theorem node83_check : node83 =
    Integer.Sparse.merge node72 node82 := by decide +kernel

theorem node83_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node83 x = ((((((-6681691 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-1483567 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) + (((-6443349 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((10582467 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x))) + ((((507536 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + (((-4628999 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + ((-2274383 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x)) + (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((-3559336 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x)))) + (((((112700 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((12695356 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x) + (((3371581 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + (((-7453387 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-14511117 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x))) + ((((-146963 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + (((189281 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x + ((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x)) + (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + (((4576468 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x + ((7350062 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_21 x))))) := by
  rw [node83_check, Integer.Sparse.eval_merge]
  rw [node72_eval, node82_eval]

theorem node84_check : node84 =
    Integer.Sparse.merge (Integer.Sparse.scale (1894258) entry_4_0) (Integer.Sparse.scale (3743702) entry_4_1) := by decide +kernel

theorem node84_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node84 x = (((1894258 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((3743702 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) := by
  rw [node84_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node85_check : node85 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4013447) entry_4_3) (Integer.Sparse.scale (8001862) entry_4_4) := by decide +kernel

theorem node85_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node85 x = (((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((8001862 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x) := by
  rw [node85_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node86_check : node86 =
    Integer.Sparse.merge (Integer.Sparse.scale (4926450) entry_4_2) node85 := by decide +kernel

theorem node86_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node86 x = (((4926450 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((8001862 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x)) := by
  rw [node86_check, Integer.Sparse.eval_merge]
  rw [node85_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node87_check : node87 =
    Integer.Sparse.merge node84 node86 := by decide +kernel

theorem node87_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node87 x = ((((1894258 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((3743702 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) + (((4926450 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((8001862 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x))) := by
  rw [node87_check, Integer.Sparse.eval_merge]
  rw [node84_eval, node86_eval]

theorem node88_check : node88 =
    Integer.Sparse.merge (Integer.Sparse.scale (3463174) entry_4_6) (Integer.Sparse.scale (2764593) entry_4_7) := by decide +kernel

theorem node88_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node88 x = (((3463174 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + ((2764593 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x) := by
  rw [node88_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node89_check : node89 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2149155) entry_4_5) node88 := by decide +kernel

theorem node89_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node89 x = (((-2149155 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + (((3463174 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + ((2764593 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x)) := by
  rw [node89_check, Integer.Sparse.eval_merge]
  rw [node88_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node90_check : node90 =
    Integer.Sparse.merge (Integer.Sparse.scale (-683505) entry_4_9) (Integer.Sparse.scale (5967631) entry_4_10) := by decide +kernel

theorem node90_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node90 x = (((-683505 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((5967631 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x) := by
  rw [node90_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node91_check : node91 =
    Integer.Sparse.merge (Integer.Sparse.scale (3803854) entry_4_8) node90 := by decide +kernel

theorem node91_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node91 x = (((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + (((-683505 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((5967631 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x)) := by
  rw [node91_check, Integer.Sparse.eval_merge]
  rw [node90_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node92_check : node92 =
    Integer.Sparse.merge node89 node91 := by decide +kernel

theorem node92_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node92 x = ((((-2149155 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + (((3463174 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + ((2764593 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x)) + (((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + (((-683505 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((5967631 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x))) := by
  rw [node92_check, Integer.Sparse.eval_merge]
  rw [node89_eval, node91_eval]

theorem node93_check : node93 =
    Integer.Sparse.merge node87 node92 := by decide +kernel

theorem node93_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node93 x = (((((1894258 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((3743702 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) + (((4926450 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((8001862 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x))) + ((((-2149155 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + (((3463174 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + ((2764593 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x)) + (((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + (((-683505 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((5967631 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x)))) := by
  rw [node93_check, Integer.Sparse.eval_merge]
  rw [node87_eval, node92_eval]

theorem node94_check : node94 =
    Integer.Sparse.merge (Integer.Sparse.scale (3481743) entry_4_11) (Integer.Sparse.scale (-11947838) entry_4_12) := by decide +kernel

theorem node94_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node94 x = (((3481743 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x + ((-11947838 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_12 x) := by
  rw [node94_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node95_check : node95 =
    Integer.Sparse.merge (Integer.Sparse.scale (4800575) entry_4_14) (Integer.Sparse.scale (22116163) entry_4_15) := by decide +kernel

theorem node95_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node95 x = (((4800575 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x + ((22116163 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_15 x) := by
  rw [node95_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node96_check : node96 =
    Integer.Sparse.merge (Integer.Sparse.scale (2934355) entry_4_13) node95 := by decide +kernel

theorem node96_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node96 x = (((2934355 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_13 x + (((4800575 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x + ((22116163 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_15 x)) := by
  rw [node96_check, Integer.Sparse.eval_merge]
  rw [node95_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node97_check : node97 =
    Integer.Sparse.merge node94 node96 := by decide +kernel

theorem node97_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node97 x = ((((3481743 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x + ((-11947838 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_12 x) + (((2934355 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_13 x + (((4800575 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x + ((22116163 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_15 x))) := by
  rw [node97_check, Integer.Sparse.eval_merge]
  rw [node94_eval, node96_eval]

theorem node98_check : node98 =
    Integer.Sparse.merge (Integer.Sparse.scale (1039608) entry_4_17) (Integer.Sparse.scale (3446947) entry_4_18) := by decide +kernel

theorem node98_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node98 x = (((1039608 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x + ((3446947 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_18 x) := by
  rw [node98_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node99_check : node99 =
    Integer.Sparse.merge (Integer.Sparse.scale (-8882925) entry_4_16) node98 := by decide +kernel

theorem node99_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node99 x = (((-8882925 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_16 x + (((1039608 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x + ((3446947 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_18 x)) := by
  rw [node99_check, Integer.Sparse.eval_merge]
  rw [node98_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node100_check : node100 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4019963) entry_4_20) (Integer.Sparse.scale (3505349) entry_4_21) := by decide +kernel

theorem node100_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node100 x = (((-4019963 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_20 x + ((3505349 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_21 x) := by
  rw [node100_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node101_check : node101 =
    Integer.Sparse.merge (Integer.Sparse.scale (-11230) entry_4_19) node100 := by decide +kernel

theorem node101_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node101 x = (((-11230 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_19 x + (((-4019963 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_20 x + ((3505349 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_21 x)) := by
  rw [node101_check, Integer.Sparse.eval_merge]
  rw [node100_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node102_check : node102 =
    Integer.Sparse.merge node99 node101 := by decide +kernel

theorem node102_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node102 x = ((((-8882925 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_16 x + (((1039608 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x + ((3446947 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_18 x)) + (((-11230 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_19 x + (((-4019963 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_20 x + ((3505349 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_21 x))) := by
  rw [node102_check, Integer.Sparse.eval_merge]
  rw [node99_eval, node101_eval]

theorem node103_check : node103 =
    Integer.Sparse.merge node97 node102 := by decide +kernel

theorem node103_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node103 x = (((((3481743 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x + ((-11947838 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_12 x) + (((2934355 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_13 x + (((4800575 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x + ((22116163 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_15 x))) + ((((-8882925 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_16 x + (((1039608 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x + ((3446947 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_18 x)) + (((-11230 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_19 x + (((-4019963 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_20 x + ((3505349 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_21 x)))) := by
  rw [node103_check, Integer.Sparse.eval_merge]
  rw [node97_eval, node102_eval]

theorem node104_check : node104 =
    Integer.Sparse.merge node93 node103 := by decide +kernel

theorem node104_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node104 x = ((((((1894258 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((3743702 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) + (((4926450 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((-4013447 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((8001862 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x))) + ((((-2149155 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + (((3463174 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + ((2764593 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x)) + (((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + (((-683505 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((5967631 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x)))) + (((((3481743 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x + ((-11947838 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_12 x) + (((2934355 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_13 x + (((4800575 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x + ((22116163 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_15 x))) + ((((-8882925 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_16 x + (((1039608 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x + ((3446947 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_18 x)) + (((-11230 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_19 x + (((-4019963 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_20 x + ((3505349 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_21 x))))) := by
  rw [node104_check, Integer.Sparse.eval_merge]
  rw [node93_eval, node103_eval]

theorem node105_check : node105 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1068497) entry_5_0) (Integer.Sparse.scale (-2156927) entry_5_1) := by decide +kernel

theorem node105_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node105 x = (((-1068497 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + ((-2156927 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x) := by
  rw [node105_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node106_check : node106 =
    Integer.Sparse.merge (Integer.Sparse.scale (507536) entry_5_3) (Integer.Sparse.scale (-2149155) entry_5_4) := by decide +kernel

theorem node106_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node106 x = (((507536 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + ((-2149155 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x) := by
  rw [node106_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node107_check : node107 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2350703) entry_5_2) node106 := by decide +kernel

theorem node107_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node107 x = (((-2350703 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x + (((507536 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + ((-2149155 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x)) := by
  rw [node107_check, Integer.Sparse.eval_merge]
  rw [node106_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node108_check : node108 =
    Integer.Sparse.merge node105 node107 := by decide +kernel

theorem node108_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node108 x = ((((-1068497 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + ((-2156927 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x) + (((-2350703 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x + (((507536 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + ((-2149155 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x))) := by
  rw [node108_check, Integer.Sparse.eval_merge]
  rw [node105_eval, node107_eval]

theorem node109_check : node109 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4702242) entry_5_6) (Integer.Sparse.scale (354131) entry_5_7) := by decide +kernel

theorem node109_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node109 x = (((-4702242 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + ((354131 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x) := by
  rw [node109_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node110_check : node110 =
    Integer.Sparse.merge (Integer.Sparse.scale (2095556) entry_5_5) node109 := by decide +kernel

theorem node110_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node110 x = (((2095556 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x + (((-4702242 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + ((354131 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x)) := by
  rw [node110_check, Integer.Sparse.eval_merge]
  rw [node109_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node111_check : node111 =
    Integer.Sparse.merge (Integer.Sparse.scale (90661) entry_5_9) (Integer.Sparse.scale (-5369286) entry_5_10) := by decide +kernel

theorem node111_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node111 x = (((90661 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + ((-5369286 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x) := by
  rw [node111_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node112_check : node112 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3195150) entry_5_8) node111 := by decide +kernel

theorem node112_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node112 x = (((-3195150 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x + (((90661 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + ((-5369286 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x)) := by
  rw [node112_check, Integer.Sparse.eval_merge]
  rw [node111_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node113_check : node113 =
    Integer.Sparse.merge node110 node112 := by decide +kernel

theorem node113_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node113 x = ((((2095556 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x + (((-4702242 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + ((354131 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x)) + (((-3195150 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x + (((90661 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + ((-5369286 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x))) := by
  rw [node113_check, Integer.Sparse.eval_merge]
  rw [node110_eval, node112_eval]

theorem node114_check : node114 =
    Integer.Sparse.merge node108 node113 := by decide +kernel

theorem node114_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node114 x = (((((-1068497 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + ((-2156927 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x) + (((-2350703 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x + (((507536 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + ((-2149155 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x))) + ((((2095556 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x + (((-4702242 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + ((354131 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x)) + (((-3195150 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x + (((90661 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + ((-5369286 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x)))) := by
  rw [node114_check, Integer.Sparse.eval_merge]
  rw [node108_eval, node113_eval]

theorem node115_check : node115 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2205269) entry_5_11) (Integer.Sparse.scale (5002923) entry_5_12) := by decide +kernel

theorem node115_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node115 x = (((-2205269 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x + ((5002923 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_12 x) := by
  rw [node115_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node116_check : node116 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6415795) entry_5_14) (Integer.Sparse.scale (-6460067) entry_5_15) := by decide +kernel

theorem node116_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node116 x = (((-6415795 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_14 x + ((-6460067 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_15 x) := by
  rw [node116_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node117_check : node117 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1757350) entry_5_13) node116 := by decide +kernel

theorem node117_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node117 x = (((-1757350 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_13 x + (((-6415795 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_14 x + ((-6460067 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_15 x)) := by
  rw [node117_check, Integer.Sparse.eval_merge]
  rw [node116_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node118_check : node118 =
    Integer.Sparse.merge node115 node117 := by decide +kernel

theorem node118_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node118 x = ((((-2205269 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x + ((5002923 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_12 x) + (((-1757350 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_13 x + (((-6415795 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_14 x + ((-6460067 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_15 x))) := by
  rw [node118_check, Integer.Sparse.eval_merge]
  rw [node115_eval, node117_eval]

theorem node119_check : node119 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1444903) entry_5_17) (Integer.Sparse.scale (-396942) entry_5_18) := by decide +kernel

theorem node119_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node119 x = (((-1444903 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_17 x + ((-396942 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_18 x) := by
  rw [node119_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node120_check : node120 =
    Integer.Sparse.merge (Integer.Sparse.scale (6777335) entry_5_16) node119 := by decide +kernel

theorem node120_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node120 x = (((6777335 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_16 x + (((-1444903 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_17 x + ((-396942 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_18 x)) := by
  rw [node120_check, Integer.Sparse.eval_merge]
  rw [node119_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node121_check : node121 =
    Integer.Sparse.merge (Integer.Sparse.scale (-74307) entry_5_20) (Integer.Sparse.scale (-3345646) entry_5_21) := by decide +kernel

theorem node121_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node121 x = (((-74307 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_20 x + ((-3345646 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_21 x) := by
  rw [node121_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node122_check : node122 =
    Integer.Sparse.merge (Integer.Sparse.scale (65585) entry_5_19) node121 := by decide +kernel

theorem node122_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node122 x = (((65585 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_19 x + (((-74307 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_20 x + ((-3345646 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_21 x)) := by
  rw [node122_check, Integer.Sparse.eval_merge]
  rw [node121_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node123_check : node123 =
    Integer.Sparse.merge node120 node122 := by decide +kernel

theorem node123_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node123 x = ((((6777335 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_16 x + (((-1444903 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_17 x + ((-396942 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_18 x)) + (((65585 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_19 x + (((-74307 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_20 x + ((-3345646 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_21 x))) := by
  rw [node123_check, Integer.Sparse.eval_merge]
  rw [node120_eval, node122_eval]

theorem node124_check : node124 =
    Integer.Sparse.merge node118 node123 := by decide +kernel

theorem node124_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node124 x = (((((-2205269 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x + ((5002923 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_12 x) + (((-1757350 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_13 x + (((-6415795 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_14 x + ((-6460067 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_15 x))) + ((((6777335 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_16 x + (((-1444903 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_17 x + ((-396942 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_18 x)) + (((65585 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_19 x + (((-74307 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_20 x + ((-3345646 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_21 x)))) := by
  rw [node124_check, Integer.Sparse.eval_merge]
  rw [node118_eval, node123_eval]

theorem node125_check : node125 =
    Integer.Sparse.merge node114 node124 := by decide +kernel

theorem node125_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node125 x = ((((((-1068497 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + ((-2156927 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x) + (((-2350703 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x + (((507536 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + ((-2149155 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x))) + ((((2095556 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x + (((-4702242 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + ((354131 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x)) + (((-3195150 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x + (((90661 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + ((-5369286 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x)))) + (((((-2205269 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x + ((5002923 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_12 x) + (((-1757350 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_13 x + (((-6415795 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_14 x + ((-6460067 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_15 x))) + ((((6777335 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_16 x + (((-1444903 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_17 x + ((-396942 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_18 x)) + (((65585 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_19 x + (((-74307 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_20 x + ((-3345646 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_21 x))))) := by
  rw [node125_check, Integer.Sparse.eval_merge]
  rw [node114_eval, node124_eval]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node147_check : node147 =
    Integer.Sparse.merge (Integer.Sparse.scale (2283451) entry_7_0) (Integer.Sparse.scale (-394829) entry_7_1) := by decide +kernel

theorem node147_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node147 x = (((2283451 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + ((-394829 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x) := by
  rw [node147_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node148_check : node148 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2274383) entry_7_3) (Integer.Sparse.scale (2764593) entry_7_4) := by decide +kernel

theorem node148_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node148 x = (((-2274383 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + ((2764593 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x) := by
  rw [node148_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node149_check : node149 =
    Integer.Sparse.merge (Integer.Sparse.scale (1999663) entry_7_2) node148 := by decide +kernel

theorem node149_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node149 x = (((1999663 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x + (((-2274383 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + ((2764593 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x)) := by
  rw [node149_check, Integer.Sparse.eval_merge]
  rw [node148_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node150_check : node150 =
    Integer.Sparse.merge node147 node149 := by decide +kernel

theorem node150_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node150 x = ((((2283451 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + ((-394829 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x) + (((1999663 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x + (((-2274383 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + ((2764593 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x))) := by
  rw [node150_check, Integer.Sparse.eval_merge]
  rw [node147_eval, node149_eval]

theorem node151_check : node151 =
    Integer.Sparse.merge (Integer.Sparse.scale (-7277099) entry_7_6) (Integer.Sparse.scale (6526673) entry_7_7) := by decide +kernel

theorem node151_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node151 x = (((-7277099 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + ((6526673 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x) := by
  rw [node151_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node152_check : node152 =
    Integer.Sparse.merge (Integer.Sparse.scale (354131) entry_7_5) node151 := by decide +kernel

theorem node152_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node152 x = (((354131 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x + (((-7277099 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + ((6526673 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x)) := by
  rw [node152_check, Integer.Sparse.eval_merge]
  rw [node151_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node153_check : node153 =
    Integer.Sparse.merge (Integer.Sparse.scale (1533901) entry_7_9) (Integer.Sparse.scale (-160327) entry_7_10) := by decide +kernel

theorem node153_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node153 x = (((1533901 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((-160327 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x) := by
  rw [node153_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node154_check : node154 =
    Integer.Sparse.merge (Integer.Sparse.scale (-281) entry_7_8) node153 := by decide +kernel

theorem node154_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node154 x = (((-281 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x + (((1533901 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((-160327 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x)) := by
  rw [node154_check, Integer.Sparse.eval_merge]
  rw [node153_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node155_check : node155 =
    Integer.Sparse.merge node152 node154 := by decide +kernel

theorem node155_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node155 x = ((((354131 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x + (((-7277099 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + ((6526673 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x)) + (((-281 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x + (((1533901 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((-160327 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x))) := by
  rw [node155_check, Integer.Sparse.eval_merge]
  rw [node152_eval, node154_eval]

theorem node156_check : node156 =
    Integer.Sparse.merge node150 node155 := by decide +kernel

theorem node156_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node156 x = (((((2283451 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + ((-394829 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x) + (((1999663 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x + (((-2274383 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + ((2764593 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x))) + ((((354131 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x + (((-7277099 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + ((6526673 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x)) + (((-281 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x + (((1533901 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((-160327 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x)))) := by
  rw [node156_check, Integer.Sparse.eval_merge]
  rw [node150_eval, node155_eval]

theorem node157_check : node157 =
    Integer.Sparse.merge (Integer.Sparse.scale (1671992) entry_7_11) (Integer.Sparse.scale (-4900936) entry_7_12) := by decide +kernel

theorem node157_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node157 x = (((1671992 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x + ((-4900936 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x) := by
  rw [node157_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node158_check : node158 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4093860) entry_7_14) (Integer.Sparse.scale (4067062) entry_7_15) := by decide +kernel

theorem node158_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node158 x = (((-4093860 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x + ((4067062 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x) := by
  rw [node158_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node159_check : node159 =
    Integer.Sparse.merge (Integer.Sparse.scale (1492337) entry_7_13) node158 := by decide +kernel

theorem node159_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node159 x = (((1492337 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_13 x + (((-4093860 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x + ((4067062 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x)) := by
  rw [node159_check, Integer.Sparse.eval_merge]
  rw [node158_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node160_check : node160 =
    Integer.Sparse.merge node157 node159 := by decide +kernel

theorem node160_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node160 x = ((((1671992 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x + ((-4900936 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x) + (((1492337 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_13 x + (((-4093860 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x + ((4067062 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x))) := by
  rw [node160_check, Integer.Sparse.eval_merge]
  rw [node157_eval, node159_eval]

theorem node161_check : node161 =
    Integer.Sparse.merge (Integer.Sparse.scale (-917759) entry_7_17) (Integer.Sparse.scale (331917) entry_7_18) := by decide +kernel

theorem node161_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node161 x = (((-917759 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x) := by
  rw [node161_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node162_check : node162 =
    Integer.Sparse.merge (Integer.Sparse.scale (6927530) entry_7_16) node161 := by decide +kernel

theorem node162_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node162 x = (((6927530 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + (((-917759 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x)) := by
  rw [node162_check, Integer.Sparse.eval_merge]
  rw [node161_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node163_check : node163 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6691783) entry_7_20) (Integer.Sparse.scale (-8777026) entry_7_21) := by decide +kernel

theorem node163_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node163 x = (((-6691783 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x + ((-8777026 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_21 x) := by
  rw [node163_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node164_check : node164 =
    Integer.Sparse.merge (Integer.Sparse.scale (-100234) entry_7_19) node163 := by decide +kernel

theorem node164_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node164 x = (((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x + (((-6691783 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x + ((-8777026 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_21 x)) := by
  rw [node164_check, Integer.Sparse.eval_merge]
  rw [node163_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node165_check : node165 =
    Integer.Sparse.merge node162 node164 := by decide +kernel

theorem node165_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node165 x = ((((6927530 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + (((-917759 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x)) + (((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x + (((-6691783 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x + ((-8777026 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_21 x))) := by
  rw [node165_check, Integer.Sparse.eval_merge]
  rw [node162_eval, node164_eval]

theorem node166_check : node166 =
    Integer.Sparse.merge node160 node165 := by decide +kernel

theorem node166_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node166 x = (((((1671992 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x + ((-4900936 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x) + (((1492337 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_13 x + (((-4093860 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x + ((4067062 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x))) + ((((6927530 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + (((-917759 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x)) + (((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x + (((-6691783 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x + ((-8777026 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_21 x)))) := by
  rw [node166_check, Integer.Sparse.eval_merge]
  rw [node160_eval, node165_eval]

theorem node167_check : node167 =
    Integer.Sparse.merge node156 node166 := by decide +kernel

theorem node167_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node167 x = ((((((2283451 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + ((-394829 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x) + (((1999663 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x + (((-2274383 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + ((2764593 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x))) + ((((354131 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x + (((-7277099 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + ((6526673 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x)) + (((-281 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x + (((1533901 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((-160327 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x)))) + (((((1671992 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x + ((-4900936 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x) + (((1492337 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_13 x + (((-4093860 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x + ((4067062 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x))) + ((((6927530 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + (((-917759 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x)) + (((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x + (((-6691783 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x + ((-8777026 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_21 x))))) := by
  rw [node167_check, Integer.Sparse.eval_merge]
  rw [node156_eval, node166_eval]

theorem node168_check : node168 =
    Integer.Sparse.merge (Integer.Sparse.scale (5870760) entry_8_0) (Integer.Sparse.scale (5057136) entry_8_1) := by decide +kernel

theorem node168_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node168 x = (((5870760 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + ((5057136 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x) := by
  rw [node168_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node169_check : node169 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3889906) entry_8_3) (Integer.Sparse.scale (3803854) entry_8_4) := by decide +kernel

theorem node169_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node169 x = (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x) := by
  rw [node169_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node170_check : node170 =
    Integer.Sparse.merge (Integer.Sparse.scale (9422497) entry_8_2) node169 := by decide +kernel

theorem node170_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node170 x = (((9422497 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x + (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x)) := by
  rw [node170_check, Integer.Sparse.eval_merge]
  rw [node169_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node171_check : node171 =
    Integer.Sparse.merge node168 node170 := by decide +kernel

theorem node171_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node171 x = ((((5870760 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + ((5057136 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x) + (((9422497 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x + (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x))) := by
  rw [node171_check, Integer.Sparse.eval_merge]
  rw [node168_eval, node170_eval]

theorem node172_check : node172 =
    Integer.Sparse.merge (Integer.Sparse.scale (8611573) entry_8_6) (Integer.Sparse.scale (-281) entry_8_7) := by decide +kernel

theorem node172_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node172 x = (((8611573 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + ((-281 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x) := by
  rw [node172_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node173_check : node173 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3195150) entry_8_5) node172 := by decide +kernel

theorem node173_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node173 x = (((-3195150 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x + (((8611573 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + ((-281 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x)) := by
  rw [node173_check, Integer.Sparse.eval_merge]
  rw [node172_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node174_check : node174 =
    Integer.Sparse.merge (Integer.Sparse.scale (1309529) entry_8_9) (Integer.Sparse.scale (13559036) entry_8_10) := by decide +kernel

theorem node174_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node174 x = (((1309529 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((13559036 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x) := by
  rw [node174_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node175_check : node175 =
    Integer.Sparse.merge (Integer.Sparse.scale (15645334) entry_8_8) node174 := by decide +kernel

theorem node175_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node175 x = (((15645334 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x + (((1309529 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((13559036 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x)) := by
  rw [node175_check, Integer.Sparse.eval_merge]
  rw [node174_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node176_check : node176 =
    Integer.Sparse.merge node173 node175 := by decide +kernel

theorem node176_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node176 x = ((((-3195150 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x + (((8611573 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + ((-281 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x)) + (((15645334 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x + (((1309529 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((13559036 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x))) := by
  rw [node176_check, Integer.Sparse.eval_merge]
  rw [node173_eval, node175_eval]

theorem node177_check : node177 =
    Integer.Sparse.merge node171 node176 := by decide +kernel

theorem node177_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node177 x = (((((5870760 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + ((5057136 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x) + (((9422497 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x + (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x))) + ((((-3195150 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x + (((8611573 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + ((-281 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x)) + (((15645334 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x + (((1309529 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((13559036 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x)))) := by
  rw [node177_check, Integer.Sparse.eval_merge]
  rw [node171_eval, node176_eval]

theorem node178_check : node178 =
    Integer.Sparse.merge (Integer.Sparse.scale (5861827) entry_8_11) (Integer.Sparse.scale (-17607260) entry_8_12) := by decide +kernel

theorem node178_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node178 x = (((5861827 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x + ((-17607260 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x) := by
  rw [node178_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node179_check : node179 =
    Integer.Sparse.merge (Integer.Sparse.scale (21938238) entry_8_14) (Integer.Sparse.scale (11639620) entry_8_15) := by decide +kernel

theorem node179_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node179 x = (((21938238 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x + ((11639620 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x) := by
  rw [node179_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node180_check : node180 =
    Integer.Sparse.merge (Integer.Sparse.scale (2684271) entry_8_13) node179 := by decide +kernel

theorem node180_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node180 x = (((2684271 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + (((21938238 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x + ((11639620 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x)) := by
  rw [node180_check, Integer.Sparse.eval_merge]
  rw [node179_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node181_check : node181 =
    Integer.Sparse.merge node178 node180 := by decide +kernel

theorem node181_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node181 x = ((((5861827 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x + ((-17607260 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x) + (((2684271 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + (((21938238 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x + ((11639620 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x))) := by
  rw [node181_check, Integer.Sparse.eval_merge]
  rw [node178_eval, node180_eval]

theorem node182_check : node182 =
    Integer.Sparse.merge (Integer.Sparse.scale (2061355) entry_8_17) (Integer.Sparse.scale (52682) entry_8_18) := by decide +kernel

theorem node182_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node182 x = (((2061355 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x + ((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x) := by
  rw [node182_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node183_check : node183 =
    Integer.Sparse.merge (Integer.Sparse.scale (-17209683) entry_8_16) node182 := by decide +kernel

theorem node183_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node183 x = (((-17209683 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + (((2061355 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x + ((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x)) := by
  rw [node183_check, Integer.Sparse.eval_merge]
  rw [node182_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node184_check : node184 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2279851) entry_8_20) (Integer.Sparse.scale (2493568) entry_8_21) := by decide +kernel

theorem node184_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node184 x = (((-2279851 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x + ((2493568 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_21 x) := by
  rw [node184_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node185_check : node185 =
    Integer.Sparse.merge (Integer.Sparse.scale (294656) entry_8_19) node184 := by decide +kernel

theorem node185_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node185 x = (((294656 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x + (((-2279851 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x + ((2493568 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_21 x)) := by
  rw [node185_check, Integer.Sparse.eval_merge]
  rw [node184_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node186_check : node186 =
    Integer.Sparse.merge node183 node185 := by decide +kernel

theorem node186_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node186 x = ((((-17209683 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + (((2061355 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x + ((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x)) + (((294656 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x + (((-2279851 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x + ((2493568 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_21 x))) := by
  rw [node186_check, Integer.Sparse.eval_merge]
  rw [node183_eval, node185_eval]

theorem node187_check : node187 =
    Integer.Sparse.merge node181 node186 := by decide +kernel

theorem node187_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node187 x = (((((5861827 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x + ((-17607260 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x) + (((2684271 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + (((21938238 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x + ((11639620 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x))) + ((((-17209683 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + (((2061355 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x + ((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x)) + (((294656 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x + (((-2279851 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x + ((2493568 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_21 x)))) := by
  rw [node187_check, Integer.Sparse.eval_merge]
  rw [node181_eval, node186_eval]

theorem node188_check : node188 =
    Integer.Sparse.merge node177 node187 := by decide +kernel

theorem node188_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node188 x = ((((((5870760 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + ((5057136 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x) + (((9422497 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x + (((-3889906 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((3803854 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x))) + ((((-3195150 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x + (((8611573 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + ((-281 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x)) + (((15645334 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x + (((1309529 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((13559036 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x)))) + (((((5861827 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x + ((-17607260 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x) + (((2684271 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + (((21938238 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x + ((11639620 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x))) + ((((-17209683 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + (((2061355 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x + ((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x)) + (((294656 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x + (((-2279851 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x + ((2493568 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_21 x))))) := by
  rw [node188_check, Integer.Sparse.eval_merge]
  rw [node177_eval, node187_eval]

theorem node189_check : node189 =
    Integer.Sparse.merge (Integer.Sparse.scale (5122348) entry_9_0) (Integer.Sparse.scale (-292814) entry_9_1) := by decide +kernel

theorem node189_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node189 x = (((5122348 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + ((-292814 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x) := by
  rw [node189_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node190_check : node190 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2349413) entry_9_3) (Integer.Sparse.scale (-683505) entry_9_4) := by decide +kernel

theorem node190_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node190 x = (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + ((-683505 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x) := by
  rw [node190_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node191_check : node191 =
    Integer.Sparse.merge (Integer.Sparse.scale (1200964) entry_9_2) node190 := by decide +kernel

theorem node191_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node191 x = (((1200964 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x + (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + ((-683505 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x)) := by
  rw [node191_check, Integer.Sparse.eval_merge]
  rw [node190_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node192_check : node192 =
    Integer.Sparse.merge node189 node191 := by decide +kernel

theorem node192_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node192 x = ((((5122348 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + ((-292814 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x) + (((1200964 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x + (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + ((-683505 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x))) := by
  rw [node192_check, Integer.Sparse.eval_merge]
  rw [node189_eval, node191_eval]

theorem node193_check : node193 =
    Integer.Sparse.merge (Integer.Sparse.scale (-158959) entry_9_6) (Integer.Sparse.scale (1533901) entry_9_7) := by decide +kernel

theorem node193_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node193 x = (((-158959 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + ((1533901 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x) := by
  rw [node193_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node194_check : node194 =
    Integer.Sparse.merge (Integer.Sparse.scale (90661) entry_9_5) node193 := by decide +kernel

theorem node194_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node194 x = (((90661 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x + (((-158959 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + ((1533901 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x)) := by
  rw [node194_check, Integer.Sparse.eval_merge]
  rw [node193_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node195_check : node195 =
    Integer.Sparse.merge (Integer.Sparse.scale (3394404) entry_9_9) (Integer.Sparse.scale (3491225) entry_9_10) := by decide +kernel

theorem node195_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node195 x = (((3394404 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + ((3491225 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x) := by
  rw [node195_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node196_check : node196 =
    Integer.Sparse.merge (Integer.Sparse.scale (1309529) entry_9_8) node195 := by decide +kernel

theorem node196_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node196 x = (((1309529 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x + (((3394404 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + ((3491225 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x)) := by
  rw [node196_check, Integer.Sparse.eval_merge]
  rw [node195_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node197_check : node197 =
    Integer.Sparse.merge node194 node196 := by decide +kernel

theorem node197_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node197 x = ((((90661 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x + (((-158959 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + ((1533901 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x)) + (((1309529 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x + (((3394404 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + ((3491225 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x))) := by
  rw [node197_check, Integer.Sparse.eval_merge]
  rw [node194_eval, node196_eval]

theorem node198_check : node198 =
    Integer.Sparse.merge node192 node197 := by decide +kernel

theorem node198_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node198 x = (((((5122348 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + ((-292814 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x) + (((1200964 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x + (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + ((-683505 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x))) + ((((90661 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x + (((-158959 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + ((1533901 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x)) + (((1309529 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x + (((3394404 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + ((3491225 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x)))) := by
  rw [node198_check, Integer.Sparse.eval_merge]
  rw [node192_eval, node197_eval]

theorem node199_check : node199 =
    Integer.Sparse.merge (Integer.Sparse.scale (854563) entry_9_11) (Integer.Sparse.scale (-1013940) entry_9_12) := by decide +kernel

theorem node199_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node199 x = (((854563 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x + ((-1013940 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_12 x) := by
  rw [node199_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node200_check : node200 =
    Integer.Sparse.merge (Integer.Sparse.scale (2839721) entry_9_14) (Integer.Sparse.scale (-5240018) entry_9_15) := by decide +kernel

theorem node200_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node200 x = (((2839721 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_14 x + ((-5240018 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_15 x) := by
  rw [node200_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node201_check : node201 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1050249) entry_9_13) node200 := by decide +kernel

theorem node201_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node201 x = (((-1050249 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_13 x + (((2839721 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_14 x + ((-5240018 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_15 x)) := by
  rw [node201_check, Integer.Sparse.eval_merge]
  rw [node200_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node202_check : node202 =
    Integer.Sparse.merge node199 node201 := by decide +kernel

theorem node202_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node202 x = ((((854563 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x + ((-1013940 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_12 x) + (((-1050249 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_13 x + (((2839721 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_14 x + ((-5240018 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_15 x))) := by
  rw [node202_check, Integer.Sparse.eval_merge]
  rw [node199_eval, node201_eval]

theorem node203_check : node203 =
    Integer.Sparse.merge (Integer.Sparse.scale (-457001) entry_9_17) (Integer.Sparse.scale (-2183598) entry_9_18) := by decide +kernel

theorem node203_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node203 x = (((-457001 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_17 x + ((-2183598 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_18 x) := by
  rw [node203_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node204_check : node204 =
    Integer.Sparse.merge (Integer.Sparse.scale (8303639) entry_9_16) node203 := by decide +kernel

theorem node204_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node204 x = (((8303639 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_16 x + (((-457001 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_17 x + ((-2183598 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_18 x)) := by
  rw [node204_check, Integer.Sparse.eval_merge]
  rw [node203_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node205_check : node205 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4392796) entry_9_20) (Integer.Sparse.scale (-11111890) entry_9_21) := by decide +kernel

theorem node205_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node205 x = (((-4392796 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_20 x + ((-11111890 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_21 x) := by
  rw [node205_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node206_check : node206 =
    Integer.Sparse.merge (Integer.Sparse.scale (-290864) entry_9_19) node205 := by decide +kernel

theorem node206_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node206 x = (((-290864 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_19 x + (((-4392796 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_20 x + ((-11111890 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_21 x)) := by
  rw [node206_check, Integer.Sparse.eval_merge]
  rw [node205_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node207_check : node207 =
    Integer.Sparse.merge node204 node206 := by decide +kernel

theorem node207_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node207 x = ((((8303639 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_16 x + (((-457001 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_17 x + ((-2183598 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_18 x)) + (((-290864 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_19 x + (((-4392796 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_20 x + ((-11111890 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_21 x))) := by
  rw [node207_check, Integer.Sparse.eval_merge]
  rw [node204_eval, node206_eval]

theorem node208_check : node208 =
    Integer.Sparse.merge node202 node207 := by decide +kernel

theorem node208_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node208 x = (((((854563 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x + ((-1013940 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_12 x) + (((-1050249 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_13 x + (((2839721 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_14 x + ((-5240018 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_15 x))) + ((((8303639 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_16 x + (((-457001 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_17 x + ((-2183598 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_18 x)) + (((-290864 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_19 x + (((-4392796 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_20 x + ((-11111890 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_21 x)))) := by
  rw [node208_check, Integer.Sparse.eval_merge]
  rw [node202_eval, node207_eval]

theorem node209_check : node209 =
    Integer.Sparse.merge node198 node208 := by decide +kernel

theorem node209_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node209 x = ((((((5122348 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + ((-292814 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x) + (((1200964 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x + (((-2349413 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + ((-683505 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x))) + ((((90661 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x + (((-158959 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + ((1533901 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x)) + (((1309529 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x + (((3394404 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + ((3491225 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x)))) + (((((854563 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x + ((-1013940 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_12 x) + (((-1050249 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_13 x + (((2839721 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_14 x + ((-5240018 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_15 x))) + ((((8303639 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_16 x + (((-457001 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_17 x + ((-2183598 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_18 x)) + (((-290864 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_19 x + (((-4392796 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_20 x + ((-11111890 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_21 x))))) := by
  rw [node209_check, Integer.Sparse.eval_merge]
  rw [node198_eval, node208_eval]

theorem node210_check : node210 =
    Integer.Sparse.merge (Integer.Sparse.scale (11944156) entry_10_0) (Integer.Sparse.scale (8387639) entry_10_1) := by decide +kernel

theorem node210_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node210 x = (((11944156 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + ((8387639 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x) := by
  rw [node210_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node211_check : node211 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3559336) entry_10_3) (Integer.Sparse.scale (5967631) entry_10_4) := by decide +kernel

theorem node211_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node211 x = (((-3559336 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + ((5967631 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x) := by
  rw [node211_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node212_check : node212 =
    Integer.Sparse.merge (Integer.Sparse.scale (9488222) entry_10_2) node211 := by decide +kernel

theorem node212_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node212 x = (((9488222 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x + (((-3559336 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + ((5967631 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x)) := by
  rw [node212_check, Integer.Sparse.eval_merge]
  rw [node211_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node213_check : node213 =
    Integer.Sparse.merge node210 node212 := by decide +kernel

theorem node213_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node213 x = ((((11944156 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + ((8387639 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x) + (((9488222 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x + (((-3559336 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + ((5967631 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x))) := by
  rw [node213_check, Integer.Sparse.eval_merge]
  rw [node210_eval, node212_eval]

theorem node214_check : node214 =
    Integer.Sparse.merge (Integer.Sparse.scale (32218355) entry_10_6) (Integer.Sparse.scale (-160327) entry_10_7) := by decide +kernel

theorem node214_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node214 x = (((32218355 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + ((-160327 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x) := by
  rw [node214_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node215_check : node215 =
    Integer.Sparse.merge (Integer.Sparse.scale (-5369286) entry_10_5) node214 := by decide +kernel

theorem node215_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node215 x = (((-5369286 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x + (((32218355 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + ((-160327 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x)) := by
  rw [node215_check, Integer.Sparse.eval_merge]
  rw [node214_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node216_check : node216 =
    Integer.Sparse.merge (Integer.Sparse.scale (3491225) entry_10_9) (Integer.Sparse.scale (44787203) entry_10_10) := by decide +kernel

theorem node216_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node216 x = (((3491225 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + ((44787203 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x) := by
  rw [node216_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node217_check : node217 =
    Integer.Sparse.merge (Integer.Sparse.scale (13559036) entry_10_8) node216 := by decide +kernel

theorem node217_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node217 x = (((13559036 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x + (((3491225 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + ((44787203 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x)) := by
  rw [node217_check, Integer.Sparse.eval_merge]
  rw [node216_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node218_check : node218 =
    Integer.Sparse.merge node215 node217 := by decide +kernel

theorem node218_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node218 x = ((((-5369286 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x + (((32218355 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + ((-160327 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x)) + (((13559036 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x + (((3491225 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + ((44787203 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x))) := by
  rw [node218_check, Integer.Sparse.eval_merge]
  rw [node215_eval, node217_eval]

theorem node219_check : node219 =
    Integer.Sparse.merge node213 node218 := by decide +kernel

theorem node219_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node219 x = (((((11944156 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + ((8387639 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x) + (((9488222 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x + (((-3559336 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + ((5967631 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x))) + ((((-5369286 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x + (((32218355 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + ((-160327 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x)) + (((13559036 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x + (((3491225 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + ((44787203 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x)))) := by
  rw [node219_check, Integer.Sparse.eval_merge]
  rw [node213_eval, node218_eval]

theorem node220_check : node220 =
    Integer.Sparse.merge (Integer.Sparse.scale (11712236) entry_10_11) (Integer.Sparse.scale (-18233209) entry_10_12) := by decide +kernel

theorem node220_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node220 x = (((11712236 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x + ((-18233209 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_12 x) := by
  rw [node220_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node221_check : node221 =
    Integer.Sparse.merge (Integer.Sparse.scale (40989979) entry_10_14) (Integer.Sparse.scale (22667693) entry_10_15) := by decide +kernel

theorem node221_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node221 x = (((40989979 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_14 x + ((22667693 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_15 x) := by
  rw [node221_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node222_check : node222 =
    Integer.Sparse.merge (Integer.Sparse.scale (11108282) entry_10_13) node221 := by decide +kernel

theorem node222_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node222 x = (((11108282 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_13 x + (((40989979 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_14 x + ((22667693 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_15 x)) := by
  rw [node222_check, Integer.Sparse.eval_merge]
  rw [node221_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node223_check : node223 =
    Integer.Sparse.merge node220 node222 := by decide +kernel

theorem node223_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node223 x = ((((11712236 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x + ((-18233209 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_12 x) + (((11108282 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_13 x + (((40989979 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_14 x + ((22667693 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_15 x))) := by
  rw [node223_check, Integer.Sparse.eval_merge]
  rw [node220_eval, node222_eval]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node224_check : node224 =
    Integer.Sparse.merge (Integer.Sparse.scale (5024836) entry_10_17) (Integer.Sparse.scale (-2050110) entry_10_18) := by decide +kernel

theorem node224_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node224 x = (((5024836 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_17 x + ((-2050110 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_18 x) := by
  rw [node224_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node225_check : node225 =
    Integer.Sparse.merge (Integer.Sparse.scale (-18516868) entry_10_16) node224 := by decide +kernel

theorem node225_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node225 x = (((-18516868 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_16 x + (((5024836 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_17 x + ((-2050110 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_18 x)) := by
  rw [node225_check, Integer.Sparse.eval_merge]
  rw [node224_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node226_check : node226 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2671294) entry_10_20) (Integer.Sparse.scale (2653116) entry_10_21) := by decide +kernel

theorem node226_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node226 x = (((-2671294 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_20 x + ((2653116 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_21 x) := by
  rw [node226_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node227_check : node227 =
    Integer.Sparse.merge (Integer.Sparse.scale (-579570) entry_10_19) node226 := by decide +kernel

theorem node227_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node227 x = (((-579570 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_19 x + (((-2671294 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_20 x + ((2653116 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_21 x)) := by
  rw [node227_check, Integer.Sparse.eval_merge]
  rw [node226_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node228_check : node228 =
    Integer.Sparse.merge node225 node227 := by decide +kernel

theorem node228_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node228 x = ((((-18516868 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_16 x + (((5024836 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_17 x + ((-2050110 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_18 x)) + (((-579570 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_19 x + (((-2671294 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_20 x + ((2653116 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_21 x))) := by
  rw [node228_check, Integer.Sparse.eval_merge]
  rw [node225_eval, node227_eval]

theorem node229_check : node229 =
    Integer.Sparse.merge node223 node228 := by decide +kernel

theorem node229_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node229 x = (((((11712236 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x + ((-18233209 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_12 x) + (((11108282 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_13 x + (((40989979 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_14 x + ((22667693 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_15 x))) + ((((-18516868 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_16 x + (((5024836 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_17 x + ((-2050110 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_18 x)) + (((-579570 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_19 x + (((-2671294 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_20 x + ((2653116 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_21 x)))) := by
  rw [node229_check, Integer.Sparse.eval_merge]
  rw [node223_eval, node228_eval]

theorem node230_check : node230 =
    Integer.Sparse.merge node219 node229 := by decide +kernel

theorem node230_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node230 x = ((((((11944156 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + ((8387639 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x) + (((9488222 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x + (((-3559336 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + ((5967631 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x))) + ((((-5369286 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x + (((32218355 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + ((-160327 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x)) + (((13559036 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x + (((3491225 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + ((44787203 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x)))) + (((((11712236 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x + ((-18233209 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_12 x) + (((11108282 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_13 x + (((40989979 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_14 x + ((22667693 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_15 x))) + ((((-18516868 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_16 x + (((5024836 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_17 x + ((-2050110 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_18 x)) + (((-579570 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_19 x + (((-2671294 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_20 x + ((2653116 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_21 x))))) := by
  rw [node230_check, Integer.Sparse.eval_merge]
  rw [node219_eval, node229_eval]

theorem node231_check : node231 =
    Integer.Sparse.merge (Integer.Sparse.scale (4278803) entry_11_0) (Integer.Sparse.scale (3154912) entry_11_1) := by decide +kernel

theorem node231_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node231 x = (((4278803 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + ((3154912 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x) := by
  rw [node231_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node232_check : node232 =
    Integer.Sparse.merge (Integer.Sparse.scale (112700) entry_11_3) (Integer.Sparse.scale (3481743) entry_11_4) := by decide +kernel

theorem node232_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node232 x = (((112700 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + ((3481743 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x) := by
  rw [node232_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node233_check : node233 =
    Integer.Sparse.merge (Integer.Sparse.scale (3809106) entry_11_2) node232 := by decide +kernel

theorem node233_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node233 x = (((3809106 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x + (((112700 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + ((3481743 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x)) := by
  rw [node233_check, Integer.Sparse.eval_merge]
  rw [node232_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node234_check : node234 =
    Integer.Sparse.merge node231 node233 := by decide +kernel

theorem node234_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node234 x = ((((4278803 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + ((3154912 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x) + (((3809106 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x + (((112700 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + ((3481743 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x))) := by
  rw [node234_check, Integer.Sparse.eval_merge]
  rw [node231_eval, node233_eval]

theorem node235_check : node235 =
    Integer.Sparse.merge (Integer.Sparse.scale (4328739) entry_11_6) (Integer.Sparse.scale (1671992) entry_11_7) := by decide +kernel

theorem node235_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node235 x = (((4328739 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + ((1671992 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x) := by
  rw [node235_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node236_check : node236 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2205269) entry_11_5) node235 := by decide +kernel

theorem node236_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node236 x = (((-2205269 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x + (((4328739 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + ((1671992 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x)) := by
  rw [node236_check, Integer.Sparse.eval_merge]
  rw [node235_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node237_check : node237 =
    Integer.Sparse.merge (Integer.Sparse.scale (854563) entry_11_9) (Integer.Sparse.scale (11712236) entry_11_10) := by decide +kernel

theorem node237_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node237 x = (((854563 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + ((11712236 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x) := by
  rw [node237_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node238_check : node238 =
    Integer.Sparse.merge (Integer.Sparse.scale (5861827) entry_11_8) node237 := by decide +kernel

theorem node238_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node238 x = (((5861827 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x + (((854563 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + ((11712236 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x)) := by
  rw [node238_check, Integer.Sparse.eval_merge]
  rw [node237_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node239_check : node239 =
    Integer.Sparse.merge node236 node238 := by decide +kernel

theorem node239_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node239 x = ((((-2205269 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x + (((4328739 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + ((1671992 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x)) + (((5861827 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x + (((854563 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + ((11712236 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x))) := by
  rw [node239_check, Integer.Sparse.eval_merge]
  rw [node236_eval, node238_eval]

theorem node240_check : node240 =
    Integer.Sparse.merge node234 node239 := by decide +kernel

theorem node240_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node240 x = (((((4278803 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + ((3154912 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x) + (((3809106 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x + (((112700 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + ((3481743 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x))) + ((((-2205269 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x + (((4328739 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + ((1671992 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x)) + (((5861827 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x + (((854563 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + ((11712236 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x)))) := by
  rw [node240_check, Integer.Sparse.eval_merge]
  rw [node234_eval, node239_eval]

theorem node241_check : node241 =
    Integer.Sparse.merge (Integer.Sparse.scale (7193374) entry_11_11) (Integer.Sparse.scale (-8643946) entry_11_12) := by decide +kernel

theorem node241_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node241 x = (((7193374 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x + ((-8643946 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x) := by
  rw [node241_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node242_check : node242 =
    Integer.Sparse.merge (Integer.Sparse.scale (9853406) entry_11_14) (Integer.Sparse.scale (7247397) entry_11_15) := by decide +kernel

theorem node242_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node242 x = (((9853406 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x + ((7247397 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x) := by
  rw [node242_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node243_check : node243 =
    Integer.Sparse.merge (Integer.Sparse.scale (4853940) entry_11_13) node242 := by decide +kernel

theorem node243_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node243 x = (((4853940 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + (((9853406 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x + ((7247397 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x)) := by
  rw [node243_check, Integer.Sparse.eval_merge]
  rw [node242_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node244_check : node244 =
    Integer.Sparse.merge node241 node243 := by decide +kernel

theorem node244_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node244 x = ((((7193374 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x + ((-8643946 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x) + (((4853940 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + (((9853406 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x + ((7247397 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x))) := by
  rw [node244_check, Integer.Sparse.eval_merge]
  rw [node241_eval, node243_eval]

theorem node245_check : node245 =
    Integer.Sparse.merge (Integer.Sparse.scale (1622012) entry_11_17) (Integer.Sparse.scale (505346) entry_11_18) := by decide +kernel

theorem node245_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node245 x = (((1622012 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x + ((505346 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x) := by
  rw [node245_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node246_check : node246 =
    Integer.Sparse.merge (Integer.Sparse.scale (-7480837) entry_11_16) node245 := by decide +kernel

theorem node246_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node246 x = (((-7480837 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + (((1622012 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x + ((505346 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x)) := by
  rw [node246_check, Integer.Sparse.eval_merge]
  rw [node245_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node247_check : node247 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3651298) entry_11_20) (Integer.Sparse.scale (787079) entry_11_21) := by decide +kernel

theorem node247_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node247 x = (((-3651298 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x + ((787079 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_21 x) := by
  rw [node247_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node248_check : node248 =
    Integer.Sparse.merge (Integer.Sparse.scale (410918) entry_11_19) node247 := by decide +kernel

theorem node248_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node248 x = (((410918 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x + (((-3651298 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x + ((787079 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_21 x)) := by
  rw [node248_check, Integer.Sparse.eval_merge]
  rw [node247_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node249_check : node249 =
    Integer.Sparse.merge node246 node248 := by decide +kernel

theorem node249_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node249 x = ((((-7480837 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + (((1622012 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x + ((505346 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x)) + (((410918 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x + (((-3651298 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x + ((787079 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_21 x))) := by
  rw [node249_check, Integer.Sparse.eval_merge]
  rw [node246_eval, node248_eval]

theorem node250_check : node250 =
    Integer.Sparse.merge node244 node249 := by decide +kernel

theorem node250_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node250 x = (((((7193374 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x + ((-8643946 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x) + (((4853940 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + (((9853406 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x + ((7247397 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x))) + ((((-7480837 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + (((1622012 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x + ((505346 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x)) + (((410918 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x + (((-3651298 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x + ((787079 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_21 x)))) := by
  rw [node250_check, Integer.Sparse.eval_merge]
  rw [node244_eval, node249_eval]

theorem node251_check : node251 =
    Integer.Sparse.merge node240 node250 := by decide +kernel

theorem node251_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node251 x = ((((((4278803 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + ((3154912 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x) + (((3809106 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x + (((112700 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + ((3481743 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x))) + ((((-2205269 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x + (((4328739 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + ((1671992 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x)) + (((5861827 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x + (((854563 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + ((11712236 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x)))) + (((((7193374 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x + ((-8643946 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x) + (((4853940 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + (((9853406 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x + ((7247397 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x))) + ((((-7480837 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + (((1622012 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x + ((505346 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x)) + (((410918 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x + (((-3651298 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x + ((787079 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_21 x))))) := by
  rw [node251_check, Integer.Sparse.eval_merge]
  rw [node240_eval, node250_eval]

theorem node252_check : node252 =
    Integer.Sparse.merge (Integer.Sparse.scale (-12939117) entry_12_0) (Integer.Sparse.scale (-8313712) entry_12_1) := by decide +kernel

theorem node252_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node252 x = (((-12939117 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_0 x + ((-8313712 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_1 x) := by
  rw [node252_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node253_check : node253 =
    Integer.Sparse.merge (Integer.Sparse.scale (12695356) entry_12_3) (Integer.Sparse.scale (-11947838) entry_12_4) := by decide +kernel

theorem node253_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node253 x = (((12695356 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_3 x + ((-11947838 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x) := by
  rw [node253_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node254_check : node254 =
    Integer.Sparse.merge (Integer.Sparse.scale (-16699012) entry_12_2) node253 := by decide +kernel

theorem node254_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node254 x = (((-16699012 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_2 x + (((12695356 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_3 x + ((-11947838 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x)) := by
  rw [node254_check, Integer.Sparse.eval_merge]
  rw [node253_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node255_check : node255 =
    Integer.Sparse.merge node252 node254 := by decide +kernel

theorem node255_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node255 x = ((((-12939117 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_0 x + ((-8313712 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_1 x) + (((-16699012 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_2 x + (((12695356 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_3 x + ((-11947838 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x))) := by
  rw [node255_check, Integer.Sparse.eval_merge]
  rw [node252_eval, node254_eval]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node256_check : node256 =
    Integer.Sparse.merge (Integer.Sparse.scale (-12463162) entry_12_6) (Integer.Sparse.scale (-4900936) entry_12_7) := by decide +kernel

theorem node256_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node256 x = (((-12463162 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_6 x + ((-4900936 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_7 x) := by
  rw [node256_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node257_check : node257 =
    Integer.Sparse.merge (Integer.Sparse.scale (5002923) entry_12_5) node256 := by decide +kernel

theorem node257_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node257 x = (((5002923 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_5 x + (((-12463162 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_6 x + ((-4900936 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_7 x)) := by
  rw [node257_check, Integer.Sparse.eval_merge]
  rw [node256_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node258_check : node258 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1013940) entry_12_9) (Integer.Sparse.scale (-18233209) entry_12_10) := by decide +kernel

theorem node258_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node258 x = (((-1013940 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_9 x + ((-18233209 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_10 x) := by
  rw [node258_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node259_check : node259 =
    Integer.Sparse.merge (Integer.Sparse.scale (-17607260) entry_12_8) node258 := by decide +kernel

theorem node259_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node259 x = (((-17607260 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_8 x + (((-1013940 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_9 x + ((-18233209 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_10 x)) := by
  rw [node259_check, Integer.Sparse.eval_merge]
  rw [node258_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node260_check : node260 =
    Integer.Sparse.merge node257 node259 := by decide +kernel

theorem node260_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node260 x = ((((5002923 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_5 x + (((-12463162 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_6 x + ((-4900936 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_7 x)) + (((-17607260 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_8 x + (((-1013940 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_9 x + ((-18233209 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_10 x))) := by
  rw [node260_check, Integer.Sparse.eval_merge]
  rw [node257_eval, node259_eval]

theorem node261_check : node261 =
    Integer.Sparse.merge node255 node260 := by decide +kernel

theorem node261_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node261 x = (((((-12939117 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_0 x + ((-8313712 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_1 x) + (((-16699012 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_2 x + (((12695356 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_3 x + ((-11947838 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x))) + ((((5002923 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_5 x + (((-12463162 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_6 x + ((-4900936 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_7 x)) + (((-17607260 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_8 x + (((-1013940 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_9 x + ((-18233209 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_10 x)))) := by
  rw [node261_check, Integer.Sparse.eval_merge]
  rw [node255_eval, node260_eval]

theorem node262_check : node262 =
    Integer.Sparse.merge (Integer.Sparse.scale (-8643946) entry_12_11) (Integer.Sparse.scale (39243904) entry_12_12) := by decide +kernel

theorem node262_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node262 x = (((-8643946 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_11 x + ((39243904 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_12 x) := by
  rw [node262_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node263_check : node263 =
    Integer.Sparse.merge (Integer.Sparse.scale (-28830365) entry_12_14) (Integer.Sparse.scale (-39888927) entry_12_15) := by decide +kernel

theorem node263_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node263 x = (((-28830365 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_14 x + ((-39888927 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_15 x) := by
  rw [node263_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node264_check : node264 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2209331) entry_12_13) node263 := by decide +kernel

theorem node264_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node264 x = (((-2209331 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_13 x + (((-28830365 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_14 x + ((-39888927 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_15 x)) := by
  rw [node264_check, Integer.Sparse.eval_merge]
  rw [node263_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node265_check : node265 =
    Integer.Sparse.merge node262 node264 := by decide +kernel

theorem node265_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node265 x = ((((-8643946 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_11 x + ((39243904 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_12 x) + (((-2209331 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_13 x + (((-28830365 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_14 x + ((-39888927 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_15 x))) := by
  rw [node265_check, Integer.Sparse.eval_merge]
  rw [node262_eval, node264_eval]

theorem node266_check : node266 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2442740) entry_12_17) (Integer.Sparse.scale (-4212976) entry_12_18) := by decide +kernel

theorem node266_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node266 x = (((-2442740 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_17 x + ((-4212976 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_18 x) := by
  rw [node266_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node267_check : node267 =
    Integer.Sparse.merge (Integer.Sparse.scale (26441031) entry_12_16) node266 := by decide +kernel

theorem node267_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node267 x = (((26441031 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_16 x + (((-2442740 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_17 x + ((-4212976 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_18 x)) := by
  rw [node267_check, Integer.Sparse.eval_merge]
  rw [node266_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node268_check : node268 =
    Integer.Sparse.merge (Integer.Sparse.scale (6351203) entry_12_20) (Integer.Sparse.scale (-3952727) entry_12_21) := by decide +kernel

theorem node268_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node268 x = (((6351203 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_20 x + ((-3952727 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_21 x) := by
  rw [node268_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node269_check : node269 =
    Integer.Sparse.merge (Integer.Sparse.scale (-270161) entry_12_19) node268 := by decide +kernel

theorem node269_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node269 x = (((-270161 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_19 x + (((6351203 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_20 x + ((-3952727 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_21 x)) := by
  rw [node269_check, Integer.Sparse.eval_merge]
  rw [node268_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node270_check : node270 =
    Integer.Sparse.merge node267 node269 := by decide +kernel

theorem node270_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node270 x = ((((26441031 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_16 x + (((-2442740 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_17 x + ((-4212976 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_18 x)) + (((-270161 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_19 x + (((6351203 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_20 x + ((-3952727 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_21 x))) := by
  rw [node270_check, Integer.Sparse.eval_merge]
  rw [node267_eval, node269_eval]

theorem node271_check : node271 =
    Integer.Sparse.merge node265 node270 := by decide +kernel

theorem node271_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node271 x = (((((-8643946 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_11 x + ((39243904 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_12 x) + (((-2209331 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_13 x + (((-28830365 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_14 x + ((-39888927 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_15 x))) + ((((26441031 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_16 x + (((-2442740 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_17 x + ((-4212976 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_18 x)) + (((-270161 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_19 x + (((6351203 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_20 x + ((-3952727 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_21 x)))) := by
  rw [node271_check, Integer.Sparse.eval_merge]
  rw [node265_eval, node270_eval]

theorem node272_check : node272 =
    Integer.Sparse.merge node261 node271 := by decide +kernel

theorem node272_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node272 x = ((((((-12939117 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_0 x + ((-8313712 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_1 x) + (((-16699012 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_2 x + (((12695356 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_3 x + ((-11947838 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x))) + ((((5002923 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_5 x + (((-12463162 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_6 x + ((-4900936 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_7 x)) + (((-17607260 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_8 x + (((-1013940 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_9 x + ((-18233209 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_10 x)))) + (((((-8643946 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_11 x + ((39243904 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_12 x) + (((-2209331 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_13 x + (((-28830365 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_14 x + ((-39888927 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_15 x))) + ((((26441031 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_16 x + (((-2442740 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_17 x + ((-4212976 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_18 x)) + (((-270161 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_19 x + (((6351203 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_20 x + ((-3952727 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_21 x))))) := by
  rw [node272_check, Integer.Sparse.eval_merge]
  rw [node261_eval, node271_eval]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node315_check : node315 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1896215) entry_15_0) (Integer.Sparse.scale (10377904) entry_15_1) := by decide +kernel

theorem node315_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node315 x = (((-1896215 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_0 x + ((10377904 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_1 x) := by
  rw [node315_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node316_check : node316 =
    Integer.Sparse.merge (Integer.Sparse.scale (-14511117) entry_15_3) (Integer.Sparse.scale (22116163) entry_15_4) := by decide +kernel

theorem node316_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node316 x = (((-14511117 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_3 x + ((22116163 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_4 x) := by
  rw [node316_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node317_check : node317 =
    Integer.Sparse.merge (Integer.Sparse.scale (16606019) entry_15_2) node316 := by decide +kernel

theorem node317_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node317 x = (((16606019 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_2 x + (((-14511117 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_3 x + ((22116163 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_4 x)) := by
  rw [node317_check, Integer.Sparse.eval_merge]
  rw [node316_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node318_check : node318 =
    Integer.Sparse.merge node315 node317 := by decide +kernel

theorem node318_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node318 x = ((((-1896215 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_0 x + ((10377904 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_1 x) + (((16606019 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_2 x + (((-14511117 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_3 x + ((22116163 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_4 x))) := by
  rw [node318_check, Integer.Sparse.eval_merge]
  rw [node315_eval, node317_eval]

theorem node319_check : node319 =
    Integer.Sparse.merge (Integer.Sparse.scale (30525040) entry_15_6) (Integer.Sparse.scale (4067062) entry_15_7) := by decide +kernel

theorem node319_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node319 x = (((30525040 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_6 x + ((4067062 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_7 x) := by
  rw [node319_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node320_check : node320 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6460067) entry_15_5) node319 := by decide +kernel

theorem node320_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node320 x = (((-6460067 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_5 x + (((30525040 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_6 x + ((4067062 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_7 x)) := by
  rw [node320_check, Integer.Sparse.eval_merge]
  rw [node319_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node321_check : node321 =
    Integer.Sparse.merge (Integer.Sparse.scale (-5240018) entry_15_9) (Integer.Sparse.scale (22667693) entry_15_10) := by decide +kernel

theorem node321_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node321 x = (((-5240018 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_9 x + ((22667693 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_10 x) := by
  rw [node321_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node322_check : node322 =
    Integer.Sparse.merge (Integer.Sparse.scale (11639620) entry_15_8) node321 := by decide +kernel

theorem node322_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node322 x = (((11639620 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_8 x + (((-5240018 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_9 x + ((22667693 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_10 x)) := by
  rw [node322_check, Integer.Sparse.eval_merge]
  rw [node321_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node323_check : node323 =
    Integer.Sparse.merge node320 node322 := by decide +kernel

theorem node323_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node323 x = ((((-6460067 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_5 x + (((30525040 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_6 x + ((4067062 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_7 x)) + (((11639620 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_8 x + (((-5240018 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_9 x + ((22667693 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_10 x))) := by
  rw [node323_check, Integer.Sparse.eval_merge]
  rw [node320_eval, node322_eval]

theorem node324_check : node324 =
    Integer.Sparse.merge node318 node323 := by decide +kernel

theorem node324_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node324 x = (((((-1896215 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_0 x + ((10377904 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_1 x) + (((16606019 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_2 x + (((-14511117 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_3 x + ((22116163 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_4 x))) + ((((-6460067 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_5 x + (((30525040 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_6 x + ((4067062 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_7 x)) + (((11639620 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_8 x + (((-5240018 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_9 x + ((22667693 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_10 x)))) := by
  rw [node324_check, Integer.Sparse.eval_merge]
  rw [node318_eval, node323_eval]

theorem node325_check : node325 =
    Integer.Sparse.merge (Integer.Sparse.scale (7247397) entry_15_11) (Integer.Sparse.scale (-39888927) entry_15_12) := by decide +kernel

theorem node325_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node325 x = (((7247397 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_11 x + ((-39888927 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_12 x) := by
  rw [node325_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node326_check : node326 =
    Integer.Sparse.merge (Integer.Sparse.scale (28297024) entry_15_14) (Integer.Sparse.scale (88538092) entry_15_15) := by decide +kernel

theorem node326_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node326 x = (((28297024 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_14 x + ((88538092 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_15 x) := by
  rw [node326_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node327_check : node327 =
    Integer.Sparse.merge (Integer.Sparse.scale (4913859) entry_15_13) node326 := by decide +kernel

theorem node327_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node327 x = (((4913859 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_13 x + (((28297024 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_14 x + ((88538092 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_15 x)) := by
  rw [node327_check, Integer.Sparse.eval_merge]
  rw [node326_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node328_check : node328 =
    Integer.Sparse.merge node325 node327 := by decide +kernel

theorem node328_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node328 x = ((((7247397 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_11 x + ((-39888927 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_12 x) + (((4913859 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_13 x + (((28297024 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_14 x + ((88538092 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_15 x))) := by
  rw [node328_check, Integer.Sparse.eval_merge]
  rw [node325_eval, node327_eval]

theorem node329_check : node329 =
    Integer.Sparse.merge (Integer.Sparse.scale (5471920) entry_15_17) (Integer.Sparse.scale (12508886) entry_15_18) := by decide +kernel

theorem node329_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node329 x = (((5471920 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_17 x + ((12508886 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_18 x) := by
  rw [node329_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node330_check : node330 =
    Integer.Sparse.merge (Integer.Sparse.scale (-40418461) entry_15_16) node329 := by decide +kernel

theorem node330_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node330 x = (((-40418461 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_16 x + (((5471920 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_17 x + ((12508886 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_18 x)) := by
  rw [node330_check, Integer.Sparse.eval_merge]
  rw [node329_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node331_check : node331 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1840193) entry_15_20) (Integer.Sparse.scale (25550802) entry_15_21) := by decide +kernel

theorem node331_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node331 x = (((-1840193 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_20 x + ((25550802 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_21 x) := by
  rw [node331_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node332_check : node332 =
    Integer.Sparse.merge (Integer.Sparse.scale (-287708) entry_15_19) node331 := by decide +kernel

theorem node332_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node332 x = (((-287708 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_19 x + (((-1840193 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_20 x + ((25550802 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_21 x)) := by
  rw [node332_check, Integer.Sparse.eval_merge]
  rw [node331_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node333_check : node333 =
    Integer.Sparse.merge node330 node332 := by decide +kernel

theorem node333_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node333 x = ((((-40418461 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_16 x + (((5471920 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_17 x + ((12508886 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_18 x)) + (((-287708 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_19 x + (((-1840193 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_20 x + ((25550802 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_21 x))) := by
  rw [node333_check, Integer.Sparse.eval_merge]
  rw [node330_eval, node332_eval]

theorem node334_check : node334 =
    Integer.Sparse.merge node328 node333 := by decide +kernel

theorem node334_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node334 x = (((((7247397 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_11 x + ((-39888927 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_12 x) + (((4913859 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_13 x + (((28297024 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_14 x + ((88538092 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_15 x))) + ((((-40418461 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_16 x + (((5471920 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_17 x + ((12508886 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_18 x)) + (((-287708 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_19 x + (((-1840193 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_20 x + ((25550802 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_21 x)))) := by
  rw [node334_check, Integer.Sparse.eval_merge]
  rw [node328_eval, node333_eval]

theorem node335_check : node335 =
    Integer.Sparse.merge node324 node334 := by decide +kernel

theorem node335_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node335 x = ((((((-1896215 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_0 x + ((10377904 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_1 x) + (((16606019 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_2 x + (((-14511117 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_3 x + ((22116163 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_4 x))) + ((((-6460067 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_5 x + (((30525040 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_6 x + ((4067062 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_7 x)) + (((11639620 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_8 x + (((-5240018 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_9 x + ((22667693 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_10 x)))) + (((((7247397 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_11 x + ((-39888927 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_12 x) + (((4913859 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_13 x + (((28297024 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_14 x + ((88538092 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_15 x))) + ((((-40418461 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_16 x + (((5471920 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_17 x + ((12508886 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_18 x)) + (((-287708 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_19 x + (((-1840193 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_20 x + ((25550802 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_21 x))))) := by
  rw [node335_check, Integer.Sparse.eval_merge]
  rw [node324_eval, node334_eval]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node357_check : node357 =
    Integer.Sparse.merge (Integer.Sparse.scale (-814376) entry_17_0) (Integer.Sparse.scale (1579557) entry_17_1) := by decide +kernel

theorem node357_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node357 x = (((-814376 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_0 x + ((1579557 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_1 x) := by
  rw [node357_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node358_check : node358 =
    Integer.Sparse.merge (Integer.Sparse.scale (189281) entry_17_3) (Integer.Sparse.scale (1039608) entry_17_4) := by decide +kernel

theorem node358_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node358 x = (((189281 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_3 x + ((1039608 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_4 x) := by
  rw [node358_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node359_check : node359 =
    Integer.Sparse.merge (Integer.Sparse.scale (1552071) entry_17_2) node358 := by decide +kernel

theorem node359_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node359 x = (((1552071 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_2 x + (((189281 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_3 x + ((1039608 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_4 x)) := by
  rw [node359_check, Integer.Sparse.eval_merge]
  rw [node358_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node360_check : node360 =
    Integer.Sparse.merge node357 node359 := by decide +kernel

theorem node360_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node360 x = ((((-814376 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_0 x + ((1579557 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_1 x) + (((1552071 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_2 x + (((189281 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_3 x + ((1039608 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_4 x))) := by
  rw [node360_check, Integer.Sparse.eval_merge]
  rw [node357_eval, node359_eval]

theorem node361_check : node361 =
    Integer.Sparse.merge (Integer.Sparse.scale (5748703) entry_17_6) (Integer.Sparse.scale (-917759) entry_17_7) := by decide +kernel

theorem node361_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node361 x = (((5748703 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_6 x + ((-917759 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_7 x) := by
  rw [node361_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node362_check : node362 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1444903) entry_17_5) node361 := by decide +kernel

theorem node362_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node362 x = (((-1444903 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_5 x + (((5748703 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_6 x + ((-917759 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_7 x)) := by
  rw [node362_check, Integer.Sparse.eval_merge]
  rw [node361_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node363_check : node363 =
    Integer.Sparse.merge (Integer.Sparse.scale (-457001) entry_17_9) (Integer.Sparse.scale (5024836) entry_17_10) := by decide +kernel

theorem node363_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node363 x = (((-457001 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_9 x + ((5024836 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_10 x) := by
  rw [node363_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node364_check : node364 =
    Integer.Sparse.merge (Integer.Sparse.scale (2061355) entry_17_8) node363 := by decide +kernel

theorem node364_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node364 x = (((2061355 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_8 x + (((-457001 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_9 x + ((5024836 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_10 x)) := by
  rw [node364_check, Integer.Sparse.eval_merge]
  rw [node363_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node365_check : node365 =
    Integer.Sparse.merge node362 node364 := by decide +kernel

theorem node365_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node365 x = ((((-1444903 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_5 x + (((5748703 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_6 x + ((-917759 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_7 x)) + (((2061355 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_8 x + (((-457001 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_9 x + ((5024836 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_10 x))) := by
  rw [node365_check, Integer.Sparse.eval_merge]
  rw [node362_eval, node364_eval]

theorem node366_check : node366 =
    Integer.Sparse.merge node360 node365 := by decide +kernel

theorem node366_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node366 x = (((((-814376 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_0 x + ((1579557 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_1 x) + (((1552071 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_2 x + (((189281 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_3 x + ((1039608 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_4 x))) + ((((-1444903 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_5 x + (((5748703 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_6 x + ((-917759 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_7 x)) + (((2061355 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_8 x + (((-457001 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_9 x + ((5024836 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_10 x)))) := by
  rw [node366_check, Integer.Sparse.eval_merge]
  rw [node360_eval, node365_eval]

theorem node367_check : node367 =
    Integer.Sparse.merge (Integer.Sparse.scale (1622012) entry_17_11) (Integer.Sparse.scale (-2442740) entry_17_12) := by decide +kernel

theorem node367_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node367 x = (((1622012 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_11 x + ((-2442740 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_12 x) := by
  rw [node367_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node368_check : node368 =
    Integer.Sparse.merge (Integer.Sparse.scale (6272171) entry_17_14) (Integer.Sparse.scale (5471920) entry_17_15) := by decide +kernel

theorem node368_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node368 x = (((6272171 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_14 x + ((5471920 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_15 x) := by
  rw [node368_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node369_check : node369 =
    Integer.Sparse.merge (Integer.Sparse.scale (2169781) entry_17_13) node368 := by decide +kernel

theorem node369_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node369 x = (((2169781 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_13 x + (((6272171 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_14 x + ((5471920 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_15 x)) := by
  rw [node369_check, Integer.Sparse.eval_merge]
  rw [node368_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node370_check : node370 =
    Integer.Sparse.merge node367 node369 := by decide +kernel

theorem node370_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node370 x = ((((1622012 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_11 x + ((-2442740 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_12 x) + (((2169781 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_13 x + (((6272171 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_14 x + ((5471920 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_15 x))) := by
  rw [node370_check, Integer.Sparse.eval_merge]
  rw [node367_eval, node369_eval]

theorem node371_check : node371 =
    Integer.Sparse.merge (Integer.Sparse.scale (1995295) entry_17_17) (Integer.Sparse.scale (135130) entry_17_18) := by decide +kernel

theorem node371_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node371 x = (((1995295 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_17 x + ((135130 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_18 x) := by
  rw [node371_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node372_check : node372 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6575663) entry_17_16) node371 := by decide +kernel

theorem node372_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node372 x = (((-6575663 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_16 x + (((1995295 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_17 x + ((135130 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_18 x)) := by
  rw [node372_check, Integer.Sparse.eval_merge]
  rw [node371_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node373_check : node373 =
    Integer.Sparse.merge (Integer.Sparse.scale (1847776) entry_17_20) (Integer.Sparse.scale (5047208) entry_17_21) := by decide +kernel

theorem node373_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node373 x = (((1847776 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_20 x + ((5047208 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_21 x) := by
  rw [node373_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node374_check : node374 =
    Integer.Sparse.merge (Integer.Sparse.scale (-105331) entry_17_19) node373 := by decide +kernel

theorem node374_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node374 x = (((-105331 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_19 x + (((1847776 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_20 x + ((5047208 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_21 x)) := by
  rw [node374_check, Integer.Sparse.eval_merge]
  rw [node373_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node375_check : node375 =
    Integer.Sparse.merge node372 node374 := by decide +kernel

theorem node375_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node375 x = ((((-6575663 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_16 x + (((1995295 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_17 x + ((135130 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_18 x)) + (((-105331 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_19 x + (((1847776 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_20 x + ((5047208 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_21 x))) := by
  rw [node375_check, Integer.Sparse.eval_merge]
  rw [node372_eval, node374_eval]

theorem node376_check : node376 =
    Integer.Sparse.merge node370 node375 := by decide +kernel

theorem node376_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node376 x = (((((1622012 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_11 x + ((-2442740 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_12 x) + (((2169781 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_13 x + (((6272171 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_14 x + ((5471920 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_15 x))) + ((((-6575663 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_16 x + (((1995295 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_17 x + ((135130 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_18 x)) + (((-105331 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_19 x + (((1847776 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_20 x + ((5047208 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_21 x)))) := by
  rw [node376_check, Integer.Sparse.eval_merge]
  rw [node370_eval, node375_eval]

theorem node377_check : node377 =
    Integer.Sparse.merge node366 node376 := by decide +kernel

theorem node377_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node377 x = ((((((-814376 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_0 x + ((1579557 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_1 x) + (((1552071 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_2 x + (((189281 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_3 x + ((1039608 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_4 x))) + ((((-1444903 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_5 x + (((5748703 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_6 x + ((-917759 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_7 x)) + (((2061355 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_8 x + (((-457001 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_9 x + ((5024836 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_10 x)))) + (((((1622012 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_11 x + ((-2442740 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_12 x) + (((2169781 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_13 x + (((6272171 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_14 x + ((5471920 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_15 x))) + ((((-6575663 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_16 x + (((1995295 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_17 x + ((135130 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_18 x)) + (((-105331 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_19 x + (((1847776 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_20 x + ((5047208 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_21 x))))) := by
  rw [node377_check, Integer.Sparse.eval_merge]
  rw [node366_eval, node376_eval]

theorem node378_check : node378 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2263423) entry_18_0) (Integer.Sparse.scale (804909) entry_18_1) := by decide +kernel

theorem node378_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node378 x = (((-2263423 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_0 x + ((804909 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_1 x) := by
  rw [node378_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node379_check : node379 =
    Integer.Sparse.merge (Integer.Sparse.scale (-767850) entry_18_3) (Integer.Sparse.scale (3446947) entry_18_4) := by decide +kernel

theorem node379_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node379 x = (((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + ((3446947 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x) := by
  rw [node379_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node380_check : node380 =
    Integer.Sparse.merge (Integer.Sparse.scale (1207709) entry_18_2) node379 := by decide +kernel

theorem node380_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node380 x = (((1207709 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_2 x + (((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + ((3446947 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x)) := by
  rw [node380_check, Integer.Sparse.eval_merge]
  rw [node379_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node381_check : node381 =
    Integer.Sparse.merge node378 node380 := by decide +kernel

theorem node381_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node381 x = ((((-2263423 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_0 x + ((804909 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_1 x) + (((1207709 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_2 x + (((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + ((3446947 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x))) := by
  rw [node381_check, Integer.Sparse.eval_merge]
  rw [node378_eval, node380_eval]

theorem node382_check : node382 =
    Integer.Sparse.merge (Integer.Sparse.scale (677023) entry_18_6) (Integer.Sparse.scale (331917) entry_18_7) := by decide +kernel

theorem node382_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node382 x = (((677023 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x) := by
  rw [node382_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node383_check : node383 =
    Integer.Sparse.merge (Integer.Sparse.scale (-396942) entry_18_5) node382 := by decide +kernel

theorem node383_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node383 x = (((-396942 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x + (((677023 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x)) := by
  rw [node383_check, Integer.Sparse.eval_merge]
  rw [node382_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node384_check : node384 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2183598) entry_18_9) (Integer.Sparse.scale (-2050110) entry_18_10) := by decide +kernel

theorem node384_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node384 x = (((-2183598 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x + ((-2050110 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x) := by
  rw [node384_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node385_check : node385 =
    Integer.Sparse.merge (Integer.Sparse.scale (52682) entry_18_8) node384 := by decide +kernel

theorem node385_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node385 x = (((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x + (((-2183598 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x + ((-2050110 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x)) := by
  rw [node385_check, Integer.Sparse.eval_merge]
  rw [node384_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node386_check : node386 =
    Integer.Sparse.merge node383 node385 := by decide +kernel

theorem node386_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node386 x = ((((-396942 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x + (((677023 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x)) + (((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x + (((-2183598 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x + ((-2050110 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x))) := by
  rw [node386_check, Integer.Sparse.eval_merge]
  rw [node383_eval, node385_eval]

theorem node387_check : node387 =
    Integer.Sparse.merge node381 node386 := by decide +kernel

theorem node387_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node387 x = (((((-2263423 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_0 x + ((804909 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_1 x) + (((1207709 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_2 x + (((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + ((3446947 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x))) + ((((-396942 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x + (((677023 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x)) + (((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x + (((-2183598 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x + ((-2050110 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x)))) := by
  rw [node387_check, Integer.Sparse.eval_merge]
  rw [node381_eval, node386_eval]

theorem node388_check : node388 =
    Integer.Sparse.merge (Integer.Sparse.scale (505346) entry_18_11) (Integer.Sparse.scale (-4212976) entry_18_12) := by decide +kernel

theorem node388_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node388 x = (((505346 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x + ((-4212976 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x) := by
  rw [node388_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node389_check : node389 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1826502) entry_18_14) (Integer.Sparse.scale (12508886) entry_18_15) := by decide +kernel

theorem node389_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node389 x = (((-1826502 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((12508886 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x) := by
  rw [node389_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node390_check : node390 =
    Integer.Sparse.merge (Integer.Sparse.scale (-175103) entry_18_13) node389 := by decide +kernel

theorem node390_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node390 x = (((-175103 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + (((-1826502 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((12508886 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x)) := by
  rw [node390_check, Integer.Sparse.eval_merge]
  rw [node389_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node391_check : node391 =
    Integer.Sparse.merge node388 node390 := by decide +kernel

theorem node391_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node391 x = ((((505346 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x + ((-4212976 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x) + (((-175103 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + (((-1826502 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((12508886 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x))) := by
  rw [node391_check, Integer.Sparse.eval_merge]
  rw [node388_eval, node390_eval]

theorem node392_check : node392 =
    Integer.Sparse.merge (Integer.Sparse.scale (135130) entry_18_17) (Integer.Sparse.scale (4058466) entry_18_18) := by decide +kernel

theorem node392_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node392 x = (((135130 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x + ((4058466 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x) := by
  rw [node392_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node393_check : node393 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6508672) entry_18_16) node392 := by decide +kernel

theorem node393_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node393 x = (((-6508672 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + (((135130 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x + ((4058466 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x)) := by
  rw [node393_check, Integer.Sparse.eval_merge]
  rw [node392_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node394_check : node394 =
    Integer.Sparse.merge (Integer.Sparse.scale (298837) entry_18_20) (Integer.Sparse.scale (6360316) entry_18_21) := by decide +kernel

theorem node394_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node394 x = (((298837 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + ((6360316 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x) := by
  rw [node394_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node395_check : node395 =
    Integer.Sparse.merge (Integer.Sparse.scale (292521) entry_18_19) node394 := by decide +kernel

theorem node395_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node395 x = (((292521 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x + (((298837 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + ((6360316 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x)) := by
  rw [node395_check, Integer.Sparse.eval_merge]
  rw [node394_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node396_check : node396 =
    Integer.Sparse.merge node393 node395 := by decide +kernel

theorem node396_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node396 x = ((((-6508672 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + (((135130 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x + ((4058466 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x)) + (((292521 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x + (((298837 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + ((6360316 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x))) := by
  rw [node396_check, Integer.Sparse.eval_merge]
  rw [node393_eval, node395_eval]

theorem node397_check : node397 =
    Integer.Sparse.merge node391 node396 := by decide +kernel

theorem node397_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node397 x = (((((505346 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x + ((-4212976 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x) + (((-175103 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + (((-1826502 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((12508886 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x))) + ((((-6508672 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + (((135130 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x + ((4058466 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x)) + (((292521 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x + (((298837 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + ((6360316 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x)))) := by
  rw [node397_check, Integer.Sparse.eval_merge]
  rw [node391_eval, node396_eval]

theorem node398_check : node398 =
    Integer.Sparse.merge node387 node397 := by decide +kernel

theorem node398_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node398 x = ((((((-2263423 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_0 x + ((804909 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_1 x) + (((1207709 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_2 x + (((-767850 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + ((3446947 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x))) + ((((-396942 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x + (((677023 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x + ((331917 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x)) + (((52682 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x + (((-2183598 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x + ((-2050110 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x)))) + (((((505346 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x + ((-4212976 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x) + (((-175103 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + (((-1826502 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((12508886 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x))) + ((((-6508672 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + (((135130 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x + ((4058466 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x)) + (((292521 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x + (((298837 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + ((6360316 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x))))) := by
  rw [node398_check, Integer.Sparse.eval_merge]
  rw [node387_eval, node397_eval]

theorem node399_check : node399 =
    Integer.Sparse.merge (Integer.Sparse.scale (-227986) entry_19_0) (Integer.Sparse.scale (-14681) entry_19_1) := by decide +kernel

theorem node399_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node399 x = (((-227986 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + ((-14681 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x) := by
  rw [node399_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node400_check : node400 =
    Integer.Sparse.merge (Integer.Sparse.scale (318017) entry_19_3) (Integer.Sparse.scale (-11230) entry_19_4) := by decide +kernel

theorem node400_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node400 x = (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + ((-11230 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x) := by
  rw [node400_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node401_check : node401 =
    Integer.Sparse.merge (Integer.Sparse.scale (97824) entry_19_2) node400 := by decide +kernel

theorem node401_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node401 x = (((97824 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x + (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + ((-11230 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x)) := by
  rw [node401_check, Integer.Sparse.eval_merge]
  rw [node400_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node402_check : node402 =
    Integer.Sparse.merge node399 node401 := by decide +kernel

theorem node402_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node402 x = ((((-227986 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + ((-14681 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x) + (((97824 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x + (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + ((-11230 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x))) := by
  rw [node402_check, Integer.Sparse.eval_merge]
  rw [node399_eval, node401_eval]

theorem node403_check : node403 =
    Integer.Sparse.merge (Integer.Sparse.scale (-524585) entry_19_6) (Integer.Sparse.scale (-100234) entry_19_7) := by decide +kernel

theorem node403_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node403 x = (((-524585 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + ((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x) := by
  rw [node403_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node404_check : node404 =
    Integer.Sparse.merge (Integer.Sparse.scale (65585) entry_19_5) node403 := by decide +kernel

theorem node404_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node404 x = (((65585 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x + (((-524585 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + ((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x)) := by
  rw [node404_check, Integer.Sparse.eval_merge]
  rw [node403_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node405_check : node405 =
    Integer.Sparse.merge (Integer.Sparse.scale (-290864) entry_19_9) (Integer.Sparse.scale (-579570) entry_19_10) := by decide +kernel

theorem node405_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node405 x = (((-290864 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((-579570 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x) := by
  rw [node405_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node406_check : node406 =
    Integer.Sparse.merge (Integer.Sparse.scale (294656) entry_19_8) node405 := by decide +kernel

theorem node406_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node406 x = (((294656 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x + (((-290864 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((-579570 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x)) := by
  rw [node406_check, Integer.Sparse.eval_merge]
  rw [node405_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node407_check : node407 =
    Integer.Sparse.merge node404 node406 := by decide +kernel

theorem node407_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node407 x = ((((65585 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x + (((-524585 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + ((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x)) + (((294656 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x + (((-290864 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((-579570 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x))) := by
  rw [node407_check, Integer.Sparse.eval_merge]
  rw [node404_eval, node406_eval]

theorem node408_check : node408 =
    Integer.Sparse.merge node402 node407 := by decide +kernel

theorem node408_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node408 x = (((((-227986 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + ((-14681 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x) + (((97824 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x + (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + ((-11230 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x))) + ((((65585 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x + (((-524585 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + ((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x)) + (((294656 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x + (((-290864 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((-579570 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x)))) := by
  rw [node408_check, Integer.Sparse.eval_merge]
  rw [node402_eval, node407_eval]

theorem node409_check : node409 =
    Integer.Sparse.merge (Integer.Sparse.scale (410918) entry_19_11) (Integer.Sparse.scale (-270161) entry_19_12) := by decide +kernel

theorem node409_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node409 x = (((410918 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x + ((-270161 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x) := by
  rw [node409_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node410_check : node410 =
    Integer.Sparse.merge (Integer.Sparse.scale (-293742) entry_19_14) (Integer.Sparse.scale (-287708) entry_19_15) := by decide +kernel

theorem node410_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node410 x = (((-293742 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-287708 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x) := by
  rw [node410_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node411_check : node411 =
    Integer.Sparse.merge (Integer.Sparse.scale (28798) entry_19_13) node410 := by decide +kernel

theorem node411_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node411 x = (((28798 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + (((-293742 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-287708 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x)) := by
  rw [node411_check, Integer.Sparse.eval_merge]
  rw [node410_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node412_check : node412 =
    Integer.Sparse.merge node409 node411 := by decide +kernel

theorem node412_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node412 x = ((((410918 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x + ((-270161 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x) + (((28798 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + (((-293742 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-287708 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x))) := by
  rw [node412_check, Integer.Sparse.eval_merge]
  rw [node409_eval, node411_eval]

theorem node413_check : node413 =
    Integer.Sparse.merge (Integer.Sparse.scale (-105331) entry_19_17) (Integer.Sparse.scale (292521) entry_19_18) := by decide +kernel

theorem node413_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node413 x = (((-105331 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x + ((292521 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x) := by
  rw [node413_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node414_check : node414 =
    Integer.Sparse.merge (Integer.Sparse.scale (-977591) entry_19_16) node413 := by decide +kernel

theorem node414_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node414 x = (((-977591 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + (((-105331 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x + ((292521 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x)) := by
  rw [node414_check, Integer.Sparse.eval_merge]
  rw [node413_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node415_check : node415 =
    Integer.Sparse.merge (Integer.Sparse.scale (64677) entry_19_20) (Integer.Sparse.scale (847534) entry_19_21) := by decide +kernel

theorem node415_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node415 x = (((64677 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x + ((847534 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_21 x) := by
  rw [node415_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node416_check : node416 =
    Integer.Sparse.merge (Integer.Sparse.scale (332991) entry_19_19) node415 := by decide +kernel

theorem node416_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node416 x = (((332991 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x + (((64677 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x + ((847534 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_21 x)) := by
  rw [node416_check, Integer.Sparse.eval_merge]
  rw [node415_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node417_check : node417 =
    Integer.Sparse.merge node414 node416 := by decide +kernel

theorem node417_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node417 x = ((((-977591 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + (((-105331 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x + ((292521 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x)) + (((332991 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x + (((64677 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x + ((847534 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_21 x))) := by
  rw [node417_check, Integer.Sparse.eval_merge]
  rw [node414_eval, node416_eval]

theorem node418_check : node418 =
    Integer.Sparse.merge node412 node417 := by decide +kernel

theorem node418_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node418 x = (((((410918 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x + ((-270161 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x) + (((28798 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + (((-293742 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-287708 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x))) + ((((-977591 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + (((-105331 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x + ((292521 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x)) + (((332991 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x + (((64677 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x + ((847534 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_21 x)))) := by
  rw [node418_check, Integer.Sparse.eval_merge]
  rw [node412_eval, node417_eval]

theorem node419_check : node419 =
    Integer.Sparse.merge node408 node418 := by decide +kernel

theorem node419_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node419 x = ((((((-227986 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + ((-14681 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x) + (((97824 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x + (((318017 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + ((-11230 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x))) + ((((65585 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x + (((-524585 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + ((-100234 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x)) + (((294656 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x + (((-290864 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((-579570 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x)))) + (((((410918 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x + ((-270161 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x) + (((28798 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + (((-293742 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-287708 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x))) + ((((-977591 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + (((-105331 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x + ((292521 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x)) + (((332991 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x + (((64677 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x + ((847534 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_21 x))))) := by
  rw [node419_check, Integer.Sparse.eval_merge]
  rw [node408_eval, node418_eval]

theorem node420_check : node420 =
    Integer.Sparse.merge (Integer.Sparse.scale (-7748966) entry_20_0) (Integer.Sparse.scale (236179) entry_20_1) := by decide +kernel

theorem node420_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node420 x = (((-7748966 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_0 x + ((236179 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x) := by
  rw [node420_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node421_check : node421 =
    Integer.Sparse.merge (Integer.Sparse.scale (4576468) entry_20_3) (Integer.Sparse.scale (-4019963) entry_20_4) := by decide +kernel

theorem node421_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node421 x = (((4576468 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + ((-4019963 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x) := by
  rw [node421_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node422_check : node422 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2753502) entry_20_2) node421 := by decide +kernel

theorem node422_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node422 x = (((-2753502 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x + (((4576468 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + ((-4019963 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x)) := by
  rw [node422_check, Integer.Sparse.eval_merge]
  rw [node421_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node423_check : node423 =
    Integer.Sparse.merge node420 node422 := by decide +kernel

theorem node423_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node423 x = ((((-7748966 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_0 x + ((236179 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x) + (((-2753502 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x + (((4576468 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + ((-4019963 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x))) := by
  rw [node423_check, Integer.Sparse.eval_merge]
  rw [node420_eval, node422_eval]

theorem node424_check : node424 =
    Integer.Sparse.merge (Integer.Sparse.scale (9575677) entry_20_6) (Integer.Sparse.scale (-6691783) entry_20_7) := by decide +kernel

theorem node424_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node424 x = (((9575677 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_6 x + ((-6691783 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x) := by
  rw [node424_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node425_check : node425 =
    Integer.Sparse.merge (Integer.Sparse.scale (-74307) entry_20_5) node424 := by decide +kernel

theorem node425_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node425 x = (((-74307 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x + (((9575677 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_6 x + ((-6691783 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x)) := by
  rw [node425_check, Integer.Sparse.eval_merge]
  rw [node424_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node426_check : node426 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4392796) entry_20_9) (Integer.Sparse.scale (-2671294) entry_20_10) := by decide +kernel

theorem node426_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node426 x = (((-4392796 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x + ((-2671294 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x) := by
  rw [node426_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node427_check : node427 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2279851) entry_20_8) node426 := by decide +kernel

theorem node427_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node427 x = (((-2279851 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x + (((-4392796 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x + ((-2671294 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x)) := by
  rw [node427_check, Integer.Sparse.eval_merge]
  rw [node426_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node428_check : node428 =
    Integer.Sparse.merge node425 node427 := by decide +kernel

theorem node428_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node428 x = ((((-74307 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x + (((9575677 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_6 x + ((-6691783 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x)) + (((-2279851 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x + (((-4392796 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x + ((-2671294 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x))) := by
  rw [node428_check, Integer.Sparse.eval_merge]
  rw [node425_eval, node427_eval]

theorem node429_check : node429 =
    Integer.Sparse.merge node423 node428 := by decide +kernel

theorem node429_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node429 x = (((((-7748966 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_0 x + ((236179 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x) + (((-2753502 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x + (((4576468 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + ((-4019963 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x))) + ((((-74307 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x + (((9575677 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_6 x + ((-6691783 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x)) + (((-2279851 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x + (((-4392796 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x + ((-2671294 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x)))) := by
  rw [node429_check, Integer.Sparse.eval_merge]
  rw [node423_eval, node428_eval]

theorem node430_check : node430 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3651298) entry_20_11) (Integer.Sparse.scale (6351203) entry_20_12) := by decide +kernel

theorem node430_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node430 x = (((-3651298 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x + ((6351203 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x) := by
  rw [node430_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node431_check : node431 =
    Integer.Sparse.merge (Integer.Sparse.scale (4188233) entry_20_14) (Integer.Sparse.scale (-1840193) entry_20_15) := by decide +kernel

theorem node431_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node431 x = (((4188233 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x + ((-1840193 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x) := by
  rw [node431_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node432_check : node432 =
    Integer.Sparse.merge (Integer.Sparse.scale (-575196) entry_20_13) node431 := by decide +kernel

theorem node432_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node432 x = (((-575196 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_13 x + (((4188233 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x + ((-1840193 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x)) := by
  rw [node432_check, Integer.Sparse.eval_merge]
  rw [node431_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node433_check : node433 =
    Integer.Sparse.merge node430 node432 := by decide +kernel

theorem node433_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node433 x = ((((-3651298 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x + ((6351203 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x) + (((-575196 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_13 x + (((4188233 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x + ((-1840193 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x))) := by
  rw [node433_check, Integer.Sparse.eval_merge]
  rw [node430_eval, node432_eval]

theorem node434_check : node434 =
    Integer.Sparse.merge (Integer.Sparse.scale (1847776) entry_20_17) (Integer.Sparse.scale (298837) entry_20_18) := by decide +kernel

theorem node434_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node434 x = (((1847776 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x + ((298837 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x) := by
  rw [node434_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node435_check : node435 =
    Integer.Sparse.merge (Integer.Sparse.scale (-15271475) entry_20_16) node434 := by decide +kernel

theorem node435_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node435 x = (((-15271475 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + (((1847776 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x + ((298837 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x)) := by
  rw [node435_check, Integer.Sparse.eval_merge]
  rw [node434_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node436_check : node436 =
    Integer.Sparse.merge (Integer.Sparse.scale (13948174) entry_20_20) (Integer.Sparse.scale (20619430) entry_20_21) := by decide +kernel

theorem node436_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node436 x = (((13948174 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_20 x + ((20619430 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_21 x) := by
  rw [node436_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node437_check : node437 =
    Integer.Sparse.merge (Integer.Sparse.scale (64677) entry_20_19) node436 := by decide +kernel

theorem node437_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node437 x = (((64677 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x + (((13948174 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_20 x + ((20619430 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_21 x)) := by
  rw [node437_check, Integer.Sparse.eval_merge]
  rw [node436_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node438_check : node438 =
    Integer.Sparse.merge node435 node437 := by decide +kernel

theorem node438_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node438 x = ((((-15271475 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + (((1847776 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x + ((298837 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x)) + (((64677 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x + (((13948174 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_20 x + ((20619430 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_21 x))) := by
  rw [node438_check, Integer.Sparse.eval_merge]
  rw [node435_eval, node437_eval]

theorem node439_check : node439 =
    Integer.Sparse.merge node433 node438 := by decide +kernel

theorem node439_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node439 x = (((((-3651298 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x + ((6351203 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x) + (((-575196 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_13 x + (((4188233 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x + ((-1840193 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x))) + ((((-15271475 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + (((1847776 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x + ((298837 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x)) + (((64677 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x + (((13948174 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_20 x + ((20619430 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_21 x)))) := by
  rw [node439_check, Integer.Sparse.eval_merge]
  rw [node433_eval, node438_eval]

theorem node440_check : node440 =
    Integer.Sparse.merge node429 node439 := by decide +kernel

theorem node440_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node440 x = ((((((-7748966 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_0 x + ((236179 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x) + (((-2753502 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x + (((4576468 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + ((-4019963 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x))) + ((((-74307 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x + (((9575677 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_6 x + ((-6691783 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x)) + (((-2279851 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x + (((-4392796 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x + ((-2671294 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x)))) + (((((-3651298 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x + ((6351203 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x) + (((-575196 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_13 x + (((4188233 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x + ((-1840193 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x))) + ((((-15271475 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + (((1847776 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x + ((298837 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x)) + (((64677 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x + (((13948174 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_20 x + ((20619430 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_21 x))))) := by
  rw [node440_check, Integer.Sparse.eval_merge]
  rw [node429_eval, node439_eval]

end MUB6.Certificate.GramAssembly.Block4

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

theorem sum_expand_22 {R : Type*} [AddCommMonoid R] (F : Fin 22 → R) :
    (∑ i, F i) = ((((F 0 + F 1) + (F 2 + (F 3 + F 4))) + ((F 5 + (F 6 + F 7)) + (F 8 + (F 9 + F 10)))) + (((F 11 + F 12) + (F 13 + (F 14 + F 15))) + ((F 16 + (F 17 + F 18)) + (F 19 + (F 20 + F 21))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F 0 + (F 1 + (F 2 + (F 3 + (F 4 + (F 5 + (F 6 + (F 7 + (F 8 + (F 9 + (F 10 + (F 11 + (F 12 + (F 13 + (F 14 + (F 15 + (F 16 + (F 17 + (F 18 + (F 19 + (F 20 + (F 21 + 0)))))))))))))))))))))) = ((((F 0 + F 1) + (F 2 + (F 3 + F 4))) + ((F 5 + (F 6 + F 7)) + (F 8 + (F 9 + F 10)))) + (((F 11 + F 12) + (F 13 + (F 14 + F 15))) + ((F 16 + (F 17 + F 18)) + (F 19 + (F 20 + F 21)))))
  simp only [add_zero, add_assoc]

end MUB6.Certificate.GramAssembly

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

open scoped BigOperators

theorem row_eval_0 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node20 x =
      ∑ j : Fin 22, (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x := by
  rw [node20_eval]
  exact (sum_expand_22 (fun j => (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x)).symm

theorem row_eval_1 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node41 x =
      ∑ j : Fin 22, (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x := by
  rw [node41_eval]
  exact (sum_expand_22 (fun j => (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x)).symm

theorem row_eval_2 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node62 x =
      ∑ j : Fin 22, (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x := by
  rw [node62_eval]
  exact (sum_expand_22 (fun j => (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x)).symm

theorem row_eval_3 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node83 x =
      ∑ j : Fin 22, (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x := by
  rw [node83_eval]
  exact (sum_expand_22 (fun j => (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x)).symm

theorem row_eval_4 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node104 x =
      ∑ j : Fin 22, (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x := by
  rw [node104_eval]
  exact (sum_expand_22 (fun j => (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x)).symm

theorem row_eval_5 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node125 x =
      ∑ j : Fin 22, (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x := by
  rw [node125_eval]
  exact (sum_expand_22 (fun j => (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x)).symm

theorem row_eval_7 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node167 x =
      ∑ j : Fin 22, (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x := by
  rw [node167_eval]
  exact (sum_expand_22 (fun j => (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x)).symm

theorem row_eval_8 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node188 x =
      ∑ j : Fin 22, (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x := by
  rw [node188_eval]
  exact (sum_expand_22 (fun j => (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x)).symm

theorem row_eval_9 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node209 x =
      ∑ j : Fin 22, (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x := by
  rw [node209_eval]
  exact (sum_expand_22 (fun j => (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x)).symm

theorem row_eval_10 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node230 x =
      ∑ j : Fin 22, (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x := by
  rw [node230_eval]
  exact (sum_expand_22 (fun j => (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x)).symm

theorem row_eval_11 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node251 x =
      ∑ j : Fin 22, (weights 11 j : ℝ) * Integer.Sparse.eval (entries 11 j) x := by
  rw [node251_eval]
  exact (sum_expand_22 (fun j => (weights 11 j : ℝ) * Integer.Sparse.eval (entries 11 j) x)).symm

theorem row_eval_12 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node272 x =
      ∑ j : Fin 22, (weights 12 j : ℝ) * Integer.Sparse.eval (entries 12 j) x := by
  rw [node272_eval]
  exact (sum_expand_22 (fun j => (weights 12 j : ℝ) * Integer.Sparse.eval (entries 12 j) x)).symm

theorem row_eval_15 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node335 x =
      ∑ j : Fin 22, (weights 15 j : ℝ) * Integer.Sparse.eval (entries 15 j) x := by
  rw [node335_eval]
  exact (sum_expand_22 (fun j => (weights 15 j : ℝ) * Integer.Sparse.eval (entries 15 j) x)).symm

theorem row_eval_17 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node377 x =
      ∑ j : Fin 22, (weights 17 j : ℝ) * Integer.Sparse.eval (entries 17 j) x := by
  rw [node377_eval]
  exact (sum_expand_22 (fun j => (weights 17 j : ℝ) * Integer.Sparse.eval (entries 17 j) x)).symm

theorem row_eval_18 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node398 x =
      ∑ j : Fin 22, (weights 18 j : ℝ) * Integer.Sparse.eval (entries 18 j) x := by
  rw [node398_eval]
  exact (sum_expand_22 (fun j => (weights 18 j : ℝ) * Integer.Sparse.eval (entries 18 j) x)).symm

theorem row_eval_19 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node419 x =
      ∑ j : Fin 22, (weights 19 j : ℝ) * Integer.Sparse.eval (entries 19 j) x := by
  rw [node419_eval]
  exact (sum_expand_22 (fun j => (weights 19 j : ℝ) * Integer.Sparse.eval (entries 19 j) x)).symm

theorem row_eval_20 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node440 x =
      ∑ j : Fin 22, (weights 20 j : ℝ) * Integer.Sparse.eval (entries 20 j) x := by
  rw [node440_eval]
  exact (sum_expand_22 (fun j => (weights 20 j : ℝ) * Integer.Sparse.eval (entries 20 j) x)).symm

theorem rows_eval_e_oai (i : Fin 22) (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval (rows i) x =
      ∑ j : Fin 22, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  fin_cases i
  · exact row_eval_0 x
  · exact row_eval_1 x
  · exact row_eval_2 x
  · exact row_eval_3 x
  · exact row_eval_4 x
  · exact row_eval_5 x
  · exact row_eval_6_e x
  · exact row_eval_7 x
  · exact row_eval_8 x
  · exact row_eval_9 x
  · exact row_eval_10 x
  · exact row_eval_11 x
  · exact row_eval_12 x
  · exact row_eval_13_e x
  · exact row_eval_14_e x
  · exact row_eval_15 x
  · exact row_eval_16_e x
  · exact row_eval_17 x
  · exact row_eval_18 x
  · exact row_eval_19 x
  · exact row_eval_20 x
  · exact row_eval_21_e x

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block4.rows_eval_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block4.rows_eval_e_oai
