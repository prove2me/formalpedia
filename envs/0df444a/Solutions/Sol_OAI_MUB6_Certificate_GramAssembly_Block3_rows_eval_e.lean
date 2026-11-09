-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block3.rows_eval_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:37:41.939229+00:00
-- url     : https://prove2.me/submissions/4ca85176-fa67-4042-bd3e-61e026111e1a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E005
import Definitions.Def_OAIQ106E177
import Definitions.Def_OAIQ106E009
import Definitions.Def_OAIQ106E196
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block3_row_eval_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block3_row_eval_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block3_row_eval_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block3_row_eval_26_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block3_row_eval_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block3_row_eval_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block3_row_eval_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block3_row_eval_9_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node0_check : node0 =
    Integer.Sparse.merge (Integer.Sparse.scale (1103969) entry_0_1) (Integer.Sparse.scale (-366698) entry_0_2) := by decide +kernel

theorem node0_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node0 x = (((1103969 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x + ((-366698 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x) := by
  rw [node0_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node1_check : node1 =
    Integer.Sparse.merge (Integer.Sparse.scale (21638825) entry_0_0) node0 := by decide +kernel

theorem node1_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node1 x = (((21638825 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + (((1103969 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x + ((-366698 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x)) := by
  rw [node1_check, Integer.Sparse.eval_merge]
  rw [node0_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node2_check : node2 =
    Integer.Sparse.merge (Integer.Sparse.scale (4675758) entry_0_4) (Integer.Sparse.scale (-348911) entry_0_5) := by decide +kernel

theorem node2_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node2 x = (((4675758 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x + ((-348911 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x) := by
  rw [node2_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node3_check : node3 =
    Integer.Sparse.merge (Integer.Sparse.scale (4472903) entry_0_3) node2 := by decide +kernel

theorem node3_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node3 x = (((4472903 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + (((4675758 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x + ((-348911 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x)) := by
  rw [node3_check, Integer.Sparse.eval_merge]
  rw [node2_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node4_check : node4 =
    Integer.Sparse.merge node1 node3 := by decide +kernel

theorem node4_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node4 x = ((((21638825 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + (((1103969 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x + ((-366698 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x)) + (((4472903 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + (((4675758 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x + ((-348911 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x))) := by
  rw [node4_check, Integer.Sparse.eval_merge]
  rw [node1_eval, node3_eval]

theorem node5_check : node5 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6679308) entry_0_7) (Integer.Sparse.scale (8323724) entry_0_8) := by decide +kernel

theorem node5_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node5 x = (((-6679308 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x + ((8323724 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x) := by
  rw [node5_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node6_check : node6 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1653142) entry_0_6) node5 := by decide +kernel

theorem node6_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node6 x = (((-1653142 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x + (((-6679308 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x + ((8323724 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x)) := by
  rw [node6_check, Integer.Sparse.eval_merge]
  rw [node5_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node7_check : node7 =
    Integer.Sparse.merge (Integer.Sparse.scale (7441570) entry_0_9) (Integer.Sparse.scale (4676581) entry_0_10) := by decide +kernel

theorem node7_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node7 x = (((7441570 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + ((4676581 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x) := by
  rw [node7_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node8_check : node8 =
    Integer.Sparse.merge (Integer.Sparse.scale (5623964) entry_0_11) (Integer.Sparse.scale (8331635) entry_0_12) := by decide +kernel

theorem node8_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node8 x = (((5623964 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x + ((8331635 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_12 x) := by
  rw [node8_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node9_check : node9 =
    Integer.Sparse.merge node7 node8 := by decide +kernel

theorem node9_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node9 x = ((((7441570 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + ((4676581 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x) + (((5623964 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x + ((8331635 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_12 x)) := by
  rw [node9_check, Integer.Sparse.eval_merge]
  rw [node7_eval, node8_eval]

theorem node10_check : node10 =
    Integer.Sparse.merge node6 node9 := by decide +kernel

theorem node10_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node10 x = ((((-1653142 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x + (((-6679308 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x + ((8323724 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x)) + ((((7441570 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + ((4676581 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x) + (((5623964 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x + ((8331635 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_12 x))) := by
  rw [node10_check, Integer.Sparse.eval_merge]
  rw [node6_eval, node9_eval]

theorem node11_check : node11 =
    Integer.Sparse.merge node4 node10 := by decide +kernel

theorem node11_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node11 x = (((((21638825 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + (((1103969 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x + ((-366698 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x)) + (((4472903 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + (((4675758 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x + ((-348911 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x))) + ((((-1653142 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x + (((-6679308 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x + ((8323724 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x)) + ((((7441570 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + ((4676581 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x) + (((5623964 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x + ((8331635 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_12 x)))) := by
  rw [node11_check, Integer.Sparse.eval_merge]
  rw [node4_eval, node10_eval]

theorem node12_check : node12 =
    Integer.Sparse.merge (Integer.Sparse.scale (1781770) entry_0_14) (Integer.Sparse.scale (196990) entry_0_15) := by decide +kernel

theorem node12_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node12 x = (((1781770 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_14 x + ((196990 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_15 x) := by
  rw [node12_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node13_check : node13 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2350116) entry_0_13) node12 := by decide +kernel

theorem node13_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node13 x = (((-2350116 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_13 x + (((1781770 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_14 x + ((196990 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_15 x)) := by
  rw [node13_check, Integer.Sparse.eval_merge]
  rw [node12_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node14_check : node14 =
    Integer.Sparse.merge (Integer.Sparse.scale (-196597) entry_0_16) (Integer.Sparse.scale (6566227) entry_0_17) := by decide +kernel

theorem node14_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node14 x = (((-196597 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_16 x + ((6566227 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_17 x) := by
  rw [node14_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node15_check : node15 =
    Integer.Sparse.merge (Integer.Sparse.scale (-8510275) entry_0_18) (Integer.Sparse.scale (4751159) entry_0_19) := by decide +kernel

theorem node15_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node15 x = (((-8510275 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_18 x + ((4751159 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_19 x) := by
  rw [node15_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node16_check : node16 =
    Integer.Sparse.merge node14 node15 := by decide +kernel

theorem node16_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node16 x = ((((-196597 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_16 x + ((6566227 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_17 x) + (((-8510275 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_18 x + ((4751159 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_19 x)) := by
  rw [node16_check, Integer.Sparse.eval_merge]
  rw [node14_eval, node15_eval]

theorem node17_check : node17 =
    Integer.Sparse.merge node13 node16 := by decide +kernel

theorem node17_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node17 x = ((((-2350116 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_13 x + (((1781770 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_14 x + ((196990 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_15 x)) + ((((-196597 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_16 x + ((6566227 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_17 x) + (((-8510275 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_18 x + ((4751159 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_19 x))) := by
  rw [node17_check, Integer.Sparse.eval_merge]
  rw [node13_eval, node16_eval]

theorem node18_check : node18 =
    Integer.Sparse.merge (Integer.Sparse.scale (14265487) entry_0_21) (Integer.Sparse.scale (26849611) entry_0_22) := by decide +kernel

theorem node18_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node18 x = (((14265487 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_21 x + ((26849611 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_22 x) := by
  rw [node18_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node19_check : node19 =
    Integer.Sparse.merge (Integer.Sparse.scale (70965) entry_0_20) node18 := by decide +kernel

theorem node19_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node19 x = (((70965 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_20 x + (((14265487 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_21 x + ((26849611 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_22 x)) := by
  rw [node19_check, Integer.Sparse.eval_merge]
  rw [node18_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node20_check : node20 =
    Integer.Sparse.merge (Integer.Sparse.scale (-9014352) entry_0_23) (Integer.Sparse.scale (2605212) entry_0_24) := by decide +kernel

theorem node20_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node20 x = (((-9014352 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_23 x + ((2605212 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_24 x) := by
  rw [node20_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node21_check : node21 =
    Integer.Sparse.merge (Integer.Sparse.scale (-9952367) entry_0_25) (Integer.Sparse.scale (-3848880) entry_0_26) := by decide +kernel

theorem node21_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node21 x = (((-9952367 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_25 x + ((-3848880 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_26 x) := by
  rw [node21_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node22_check : node22 =
    Integer.Sparse.merge node20 node21 := by decide +kernel

theorem node22_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node22 x = ((((-9014352 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_23 x + ((2605212 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_24 x) + (((-9952367 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_25 x + ((-3848880 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_26 x)) := by
  rw [node22_check, Integer.Sparse.eval_merge]
  rw [node20_eval, node21_eval]

theorem node23_check : node23 =
    Integer.Sparse.merge node19 node22 := by decide +kernel

theorem node23_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node23 x = ((((70965 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_20 x + (((14265487 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_21 x + ((26849611 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_22 x)) + ((((-9014352 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_23 x + ((2605212 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_24 x) + (((-9952367 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_25 x + ((-3848880 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_26 x))) := by
  rw [node23_check, Integer.Sparse.eval_merge]
  rw [node19_eval, node22_eval]

theorem node24_check : node24 =
    Integer.Sparse.merge node17 node23 := by decide +kernel

theorem node24_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node24 x = (((((-2350116 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_13 x + (((1781770 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_14 x + ((196990 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_15 x)) + ((((-196597 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_16 x + ((6566227 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_17 x) + (((-8510275 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_18 x + ((4751159 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_19 x))) + ((((70965 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_20 x + (((14265487 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_21 x + ((26849611 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_22 x)) + ((((-9014352 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_23 x + ((2605212 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_24 x) + (((-9952367 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_25 x + ((-3848880 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_26 x)))) := by
  rw [node24_check, Integer.Sparse.eval_merge]
  rw [node17_eval, node23_eval]

theorem node25_check : node25 =
    Integer.Sparse.merge node11 node24 := by decide +kernel

theorem node25_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node25 x = ((((((21638825 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + (((1103969 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x + ((-366698 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x)) + (((4472903 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + (((4675758 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x + ((-348911 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x))) + ((((-1653142 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x + (((-6679308 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x + ((8323724 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x)) + ((((7441570 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + ((4676581 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x) + (((5623964 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x + ((8331635 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_12 x)))) + (((((-2350116 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_13 x + (((1781770 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_14 x + ((196990 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_15 x)) + ((((-196597 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_16 x + ((6566227 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_17 x) + (((-8510275 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_18 x + ((4751159 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_19 x))) + ((((70965 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_20 x + (((14265487 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_21 x + ((26849611 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_22 x)) + ((((-9014352 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_23 x + ((2605212 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_24 x) + (((-9952367 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_25 x + ((-3848880 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_26 x))))) := by
  rw [node25_check, Integer.Sparse.eval_merge]
  rw [node11_eval, node24_eval]

theorem node26_check : node26 =
    Integer.Sparse.merge (Integer.Sparse.scale (944580) entry_1_1) (Integer.Sparse.scale (262232) entry_1_2) := by decide +kernel

theorem node26_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node26 x = (((944580 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x + ((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x) := by
  rw [node26_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node27_check : node27 =
    Integer.Sparse.merge (Integer.Sparse.scale (1103969) entry_1_0) node26 := by decide +kernel

theorem node27_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node27 x = (((1103969 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + (((944580 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x + ((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x)) := by
  rw [node27_check, Integer.Sparse.eval_merge]
  rw [node26_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node28_check : node28 =
    Integer.Sparse.merge (Integer.Sparse.scale (95477) entry_1_4) (Integer.Sparse.scale (1215062) entry_1_5) := by decide +kernel

theorem node28_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node28 x = (((95477 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x + ((1215062 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x) := by
  rw [node28_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node29_check : node29 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1282119) entry_1_3) node28 := by decide +kernel

theorem node29_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node29 x = (((-1282119 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + (((95477 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x + ((1215062 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x)) := by
  rw [node29_check, Integer.Sparse.eval_merge]
  rw [node28_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node30_check : node30 =
    Integer.Sparse.merge node27 node29 := by decide +kernel

theorem node30_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node30 x = ((((1103969 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + (((944580 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x + ((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x)) + (((-1282119 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + (((95477 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x + ((1215062 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x))) := by
  rw [node30_check, Integer.Sparse.eval_merge]
  rw [node27_eval, node29_eval]

theorem node31_check : node31 =
    Integer.Sparse.merge (Integer.Sparse.scale (-35356) entry_1_7) (Integer.Sparse.scale (-831071) entry_1_8) := by decide +kernel

theorem node31_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node31 x = (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + ((-831071 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x) := by
  rw [node31_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node32_check : node32 =
    Integer.Sparse.merge (Integer.Sparse.scale (-564931) entry_1_6) node31 := by decide +kernel

theorem node32_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node32 x = (((-564931 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + ((-831071 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x)) := by
  rw [node32_check, Integer.Sparse.eval_merge]
  rw [node31_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node33_check : node33 =
    Integer.Sparse.merge (Integer.Sparse.scale (337531) entry_1_9) (Integer.Sparse.scale (-143710) entry_1_10) := by decide +kernel

theorem node33_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node33 x = (((337531 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((-143710 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x) := by
  rw [node33_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node34_check : node34 =
    Integer.Sparse.merge (Integer.Sparse.scale (302472) entry_1_11) (Integer.Sparse.scale (204411) entry_1_12) := by decide +kernel

theorem node34_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node34 x = (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x + ((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x) := by
  rw [node34_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node35_check : node35 =
    Integer.Sparse.merge node33 node34 := by decide +kernel

theorem node35_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node35 x = ((((337531 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((-143710 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x) + (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x + ((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x)) := by
  rw [node35_check, Integer.Sparse.eval_merge]
  rw [node33_eval, node34_eval]

theorem node36_check : node36 =
    Integer.Sparse.merge node32 node35 := by decide +kernel

theorem node36_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node36 x = ((((-564931 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + ((-831071 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x)) + ((((337531 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((-143710 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x) + (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x + ((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x))) := by
  rw [node36_check, Integer.Sparse.eval_merge]
  rw [node32_eval, node35_eval]

theorem node37_check : node37 =
    Integer.Sparse.merge node30 node36 := by decide +kernel

theorem node37_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node37 x = (((((1103969 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + (((944580 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x + ((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x)) + (((-1282119 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + (((95477 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x + ((1215062 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x))) + ((((-564931 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + ((-831071 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x)) + ((((337531 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((-143710 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x) + (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x + ((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x)))) := by
  rw [node37_check, Integer.Sparse.eval_merge]
  rw [node30_eval, node36_eval]

theorem node38_check : node38 =
    Integer.Sparse.merge (Integer.Sparse.scale (56758) entry_1_14) (Integer.Sparse.scale (-848390) entry_1_15) := by decide +kernel

theorem node38_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node38 x = (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x + ((-848390 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x) := by
  rw [node38_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node39_check : node39 =
    Integer.Sparse.merge (Integer.Sparse.scale (-65538) entry_1_13) node38 := by decide +kernel

theorem node39_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node39 x = (((-65538 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x + ((-848390 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x)) := by
  rw [node39_check, Integer.Sparse.eval_merge]
  rw [node38_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node40_check : node40 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1894747) entry_1_16) (Integer.Sparse.scale (1697129) entry_1_17) := by decide +kernel

theorem node40_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node40 x = (((-1894747 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + ((1697129 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x) := by
  rw [node40_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node41_check : node41 =
    Integer.Sparse.merge (Integer.Sparse.scale (37861) entry_1_18) (Integer.Sparse.scale (-2357894) entry_1_19) := by decide +kernel

theorem node41_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node41 x = (((37861 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x + ((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x) := by
  rw [node41_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node42_check : node42 =
    Integer.Sparse.merge node40 node41 := by decide +kernel

theorem node42_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node42 x = ((((-1894747 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + ((1697129 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x) + (((37861 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x + ((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x)) := by
  rw [node42_check, Integer.Sparse.eval_merge]
  rw [node40_eval, node41_eval]

theorem node43_check : node43 =
    Integer.Sparse.merge node39 node42 := by decide +kernel

theorem node43_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node43 x = ((((-65538 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x + ((-848390 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x)) + ((((-1894747 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + ((1697129 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x) + (((37861 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x + ((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x))) := by
  rw [node43_check, Integer.Sparse.eval_merge]
  rw [node39_eval, node42_eval]

theorem node44_check : node44 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1198268) entry_1_21) (Integer.Sparse.scale (1132197) entry_1_22) := by decide +kernel

theorem node44_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node44 x = (((-1198268 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_21 x + ((1132197 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_22 x) := by
  rw [node44_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node45_check : node45 =
    Integer.Sparse.merge (Integer.Sparse.scale (-256571) entry_1_20) node44 := by decide +kernel

theorem node45_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node45 x = (((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x + (((-1198268 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_21 x + ((1132197 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_22 x)) := by
  rw [node45_check, Integer.Sparse.eval_merge]
  rw [node44_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node46_check : node46 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1361624) entry_1_23) (Integer.Sparse.scale (449476) entry_1_24) := by decide +kernel

theorem node46_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node46 x = (((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_23 x + ((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_24 x) := by
  rw [node46_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node47_check : node47 =
    Integer.Sparse.merge (Integer.Sparse.scale (312826) entry_1_25) (Integer.Sparse.scale (206227) entry_1_26) := by decide +kernel

theorem node47_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node47 x = (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_25 x + ((206227 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_26 x) := by
  rw [node47_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node48_check : node48 =
    Integer.Sparse.merge node46 node47 := by decide +kernel

theorem node48_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node48 x = ((((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_23 x + ((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_24 x) + (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_25 x + ((206227 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_26 x)) := by
  rw [node48_check, Integer.Sparse.eval_merge]
  rw [node46_eval, node47_eval]

theorem node49_check : node49 =
    Integer.Sparse.merge node45 node48 := by decide +kernel

theorem node49_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node49 x = ((((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x + (((-1198268 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_21 x + ((1132197 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_22 x)) + ((((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_23 x + ((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_24 x) + (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_25 x + ((206227 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_26 x))) := by
  rw [node49_check, Integer.Sparse.eval_merge]
  rw [node45_eval, node48_eval]

theorem node50_check : node50 =
    Integer.Sparse.merge node43 node49 := by decide +kernel

theorem node50_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node50 x = (((((-65538 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x + ((-848390 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x)) + ((((-1894747 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + ((1697129 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x) + (((37861 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x + ((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x))) + ((((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x + (((-1198268 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_21 x + ((1132197 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_22 x)) + ((((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_23 x + ((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_24 x) + (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_25 x + ((206227 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_26 x)))) := by
  rw [node50_check, Integer.Sparse.eval_merge]
  rw [node43_eval, node49_eval]

theorem node51_check : node51 =
    Integer.Sparse.merge node37 node50 := by decide +kernel

theorem node51_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node51 x = ((((((1103969 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + (((944580 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x + ((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x)) + (((-1282119 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + (((95477 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x + ((1215062 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x))) + ((((-564931 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + ((-831071 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x)) + ((((337531 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((-143710 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x) + (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x + ((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x)))) + (((((-65538 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x + ((-848390 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x)) + ((((-1894747 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + ((1697129 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x) + (((37861 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x + ((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x))) + ((((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x + (((-1198268 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_21 x + ((1132197 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_22 x)) + ((((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_23 x + ((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_24 x) + (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_25 x + ((206227 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_26 x))))) := by
  rw [node51_check, Integer.Sparse.eval_merge]
  rw [node37_eval, node50_eval]

theorem node52_check : node52 =
    Integer.Sparse.merge (Integer.Sparse.scale (262232) entry_2_1) (Integer.Sparse.scale (4372564) entry_2_2) := by decide +kernel

theorem node52_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node52 x = (((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x + ((4372564 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x) := by
  rw [node52_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node53_check : node53 =
    Integer.Sparse.merge (Integer.Sparse.scale (-366698) entry_2_0) node52 := by decide +kernel

theorem node53_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node53 x = (((-366698 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + (((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x + ((4372564 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x)) := by
  rw [node53_check, Integer.Sparse.eval_merge]
  rw [node52_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node54_check : node54 =
    Integer.Sparse.merge (Integer.Sparse.scale (-407706) entry_2_4) (Integer.Sparse.scale (2092458) entry_2_5) := by decide +kernel

theorem node54_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node54 x = (((-407706 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x + ((2092458 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x) := by
  rw [node54_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node55_check : node55 =
    Integer.Sparse.merge (Integer.Sparse.scale (3731369) entry_2_3) node54 := by decide +kernel

theorem node55_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node55 x = (((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + (((-407706 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x + ((2092458 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x)) := by
  rw [node55_check, Integer.Sparse.eval_merge]
  rw [node54_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node56_check : node56 =
    Integer.Sparse.merge node53 node55 := by decide +kernel

theorem node56_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node56 x = ((((-366698 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + (((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x + ((4372564 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x)) + (((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + (((-407706 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x + ((2092458 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x))) := by
  rw [node56_check, Integer.Sparse.eval_merge]
  rw [node53_eval, node55_eval]

theorem node57_check : node57 =
    Integer.Sparse.merge (Integer.Sparse.scale (873692) entry_2_7) (Integer.Sparse.scale (-2456751) entry_2_8) := by decide +kernel

theorem node57_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node57 x = (((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + ((-2456751 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x) := by
  rw [node57_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node58_check : node58 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1007026) entry_2_6) node57 := by decide +kernel

theorem node58_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node58 x = (((-1007026 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + (((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + ((-2456751 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x)) := by
  rw [node58_check, Integer.Sparse.eval_merge]
  rw [node57_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node59_check : node59 =
    Integer.Sparse.merge (Integer.Sparse.scale (-216243) entry_2_9) (Integer.Sparse.scale (-1563203) entry_2_10) := by decide +kernel

theorem node59_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node59 x = (((-216243 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((-1563203 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x) := by
  rw [node59_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node60_check : node60 =
    Integer.Sparse.merge (Integer.Sparse.scale (1156547) entry_2_11) (Integer.Sparse.scale (42736) entry_2_12) := by decide +kernel

theorem node60_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node60 x = (((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x) := by
  rw [node60_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node61_check : node61 =
    Integer.Sparse.merge node59 node60 := by decide +kernel

theorem node61_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node61 x = ((((-216243 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((-1563203 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x) + (((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x)) := by
  rw [node61_check, Integer.Sparse.eval_merge]
  rw [node59_eval, node60_eval]

theorem node62_check : node62 =
    Integer.Sparse.merge node58 node61 := by decide +kernel

theorem node62_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node62 x = ((((-1007026 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + (((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + ((-2456751 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x)) + ((((-216243 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((-1563203 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x) + (((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x))) := by
  rw [node62_check, Integer.Sparse.eval_merge]
  rw [node58_eval, node61_eval]

theorem node63_check : node63 =
    Integer.Sparse.merge node56 node62 := by decide +kernel

theorem node63_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node63 x = (((((-366698 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + (((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x + ((4372564 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x)) + (((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + (((-407706 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x + ((2092458 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x))) + ((((-1007026 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + (((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + ((-2456751 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x)) + ((((-216243 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((-1563203 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x) + (((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x)))) := by
  rw [node63_check, Integer.Sparse.eval_merge]
  rw [node56_eval, node62_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node64_check : node64 =
    Integer.Sparse.merge (Integer.Sparse.scale (2315448) entry_2_14) (Integer.Sparse.scale (-2604186) entry_2_15) := by decide +kernel

theorem node64_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node64 x = (((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x + ((-2604186 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x) := by
  rw [node64_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node65_check : node65 =
    Integer.Sparse.merge (Integer.Sparse.scale (737006) entry_2_13) node64 := by decide +kernel

theorem node65_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node65 x = (((737006 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + (((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x + ((-2604186 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x)) := by
  rw [node65_check, Integer.Sparse.eval_merge]
  rw [node64_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node66_check : node66 =
    Integer.Sparse.merge (Integer.Sparse.scale (830681) entry_2_16) (Integer.Sparse.scale (2358685) entry_2_17) := by decide +kernel

theorem node66_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node66 x = (((830681 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + ((2358685 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x) := by
  rw [node66_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node67_check : node67 =
    Integer.Sparse.merge (Integer.Sparse.scale (4672623) entry_2_18) (Integer.Sparse.scale (-140249) entry_2_19) := by decide +kernel

theorem node67_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node67 x = (((4672623 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x) := by
  rw [node67_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node68_check : node68 =
    Integer.Sparse.merge node66 node67 := by decide +kernel

theorem node68_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node68 x = ((((830681 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + ((2358685 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x) + (((4672623 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x)) := by
  rw [node68_check, Integer.Sparse.eval_merge]
  rw [node66_eval, node67_eval]

theorem node69_check : node69 =
    Integer.Sparse.merge node65 node68 := by decide +kernel

theorem node69_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node69 x = ((((737006 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + (((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x + ((-2604186 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x)) + ((((830681 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + ((2358685 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x) + (((4672623 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x))) := by
  rw [node69_check, Integer.Sparse.eval_merge]
  rw [node65_eval, node68_eval]

theorem node70_check : node70 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1590279) entry_2_21) (Integer.Sparse.scale (-234365) entry_2_22) := by decide +kernel

theorem node70_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node70 x = (((-1590279 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_21 x + ((-234365 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_22 x) := by
  rw [node70_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node71_check : node71 =
    Integer.Sparse.merge (Integer.Sparse.scale (456406) entry_2_20) node70 := by decide +kernel

theorem node71_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node71 x = (((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x + (((-1590279 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_21 x + ((-234365 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_22 x)) := by
  rw [node71_check, Integer.Sparse.eval_merge]
  rw [node70_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node72_check : node72 =
    Integer.Sparse.merge (Integer.Sparse.scale (-483957) entry_2_23) (Integer.Sparse.scale (-124524) entry_2_24) := by decide +kernel

theorem node72_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node72 x = (((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_23 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_24 x) := by
  rw [node72_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node73_check : node73 =
    Integer.Sparse.merge (Integer.Sparse.scale (5876220) entry_2_25) (Integer.Sparse.scale (-1320981) entry_2_26) := by decide +kernel

theorem node73_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node73 x = (((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_25 x + ((-1320981 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_26 x) := by
  rw [node73_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node74_check : node74 =
    Integer.Sparse.merge node72 node73 := by decide +kernel

theorem node74_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node74 x = ((((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_23 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_24 x) + (((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_25 x + ((-1320981 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_26 x)) := by
  rw [node74_check, Integer.Sparse.eval_merge]
  rw [node72_eval, node73_eval]

theorem node75_check : node75 =
    Integer.Sparse.merge node71 node74 := by decide +kernel

theorem node75_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node75 x = ((((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x + (((-1590279 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_21 x + ((-234365 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_22 x)) + ((((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_23 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_24 x) + (((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_25 x + ((-1320981 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_26 x))) := by
  rw [node75_check, Integer.Sparse.eval_merge]
  rw [node71_eval, node74_eval]

theorem node76_check : node76 =
    Integer.Sparse.merge node69 node75 := by decide +kernel

theorem node76_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node76 x = (((((737006 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + (((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x + ((-2604186 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x)) + ((((830681 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + ((2358685 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x) + (((4672623 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x))) + ((((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x + (((-1590279 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_21 x + ((-234365 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_22 x)) + ((((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_23 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_24 x) + (((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_25 x + ((-1320981 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_26 x)))) := by
  rw [node76_check, Integer.Sparse.eval_merge]
  rw [node69_eval, node75_eval]

theorem node77_check : node77 =
    Integer.Sparse.merge node63 node76 := by decide +kernel

theorem node77_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node77 x = ((((((-366698 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + (((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x + ((4372564 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x)) + (((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + (((-407706 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x + ((2092458 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x))) + ((((-1007026 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + (((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + ((-2456751 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x)) + ((((-216243 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((-1563203 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x) + (((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x)))) + (((((737006 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + (((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x + ((-2604186 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x)) + ((((830681 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + ((2358685 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x) + (((4672623 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x))) + ((((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x + (((-1590279 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_21 x + ((-234365 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_22 x)) + ((((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_23 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_24 x) + (((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_25 x + ((-1320981 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_26 x))))) := by
  rw [node77_check, Integer.Sparse.eval_merge]
  rw [node63_eval, node76_eval]

theorem node78_check : node78 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1282119) entry_3_1) (Integer.Sparse.scale (3731369) entry_3_2) := by decide +kernel

theorem node78_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node78 x = (((-1282119 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x + ((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x) := by
  rw [node78_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node79_check : node79 =
    Integer.Sparse.merge (Integer.Sparse.scale (4472903) entry_3_0) node78 := by decide +kernel

theorem node79_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node79 x = (((4472903 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + (((-1282119 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x + ((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x)) := by
  rw [node79_check, Integer.Sparse.eval_merge]
  rw [node78_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node80_check : node80 =
    Integer.Sparse.merge (Integer.Sparse.scale (-144329) entry_3_4) (Integer.Sparse.scale (-427246) entry_3_5) := by decide +kernel

theorem node80_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node80 x = (((-144329 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x + ((-427246 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x) := by
  rw [node80_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node81_check : node81 =
    Integer.Sparse.merge (Integer.Sparse.scale (19481819) entry_3_3) node80 := by decide +kernel

theorem node81_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node81 x = (((19481819 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + (((-144329 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x + ((-427246 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x)) := by
  rw [node81_check, Integer.Sparse.eval_merge]
  rw [node80_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node82_check : node82 =
    Integer.Sparse.merge node79 node81 := by decide +kernel

theorem node82_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node82 x = ((((4472903 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + (((-1282119 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x + ((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x)) + (((19481819 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + (((-144329 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x + ((-427246 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x))) := by
  rw [node82_check, Integer.Sparse.eval_merge]
  rw [node79_eval, node81_eval]

theorem node83_check : node83 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1883385) entry_3_7) (Integer.Sparse.scale (-68139) entry_3_8) := by decide +kernel

theorem node83_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node83 x = (((-1883385 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + ((-68139 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x) := by
  rw [node83_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node84_check : node84 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3175977) entry_3_6) node83 := by decide +kernel

theorem node84_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node84 x = (((-3175977 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + (((-1883385 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + ((-68139 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x)) := by
  rw [node84_check, Integer.Sparse.eval_merge]
  rw [node83_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node85_check : node85 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3526786) entry_3_9) (Integer.Sparse.scale (3743961) entry_3_10) := by decide +kernel

theorem node85_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node85 x = (((-3526786 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((3743961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x) := by
  rw [node85_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node86_check : node86 =
    Integer.Sparse.merge (Integer.Sparse.scale (6685420) entry_3_11) (Integer.Sparse.scale (1352597) entry_3_12) := by decide +kernel

theorem node86_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node86 x = (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((1352597 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x) := by
  rw [node86_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node87_check : node87 =
    Integer.Sparse.merge node85 node86 := by decide +kernel

theorem node87_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node87 x = ((((-3526786 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((3743961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x) + (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((1352597 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x)) := by
  rw [node87_check, Integer.Sparse.eval_merge]
  rw [node85_eval, node86_eval]

theorem node88_check : node88 =
    Integer.Sparse.merge node84 node87 := by decide +kernel

theorem node88_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node88 x = ((((-3175977 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + (((-1883385 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + ((-68139 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x)) + ((((-3526786 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((3743961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x) + (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((1352597 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x))) := by
  rw [node88_check, Integer.Sparse.eval_merge]
  rw [node84_eval, node87_eval]

theorem node89_check : node89 =
    Integer.Sparse.merge node82 node88 := by decide +kernel

theorem node89_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node89 x = (((((4472903 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + (((-1282119 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x + ((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x)) + (((19481819 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + (((-144329 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x + ((-427246 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x))) + ((((-3175977 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + (((-1883385 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + ((-68139 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x)) + ((((-3526786 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((3743961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x) + (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((1352597 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x)))) := by
  rw [node89_check, Integer.Sparse.eval_merge]
  rw [node82_eval, node88_eval]

theorem node90_check : node90 =
    Integer.Sparse.merge (Integer.Sparse.scale (2706754) entry_3_14) (Integer.Sparse.scale (-11269051) entry_3_15) := by decide +kernel

theorem node90_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node90 x = (((2706754 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-11269051 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x) := by
  rw [node90_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node91_check : node91 =
    Integer.Sparse.merge (Integer.Sparse.scale (2280274) entry_3_13) node90 := by decide +kernel

theorem node91_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node91 x = (((2280274 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + (((2706754 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-11269051 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x)) := by
  rw [node91_check, Integer.Sparse.eval_merge]
  rw [node90_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node92_check : node92 =
    Integer.Sparse.merge (Integer.Sparse.scale (4787889) entry_3_16) (Integer.Sparse.scale (-3225514) entry_3_17) := by decide +kernel

theorem node92_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node92 x = (((4787889 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((-3225514 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x) := by
  rw [node92_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node93_check : node93 =
    Integer.Sparse.merge (Integer.Sparse.scale (3611637) entry_3_18) (Integer.Sparse.scale (21924365) entry_3_19) := by decide +kernel

theorem node93_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node93 x = (((3611637 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x + ((21924365 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x) := by
  rw [node93_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node94_check : node94 =
    Integer.Sparse.merge node92 node93 := by decide +kernel

theorem node94_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node94 x = ((((4787889 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((-3225514 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x) + (((3611637 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x + ((21924365 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x)) := by
  rw [node94_check, Integer.Sparse.eval_merge]
  rw [node92_eval, node93_eval]

theorem node95_check : node95 =
    Integer.Sparse.merge node91 node94 := by decide +kernel

theorem node95_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node95 x = ((((2280274 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + (((2706754 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-11269051 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x)) + ((((4787889 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((-3225514 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x) + (((3611637 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x + ((21924365 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x))) := by
  rw [node95_check, Integer.Sparse.eval_merge]
  rw [node91_eval, node94_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node96_check : node96 =
    Integer.Sparse.merge (Integer.Sparse.scale (2837114) entry_3_21) (Integer.Sparse.scale (17953246) entry_3_22) := by decide +kernel

theorem node96_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node96 x = (((2837114 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_21 x + ((17953246 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_22 x) := by
  rw [node96_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node97_check : node97 =
    Integer.Sparse.merge (Integer.Sparse.scale (2276614) entry_3_20) node96 := by decide +kernel

theorem node97_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node97 x = (((2276614 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x + (((2837114 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_21 x + ((17953246 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_22 x)) := by
  rw [node97_check, Integer.Sparse.eval_merge]
  rw [node96_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node98_check : node98 =
    Integer.Sparse.merge (Integer.Sparse.scale (-685263) entry_3_23) (Integer.Sparse.scale (1227195) entry_3_24) := by decide +kernel

theorem node98_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node98 x = (((-685263 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_23 x + ((1227195 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_24 x) := by
  rw [node98_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node99_check : node99 =
    Integer.Sparse.merge (Integer.Sparse.scale (2993143) entry_3_25) (Integer.Sparse.scale (-2602804) entry_3_26) := by decide +kernel

theorem node99_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node99 x = (((2993143 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_25 x + ((-2602804 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_26 x) := by
  rw [node99_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node100_check : node100 =
    Integer.Sparse.merge node98 node99 := by decide +kernel

theorem node100_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node100 x = ((((-685263 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_23 x + ((1227195 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_24 x) + (((2993143 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_25 x + ((-2602804 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_26 x)) := by
  rw [node100_check, Integer.Sparse.eval_merge]
  rw [node98_eval, node99_eval]

theorem node101_check : node101 =
    Integer.Sparse.merge node97 node100 := by decide +kernel

theorem node101_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node101 x = ((((2276614 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x + (((2837114 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_21 x + ((17953246 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_22 x)) + ((((-685263 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_23 x + ((1227195 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_24 x) + (((2993143 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_25 x + ((-2602804 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_26 x))) := by
  rw [node101_check, Integer.Sparse.eval_merge]
  rw [node97_eval, node100_eval]

theorem node102_check : node102 =
    Integer.Sparse.merge node95 node101 := by decide +kernel

theorem node102_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node102 x = (((((2280274 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + (((2706754 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-11269051 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x)) + ((((4787889 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((-3225514 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x) + (((3611637 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x + ((21924365 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x))) + ((((2276614 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x + (((2837114 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_21 x + ((17953246 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_22 x)) + ((((-685263 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_23 x + ((1227195 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_24 x) + (((2993143 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_25 x + ((-2602804 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_26 x)))) := by
  rw [node102_check, Integer.Sparse.eval_merge]
  rw [node95_eval, node101_eval]

theorem node103_check : node103 =
    Integer.Sparse.merge node89 node102 := by decide +kernel

theorem node103_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node103 x = ((((((4472903 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + (((-1282119 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x + ((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x)) + (((19481819 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + (((-144329 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x + ((-427246 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x))) + ((((-3175977 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + (((-1883385 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + ((-68139 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x)) + ((((-3526786 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((3743961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x) + (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((1352597 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x)))) + (((((2280274 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + (((2706754 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-11269051 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x)) + ((((4787889 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((-3225514 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x) + (((3611637 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x + ((21924365 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x))) + ((((2276614 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x + (((2837114 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_21 x + ((17953246 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_22 x)) + ((((-685263 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_23 x + ((1227195 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_24 x) + (((2993143 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_25 x + ((-2602804 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_26 x))))) := by
  rw [node103_check, Integer.Sparse.eval_merge]
  rw [node89_eval, node102_eval]

theorem node104_check : node104 =
    Integer.Sparse.merge (Integer.Sparse.scale (95477) entry_4_1) (Integer.Sparse.scale (-407706) entry_4_2) := by decide +kernel

theorem node104_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node104 x = (((95477 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x + ((-407706 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x) := by
  rw [node104_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node105_check : node105 =
    Integer.Sparse.merge (Integer.Sparse.scale (4675758) entry_4_0) node104 := by decide +kernel

theorem node105_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node105 x = (((4675758 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + (((95477 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x + ((-407706 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x)) := by
  rw [node105_check, Integer.Sparse.eval_merge]
  rw [node104_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node106_check : node106 =
    Integer.Sparse.merge (Integer.Sparse.scale (6492797) entry_4_4) (Integer.Sparse.scale (-1491868) entry_4_5) := by decide +kernel

theorem node106_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node106 x = (((6492797 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x + ((-1491868 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x) := by
  rw [node106_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node107_check : node107 =
    Integer.Sparse.merge (Integer.Sparse.scale (-144329) entry_4_3) node106 := by decide +kernel

theorem node107_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node107 x = (((-144329 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + (((6492797 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x + ((-1491868 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x)) := by
  rw [node107_check, Integer.Sparse.eval_merge]
  rw [node106_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node108_check : node108 =
    Integer.Sparse.merge node105 node107 := by decide +kernel

theorem node108_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node108 x = ((((4675758 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + (((95477 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x + ((-407706 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x)) + (((-144329 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + (((6492797 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x + ((-1491868 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x))) := by
  rw [node108_check, Integer.Sparse.eval_merge]
  rw [node105_eval, node107_eval]

theorem node109_check : node109 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4627001) entry_4_7) (Integer.Sparse.scale (7215886) entry_4_8) := by decide +kernel

theorem node109_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node109 x = (((-4627001 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x + ((7215886 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x) := by
  rw [node109_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node110_check : node110 =
    Integer.Sparse.merge (Integer.Sparse.scale (817068) entry_4_6) node109 := by decide +kernel

theorem node110_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node110 x = (((817068 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + (((-4627001 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x + ((7215886 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x)) := by
  rw [node110_check, Integer.Sparse.eval_merge]
  rw [node109_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node111_check : node111 =
    Integer.Sparse.merge (Integer.Sparse.scale (5805250) entry_4_9) (Integer.Sparse.scale (-1305636) entry_4_10) := by decide +kernel

theorem node111_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node111 x = (((5805250 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((-1305636 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x) := by
  rw [node111_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node112_check : node112 =
    Integer.Sparse.merge (Integer.Sparse.scale (2952474) entry_4_11) (Integer.Sparse.scale (3939166) entry_4_12) := by decide +kernel

theorem node112_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node112 x = (((2952474 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x + ((3939166 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_12 x) := by
  rw [node112_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node113_check : node113 =
    Integer.Sparse.merge node111 node112 := by decide +kernel

theorem node113_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node113 x = ((((5805250 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((-1305636 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x) + (((2952474 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x + ((3939166 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_12 x)) := by
  rw [node113_check, Integer.Sparse.eval_merge]
  rw [node111_eval, node112_eval]

theorem node114_check : node114 =
    Integer.Sparse.merge node110 node113 := by decide +kernel

theorem node114_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node114 x = ((((817068 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + (((-4627001 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x + ((7215886 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x)) + ((((5805250 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((-1305636 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x) + (((2952474 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x + ((3939166 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_12 x))) := by
  rw [node114_check, Integer.Sparse.eval_merge]
  rw [node110_eval, node113_eval]

theorem node115_check : node115 =
    Integer.Sparse.merge node108 node114 := by decide +kernel

theorem node115_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node115 x = (((((4675758 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + (((95477 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x + ((-407706 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x)) + (((-144329 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + (((6492797 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x + ((-1491868 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x))) + ((((817068 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + (((-4627001 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x + ((7215886 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x)) + ((((5805250 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((-1305636 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x) + (((2952474 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x + ((3939166 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_12 x)))) := by
  rw [node115_check, Integer.Sparse.eval_merge]
  rw [node108_eval, node114_eval]

theorem node116_check : node116 =
    Integer.Sparse.merge (Integer.Sparse.scale (1532955) entry_4_14) (Integer.Sparse.scale (5894401) entry_4_15) := by decide +kernel

theorem node116_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node116 x = (((1532955 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x + ((5894401 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_15 x) := by
  rw [node116_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node117_check : node117 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1359246) entry_4_13) node116 := by decide +kernel

theorem node117_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node117 x = (((-1359246 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_13 x + (((1532955 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x + ((5894401 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_15 x)) := by
  rw [node117_check, Integer.Sparse.eval_merge]
  rw [node116_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node118_check : node118 =
    Integer.Sparse.merge (Integer.Sparse.scale (-29611) entry_4_16) (Integer.Sparse.scale (6202189) entry_4_17) := by decide +kernel

theorem node118_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node118 x = (((-29611 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_16 x + ((6202189 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x) := by
  rw [node118_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node119_check : node119 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2291217) entry_4_18) (Integer.Sparse.scale (-481138) entry_4_19) := by decide +kernel

theorem node119_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node119 x = (((-2291217 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_18 x + ((-481138 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_19 x) := by
  rw [node119_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node120_check : node120 =
    Integer.Sparse.merge node118 node119 := by decide +kernel

theorem node120_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node120 x = ((((-29611 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_16 x + ((6202189 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x) + (((-2291217 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_18 x + ((-481138 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_19 x)) := by
  rw [node120_check, Integer.Sparse.eval_merge]
  rw [node118_eval, node119_eval]

theorem node121_check : node121 =
    Integer.Sparse.merge node117 node120 := by decide +kernel

theorem node121_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node121 x = ((((-1359246 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_13 x + (((1532955 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x + ((5894401 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_15 x)) + ((((-29611 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_16 x + ((6202189 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x) + (((-2291217 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_18 x + ((-481138 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_19 x))) := by
  rw [node121_check, Integer.Sparse.eval_merge]
  rw [node117_eval, node120_eval]

theorem node122_check : node122 =
    Integer.Sparse.merge (Integer.Sparse.scale (6508035) entry_4_21) (Integer.Sparse.scale (2071984) entry_4_22) := by decide +kernel

theorem node122_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node122 x = (((6508035 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_21 x + ((2071984 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_22 x) := by
  rw [node122_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node123_check : node123 =
    Integer.Sparse.merge (Integer.Sparse.scale (684539) entry_4_20) node122 := by decide +kernel

theorem node123_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node123 x = (((684539 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_20 x + (((6508035 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_21 x + ((2071984 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_22 x)) := by
  rw [node123_check, Integer.Sparse.eval_merge]
  rw [node122_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node124_check : node124 =
    Integer.Sparse.merge (Integer.Sparse.scale (3406557) entry_4_23) (Integer.Sparse.scale (1483542) entry_4_24) := by decide +kernel

theorem node124_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node124 x = (((3406557 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_23 x + ((1483542 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_24 x) := by
  rw [node124_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node125_check : node125 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1112872) entry_4_25) (Integer.Sparse.scale (-1483981) entry_4_26) := by decide +kernel

theorem node125_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node125 x = (((-1112872 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_25 x + ((-1483981 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_26 x) := by
  rw [node125_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node126_check : node126 =
    Integer.Sparse.merge node124 node125 := by decide +kernel

theorem node126_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node126 x = ((((3406557 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_23 x + ((1483542 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_24 x) + (((-1112872 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_25 x + ((-1483981 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_26 x)) := by
  rw [node126_check, Integer.Sparse.eval_merge]
  rw [node124_eval, node125_eval]

theorem node127_check : node127 =
    Integer.Sparse.merge node123 node126 := by decide +kernel

theorem node127_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node127 x = ((((684539 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_20 x + (((6508035 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_21 x + ((2071984 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_22 x)) + ((((3406557 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_23 x + ((1483542 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_24 x) + (((-1112872 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_25 x + ((-1483981 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_26 x))) := by
  rw [node127_check, Integer.Sparse.eval_merge]
  rw [node123_eval, node126_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node128_check : node128 =
    Integer.Sparse.merge node121 node127 := by decide +kernel

theorem node128_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node128 x = (((((-1359246 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_13 x + (((1532955 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x + ((5894401 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_15 x)) + ((((-29611 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_16 x + ((6202189 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x) + (((-2291217 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_18 x + ((-481138 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_19 x))) + ((((684539 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_20 x + (((6508035 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_21 x + ((2071984 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_22 x)) + ((((3406557 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_23 x + ((1483542 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_24 x) + (((-1112872 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_25 x + ((-1483981 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_26 x)))) := by
  rw [node128_check, Integer.Sparse.eval_merge]
  rw [node121_eval, node127_eval]

theorem node129_check : node129 =
    Integer.Sparse.merge node115 node128 := by decide +kernel

theorem node129_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node129 x = ((((((4675758 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + (((95477 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x + ((-407706 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x)) + (((-144329 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + (((6492797 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x + ((-1491868 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x))) + ((((817068 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + (((-4627001 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x + ((7215886 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x)) + ((((5805250 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((-1305636 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x) + (((2952474 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x + ((3939166 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_12 x)))) + (((((-1359246 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_13 x + (((1532955 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x + ((5894401 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_15 x)) + ((((-29611 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_16 x + ((6202189 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x) + (((-2291217 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_18 x + ((-481138 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_19 x))) + ((((684539 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_20 x + (((6508035 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_21 x + ((2071984 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_22 x)) + ((((3406557 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_23 x + ((1483542 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_24 x) + (((-1112872 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_25 x + ((-1483981 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_26 x))))) := by
  rw [node129_check, Integer.Sparse.eval_merge]
  rw [node115_eval, node128_eval]

theorem node156_check : node156 =
    Integer.Sparse.merge (Integer.Sparse.scale (-564931) entry_6_1) (Integer.Sparse.scale (-1007026) entry_6_2) := by decide +kernel

theorem node156_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node156 x = (((-564931 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x + ((-1007026 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x) := by
  rw [node156_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node157_check : node157 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1653142) entry_6_0) node156 := by decide +kernel

theorem node157_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node157 x = (((-1653142 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + (((-564931 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x + ((-1007026 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x)) := by
  rw [node157_check, Integer.Sparse.eval_merge]
  rw [node156_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node158_check : node158 =
    Integer.Sparse.merge (Integer.Sparse.scale (817068) entry_6_4) (Integer.Sparse.scale (-614723) entry_6_5) := by decide +kernel

theorem node158_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node158 x = (((817068 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x + ((-614723 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x) := by
  rw [node158_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node159_check : node159 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3175977) entry_6_3) node158 := by decide +kernel

theorem node159_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node159 x = (((-3175977 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + (((817068 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x + ((-614723 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x)) := by
  rw [node159_check, Integer.Sparse.eval_merge]
  rw [node158_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node160_check : node160 =
    Integer.Sparse.merge node157 node159 := by decide +kernel

theorem node160_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node160 x = ((((-1653142 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + (((-564931 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x + ((-1007026 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x)) + (((-3175977 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + (((817068 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x + ((-614723 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x))) := by
  rw [node160_check, Integer.Sparse.eval_merge]
  rw [node157_eval, node159_eval]

theorem node161_check : node161 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1569264) entry_6_7) (Integer.Sparse.scale (3004866) entry_6_8) := by decide +kernel

theorem node161_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node161 x = (((-1569264 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((3004866 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x) := by
  rw [node161_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node162_check : node162 =
    Integer.Sparse.merge (Integer.Sparse.scale (3480564) entry_6_6) node161 := by decide +kernel

theorem node162_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node162 x = (((3480564 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + (((-1569264 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((3004866 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x)) := by
  rw [node162_check, Integer.Sparse.eval_merge]
  rw [node161_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node163_check : node163 =
    Integer.Sparse.merge (Integer.Sparse.scale (1839889) entry_6_9) (Integer.Sparse.scale (-1954425) entry_6_10) := by decide +kernel

theorem node163_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node163 x = (((1839889 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((-1954425 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x) := by
  rw [node163_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node164_check : node164 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3083192) entry_6_11) (Integer.Sparse.scale (-381717) entry_6_12) := by decide +kernel

theorem node164_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node164 x = (((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x + ((-381717 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x) := by
  rw [node164_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node165_check : node165 =
    Integer.Sparse.merge node163 node164 := by decide +kernel

theorem node165_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node165 x = ((((1839889 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((-1954425 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x) + (((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x + ((-381717 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x)) := by
  rw [node165_check, Integer.Sparse.eval_merge]
  rw [node163_eval, node164_eval]

theorem node166_check : node166 =
    Integer.Sparse.merge node162 node165 := by decide +kernel

theorem node166_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node166 x = ((((3480564 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + (((-1569264 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((3004866 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x)) + ((((1839889 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((-1954425 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x) + (((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x + ((-381717 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x))) := by
  rw [node166_check, Integer.Sparse.eval_merge]
  rw [node162_eval, node165_eval]

theorem node167_check : node167 =
    Integer.Sparse.merge node160 node166 := by decide +kernel

theorem node167_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node167 x = (((((-1653142 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + (((-564931 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x + ((-1007026 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x)) + (((-3175977 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + (((817068 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x + ((-614723 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x))) + ((((3480564 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + (((-1569264 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((3004866 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x)) + ((((1839889 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((-1954425 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x) + (((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x + ((-381717 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x)))) := by
  rw [node167_check, Integer.Sparse.eval_merge]
  rw [node160_eval, node166_eval]

theorem node168_check : node168 =
    Integer.Sparse.merge (Integer.Sparse.scale (548165) entry_6_14) (Integer.Sparse.scale (7957870) entry_6_15) := by decide +kernel

theorem node168_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node168 x = (((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x + ((7957870 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x) := by
  rw [node168_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node169_check : node169 =
    Integer.Sparse.merge (Integer.Sparse.scale (-777936) entry_6_13) node168 := by decide +kernel

theorem node169_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node169 x = (((-777936 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + (((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x + ((7957870 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x)) := by
  rw [node169_check, Integer.Sparse.eval_merge]
  rw [node168_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node170_check : node170 =
    Integer.Sparse.merge (Integer.Sparse.scale (1340972) entry_6_16) (Integer.Sparse.scale (1639448) entry_6_17) := by decide +kernel

theorem node170_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node170 x = (((1340972 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + ((1639448 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x) := by
  rw [node170_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node171_check : node171 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1148157) entry_6_18) (Integer.Sparse.scale (-5852439) entry_6_19) := by decide +kernel

theorem node171_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node171 x = (((-1148157 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x + ((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x) := by
  rw [node171_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node172_check : node172 =
    Integer.Sparse.merge node170 node171 := by decide +kernel

theorem node172_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node172 x = ((((1340972 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + ((1639448 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x) + (((-1148157 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x + ((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x)) := by
  rw [node172_check, Integer.Sparse.eval_merge]
  rw [node170_eval, node171_eval]

theorem node173_check : node173 =
    Integer.Sparse.merge node169 node172 := by decide +kernel

theorem node173_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node173 x = ((((-777936 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + (((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x + ((7957870 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x)) + ((((1340972 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + ((1639448 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x) + (((-1148157 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x + ((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x))) := by
  rw [node173_check, Integer.Sparse.eval_merge]
  rw [node169_eval, node172_eval]

theorem node174_check : node174 =
    Integer.Sparse.merge (Integer.Sparse.scale (3554996) entry_6_21) (Integer.Sparse.scale (-10414524) entry_6_22) := by decide +kernel

theorem node174_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node174 x = (((3554996 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_21 x + ((-10414524 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_22 x) := by
  rw [node174_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node175_check : node175 =
    Integer.Sparse.merge (Integer.Sparse.scale (-380245) entry_6_20) node174 := by decide +kernel

theorem node175_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node175 x = (((-380245 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x + (((3554996 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_21 x + ((-10414524 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_22 x)) := by
  rw [node175_check, Integer.Sparse.eval_merge]
  rw [node174_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node176_check : node176 =
    Integer.Sparse.merge (Integer.Sparse.scale (2933849) entry_6_23) (Integer.Sparse.scale (-467475) entry_6_24) := by decide +kernel

theorem node176_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node176 x = (((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_23 x + ((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_24 x) := by
  rw [node176_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node177_check : node177 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1973233) entry_6_25) (Integer.Sparse.scale (-1032694) entry_6_26) := by decide +kernel

theorem node177_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node177 x = (((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_25 x + ((-1032694 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_26 x) := by
  rw [node177_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node178_check : node178 =
    Integer.Sparse.merge node176 node177 := by decide +kernel

theorem node178_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node178 x = ((((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_23 x + ((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_24 x) + (((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_25 x + ((-1032694 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_26 x)) := by
  rw [node178_check, Integer.Sparse.eval_merge]
  rw [node176_eval, node177_eval]

theorem node179_check : node179 =
    Integer.Sparse.merge node175 node178 := by decide +kernel

theorem node179_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node179 x = ((((-380245 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x + (((3554996 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_21 x + ((-10414524 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_22 x)) + ((((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_23 x + ((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_24 x) + (((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_25 x + ((-1032694 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_26 x))) := by
  rw [node179_check, Integer.Sparse.eval_merge]
  rw [node175_eval, node178_eval]

theorem node180_check : node180 =
    Integer.Sparse.merge node173 node179 := by decide +kernel

theorem node180_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node180 x = (((((-777936 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + (((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x + ((7957870 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x)) + ((((1340972 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + ((1639448 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x) + (((-1148157 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x + ((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x))) + ((((-380245 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x + (((3554996 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_21 x + ((-10414524 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_22 x)) + ((((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_23 x + ((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_24 x) + (((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_25 x + ((-1032694 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_26 x)))) := by
  rw [node180_check, Integer.Sparse.eval_merge]
  rw [node173_eval, node179_eval]

theorem node181_check : node181 =
    Integer.Sparse.merge node167 node180 := by decide +kernel

theorem node181_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node181 x = ((((((-1653142 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + (((-564931 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x + ((-1007026 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x)) + (((-3175977 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + (((817068 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x + ((-614723 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x))) + ((((3480564 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + (((-1569264 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x + ((3004866 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x)) + ((((1839889 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((-1954425 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x) + (((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x + ((-381717 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x)))) + (((((-777936 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + (((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x + ((7957870 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x)) + ((((1340972 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + ((1639448 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x) + (((-1148157 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x + ((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x))) + ((((-380245 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x + (((3554996 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_21 x + ((-10414524 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_22 x)) + ((((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_23 x + ((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_24 x) + (((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_25 x + ((-1032694 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_26 x))))) := by
  rw [node181_check, Integer.Sparse.eval_merge]
  rw [node167_eval, node180_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node260_check : node260 =
    Integer.Sparse.merge (Integer.Sparse.scale (-143710) entry_10_1) (Integer.Sparse.scale (-1563203) entry_10_2) := by decide +kernel

theorem node260_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node260 x = (((-143710 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x + ((-1563203 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x) := by
  rw [node260_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node261_check : node261 =
    Integer.Sparse.merge (Integer.Sparse.scale (4676581) entry_10_0) node260 := by decide +kernel

theorem node261_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node261 x = (((4676581 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + (((-143710 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x + ((-1563203 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x)) := by
  rw [node261_check, Integer.Sparse.eval_merge]
  rw [node260_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node262_check : node262 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1305636) entry_10_4) (Integer.Sparse.scale (469732) entry_10_5) := by decide +kernel

theorem node262_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node262 x = (((-1305636 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x + ((469732 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x) := by
  rw [node262_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node263_check : node263 =
    Integer.Sparse.merge (Integer.Sparse.scale (3743961) entry_10_3) node262 := by decide +kernel

theorem node263_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node263 x = (((3743961 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + (((-1305636 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x + ((469732 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x)) := by
  rw [node263_check, Integer.Sparse.eval_merge]
  rw [node262_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node264_check : node264 =
    Integer.Sparse.merge node261 node263 := by decide +kernel

theorem node264_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node264 x = ((((4676581 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + (((-143710 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x + ((-1563203 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x)) + (((3743961 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + (((-1305636 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x + ((469732 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x))) := by
  rw [node264_check, Integer.Sparse.eval_merge]
  rw [node261_eval, node263_eval]

theorem node265_check : node265 =
    Integer.Sparse.merge (Integer.Sparse.scale (118611) entry_10_7) (Integer.Sparse.scale (909816) entry_10_8) := by decide +kernel

theorem node265_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node265 x = (((118611 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + ((909816 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x) := by
  rw [node265_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node266_check : node266 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1954425) entry_10_6) node265 := by decide +kernel

theorem node266_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node266 x = (((-1954425 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + (((118611 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + ((909816 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x)) := by
  rw [node266_check, Integer.Sparse.eval_merge]
  rw [node265_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node267_check : node267 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2924799) entry_10_9) (Integer.Sparse.scale (7987018) entry_10_10) := by decide +kernel

theorem node267_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node267 x = (((-2924799 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + ((7987018 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x) := by
  rw [node267_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node268_check : node268 =
    Integer.Sparse.merge (Integer.Sparse.scale (2298496) entry_10_11) (Integer.Sparse.scale (670012) entry_10_12) := by decide +kernel

theorem node268_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node268 x = (((2298496 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x + ((670012 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_12 x) := by
  rw [node268_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node269_check : node269 =
    Integer.Sparse.merge node267 node268 := by decide +kernel

theorem node269_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node269 x = ((((-2924799 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + ((7987018 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x) + (((2298496 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x + ((670012 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_12 x)) := by
  rw [node269_check, Integer.Sparse.eval_merge]
  rw [node267_eval, node268_eval]

theorem node270_check : node270 =
    Integer.Sparse.merge node266 node269 := by decide +kernel

theorem node270_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node270 x = ((((-1954425 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + (((118611 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + ((909816 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x)) + ((((-2924799 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + ((7987018 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x) + (((2298496 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x + ((670012 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_12 x))) := by
  rw [node270_check, Integer.Sparse.eval_merge]
  rw [node266_eval, node269_eval]

theorem node271_check : node271 =
    Integer.Sparse.merge node264 node270 := by decide +kernel

theorem node271_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node271 x = (((((4676581 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + (((-143710 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x + ((-1563203 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x)) + (((3743961 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + (((-1305636 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x + ((469732 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x))) + ((((-1954425 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + (((118611 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + ((909816 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x)) + ((((-2924799 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + ((7987018 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x) + (((2298496 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x + ((670012 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_12 x)))) := by
  rw [node271_check, Integer.Sparse.eval_merge]
  rw [node264_eval, node270_eval]

theorem node272_check : node272 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1536421) entry_10_14) (Integer.Sparse.scale (-6516193) entry_10_15) := by decide +kernel

theorem node272_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node272 x = (((-1536421 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_14 x + ((-6516193 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_15 x) := by
  rw [node272_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node273_check : node273 =
    Integer.Sparse.merge (Integer.Sparse.scale (1060859) entry_10_13) node272 := by decide +kernel

theorem node273_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node273 x = (((1060859 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_13 x + (((-1536421 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_14 x + ((-6516193 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_15 x)) := by
  rw [node273_check, Integer.Sparse.eval_merge]
  rw [node272_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node274_check : node274 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3482292) entry_10_16) (Integer.Sparse.scale (-6804900) entry_10_17) := by decide +kernel

theorem node274_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node274 x = (((-3482292 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_16 x + ((-6804900 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_17 x) := by
  rw [node274_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node275_check : node275 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6889389) entry_10_18) (Integer.Sparse.scale (9482366) entry_10_19) := by decide +kernel

theorem node275_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node275 x = (((-6889389 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_18 x + ((9482366 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_19 x) := by
  rw [node275_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node276_check : node276 =
    Integer.Sparse.merge node274 node275 := by decide +kernel

theorem node276_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node276 x = ((((-3482292 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_16 x + ((-6804900 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_17 x) + (((-6889389 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_18 x + ((9482366 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_19 x)) := by
  rw [node276_check, Integer.Sparse.eval_merge]
  rw [node274_eval, node275_eval]

theorem node277_check : node277 =
    Integer.Sparse.merge node273 node276 := by decide +kernel

theorem node277_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node277 x = ((((1060859 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_13 x + (((-1536421 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_14 x + ((-6516193 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_15 x)) + ((((-3482292 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_16 x + ((-6804900 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_17 x) + (((-6889389 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_18 x + ((9482366 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_19 x))) := by
  rw [node277_check, Integer.Sparse.eval_merge]
  rw [node273_eval, node276_eval]

theorem node278_check : node278 =
    Integer.Sparse.merge (Integer.Sparse.scale (1772760) entry_10_21) (Integer.Sparse.scale (18979737) entry_10_22) := by decide +kernel

theorem node278_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node278 x = (((1772760 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_21 x + ((18979737 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_22 x) := by
  rw [node278_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node279_check : node279 =
    Integer.Sparse.merge (Integer.Sparse.scale (-31994) entry_10_20) node278 := by decide +kernel

theorem node279_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node279 x = (((-31994 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_20 x + (((1772760 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_21 x + ((18979737 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_22 x)) := by
  rw [node279_check, Integer.Sparse.eval_merge]
  rw [node278_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node280_check : node280 =
    Integer.Sparse.merge (Integer.Sparse.scale (-5584492) entry_10_23) (Integer.Sparse.scale (2189272) entry_10_24) := by decide +kernel

theorem node280_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node280 x = (((-5584492 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_23 x + ((2189272 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_24 x) := by
  rw [node280_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node281_check : node281 =
    Integer.Sparse.merge (Integer.Sparse.scale (-9602945) entry_10_25) (Integer.Sparse.scale (-1745575) entry_10_26) := by decide +kernel

theorem node281_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node281 x = (((-9602945 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_25 x + ((-1745575 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_26 x) := by
  rw [node281_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node282_check : node282 =
    Integer.Sparse.merge node280 node281 := by decide +kernel

theorem node282_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node282 x = ((((-5584492 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_23 x + ((2189272 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_24 x) + (((-9602945 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_25 x + ((-1745575 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_26 x)) := by
  rw [node282_check, Integer.Sparse.eval_merge]
  rw [node280_eval, node281_eval]

theorem node283_check : node283 =
    Integer.Sparse.merge node279 node282 := by decide +kernel

theorem node283_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node283 x = ((((-31994 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_20 x + (((1772760 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_21 x + ((18979737 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_22 x)) + ((((-5584492 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_23 x + ((2189272 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_24 x) + (((-9602945 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_25 x + ((-1745575 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_26 x))) := by
  rw [node283_check, Integer.Sparse.eval_merge]
  rw [node279_eval, node282_eval]

theorem node284_check : node284 =
    Integer.Sparse.merge node277 node283 := by decide +kernel

theorem node284_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node284 x = (((((1060859 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_13 x + (((-1536421 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_14 x + ((-6516193 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_15 x)) + ((((-3482292 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_16 x + ((-6804900 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_17 x) + (((-6889389 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_18 x + ((9482366 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_19 x))) + ((((-31994 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_20 x + (((1772760 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_21 x + ((18979737 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_22 x)) + ((((-5584492 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_23 x + ((2189272 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_24 x) + (((-9602945 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_25 x + ((-1745575 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_26 x)))) := by
  rw [node284_check, Integer.Sparse.eval_merge]
  rw [node277_eval, node283_eval]

theorem node285_check : node285 =
    Integer.Sparse.merge node271 node284 := by decide +kernel

theorem node285_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node285 x = ((((((4676581 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + (((-143710 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x + ((-1563203 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x)) + (((3743961 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + (((-1305636 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x + ((469732 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x))) + ((((-1954425 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + (((118611 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + ((909816 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x)) + ((((-2924799 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + ((7987018 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x) + (((2298496 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x + ((670012 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_12 x)))) + (((((1060859 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_13 x + (((-1536421 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_14 x + ((-6516193 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_15 x)) + ((((-3482292 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_16 x + ((-6804900 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_17 x) + (((-6889389 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_18 x + ((9482366 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_19 x))) + ((((-31994 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_20 x + (((1772760 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_21 x + ((18979737 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_22 x)) + ((((-5584492 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_23 x + ((2189272 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_24 x) + (((-9602945 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_25 x + ((-1745575 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_26 x))))) := by
  rw [node285_check, Integer.Sparse.eval_merge]
  rw [node271_eval, node284_eval]

theorem node286_check : node286 =
    Integer.Sparse.merge (Integer.Sparse.scale (302472) entry_11_1) (Integer.Sparse.scale (1156547) entry_11_2) := by decide +kernel

theorem node286_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node286 x = (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x + ((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x) := by
  rw [node286_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node287_check : node287 =
    Integer.Sparse.merge (Integer.Sparse.scale (5623964) entry_11_0) node286 := by decide +kernel

theorem node287_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node287 x = (((5623964 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x + ((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x)) := by
  rw [node287_check, Integer.Sparse.eval_merge]
  rw [node286_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node288_check : node288 =
    Integer.Sparse.merge (Integer.Sparse.scale (2952474) entry_11_4) (Integer.Sparse.scale (-959011) entry_11_5) := by decide +kernel

theorem node288_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node288 x = (((2952474 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-959011 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x) := by
  rw [node288_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node289_check : node289 =
    Integer.Sparse.merge (Integer.Sparse.scale (6685420) entry_11_3) node288 := by decide +kernel

theorem node289_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node289 x = (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + (((2952474 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-959011 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x)) := by
  rw [node289_check, Integer.Sparse.eval_merge]
  rw [node288_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node290_check : node290 =
    Integer.Sparse.merge node287 node289 := by decide +kernel

theorem node290_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node290 x = ((((5623964 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x + ((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x)) + (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + (((2952474 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-959011 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x))) := by
  rw [node290_check, Integer.Sparse.eval_merge]
  rw [node287_eval, node289_eval]

theorem node291_check : node291 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3301327) entry_11_7) (Integer.Sparse.scale (2492242) entry_11_8) := by decide +kernel

theorem node291_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node291 x = (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + ((2492242 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x) := by
  rw [node291_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node292_check : node292 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3083192) entry_11_6) node291 := by decide +kernel

theorem node292_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node292 x = (((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + ((2492242 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x)) := by
  rw [node292_check, Integer.Sparse.eval_merge]
  rw [node291_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node293_check : node293 =
    Integer.Sparse.merge (Integer.Sparse.scale (3946206) entry_11_9) (Integer.Sparse.scale (2298496) entry_11_10) := by decide +kernel

theorem node293_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node293 x = (((3946206 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + ((2298496 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x) := by
  rw [node293_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node294_check : node294 =
    Integer.Sparse.merge (Integer.Sparse.scale (11293001) entry_11_11) (Integer.Sparse.scale (3855450) entry_11_12) := by decide +kernel

theorem node294_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node294 x = (((11293001 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x + ((3855450 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x) := by
  rw [node294_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node295_check : node295 =
    Integer.Sparse.merge node293 node294 := by decide +kernel

theorem node295_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node295 x = ((((3946206 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + ((2298496 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x) + (((11293001 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x + ((3855450 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x)) := by
  rw [node295_check, Integer.Sparse.eval_merge]
  rw [node293_eval, node294_eval]

theorem node296_check : node296 =
    Integer.Sparse.merge node292 node295 := by decide +kernel

theorem node296_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node296 x = ((((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + ((2492242 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x)) + ((((3946206 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + ((2298496 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x) + (((11293001 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x + ((3855450 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x))) := by
  rw [node296_check, Integer.Sparse.eval_merge]
  rw [node292_eval, node295_eval]

theorem node297_check : node297 =
    Integer.Sparse.merge node290 node296 := by decide +kernel

theorem node297_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node297 x = (((((5623964 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x + ((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x)) + (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + (((2952474 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-959011 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x))) + ((((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + ((2492242 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x)) + ((((3946206 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + ((2298496 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x) + (((11293001 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x + ((3855450 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x)))) := by
  rw [node297_check, Integer.Sparse.eval_merge]
  rw [node290_eval, node296_eval]

theorem node298_check : node298 =
    Integer.Sparse.merge (Integer.Sparse.scale (919586) entry_11_14) (Integer.Sparse.scale (-1479887) entry_11_15) := by decide +kernel

theorem node298_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node298 x = (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x + ((-1479887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x) := by
  rw [node298_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node299_check : node299 =
    Integer.Sparse.merge (Integer.Sparse.scale (207606) entry_11_13) node298 := by decide +kernel

theorem node299_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node299 x = (((207606 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x + ((-1479887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x)) := by
  rw [node299_check, Integer.Sparse.eval_merge]
  rw [node298_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node300_check : node300 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1937263) entry_11_16) (Integer.Sparse.scale (3041223) entry_11_17) := by decide +kernel

theorem node300_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node300 x = (((-1937263 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + ((3041223 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x) := by
  rw [node300_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node301_check : node301 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1958480) entry_11_18) (Integer.Sparse.scale (5974596) entry_11_19) := by decide +kernel

theorem node301_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node301 x = (((-1958480 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x + ((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x) := by
  rw [node301_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node302_check : node302 =
    Integer.Sparse.merge node300 node301 := by decide +kernel

theorem node302_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node302 x = ((((-1937263 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + ((3041223 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x) + (((-1958480 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x + ((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x)) := by
  rw [node302_check, Integer.Sparse.eval_merge]
  rw [node300_eval, node301_eval]

theorem node303_check : node303 =
    Integer.Sparse.merge node299 node302 := by decide +kernel

theorem node303_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node303 x = ((((207606 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x + ((-1479887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x)) + ((((-1937263 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + ((3041223 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x) + (((-1958480 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x + ((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x))) := by
  rw [node303_check, Integer.Sparse.eval_merge]
  rw [node299_eval, node302_eval]

theorem node304_check : node304 =
    Integer.Sparse.merge (Integer.Sparse.scale (4701210) entry_11_21) (Integer.Sparse.scale (16943621) entry_11_22) := by decide +kernel

theorem node304_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node304 x = (((4701210 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_21 x + ((16943621 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_22 x) := by
  rw [node304_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node305_check : node305 =
    Integer.Sparse.merge (Integer.Sparse.scale (1576779) entry_11_20) node304 := by decide +kernel

theorem node305_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node305 x = (((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x + (((4701210 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_21 x + ((16943621 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_22 x)) := by
  rw [node305_check, Integer.Sparse.eval_merge]
  rw [node304_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node306_check : node306 =
    Integer.Sparse.merge (Integer.Sparse.scale (-736999) entry_11_23) (Integer.Sparse.scale (2493931) entry_11_24) := by decide +kernel

theorem node306_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node306 x = (((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_23 x + ((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_24 x) := by
  rw [node306_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node307_check : node307 =
    Integer.Sparse.merge (Integer.Sparse.scale (458016) entry_11_25) (Integer.Sparse.scale (-1738479) entry_11_26) := by decide +kernel

theorem node307_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node307 x = (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_25 x + ((-1738479 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_26 x) := by
  rw [node307_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node308_check : node308 =
    Integer.Sparse.merge node306 node307 := by decide +kernel

theorem node308_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node308 x = ((((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_23 x + ((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_24 x) + (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_25 x + ((-1738479 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_26 x)) := by
  rw [node308_check, Integer.Sparse.eval_merge]
  rw [node306_eval, node307_eval]

theorem node309_check : node309 =
    Integer.Sparse.merge node305 node308 := by decide +kernel

theorem node309_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node309 x = ((((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x + (((4701210 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_21 x + ((16943621 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_22 x)) + ((((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_23 x + ((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_24 x) + (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_25 x + ((-1738479 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_26 x))) := by
  rw [node309_check, Integer.Sparse.eval_merge]
  rw [node305_eval, node308_eval]

theorem node310_check : node310 =
    Integer.Sparse.merge node303 node309 := by decide +kernel

theorem node310_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node310 x = (((((207606 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x + ((-1479887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x)) + ((((-1937263 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + ((3041223 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x) + (((-1958480 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x + ((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x))) + ((((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x + (((4701210 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_21 x + ((16943621 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_22 x)) + ((((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_23 x + ((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_24 x) + (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_25 x + ((-1738479 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_26 x)))) := by
  rw [node310_check, Integer.Sparse.eval_merge]
  rw [node303_eval, node309_eval]

theorem node311_check : node311 =
    Integer.Sparse.merge node297 node310 := by decide +kernel

theorem node311_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node311 x = ((((((5623964 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x + ((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x)) + (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + (((2952474 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-959011 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x))) + ((((-3083192 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + ((2492242 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x)) + ((((3946206 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_9 x + ((2298496 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_10 x) + (((11293001 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_11 x + ((3855450 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_12 x)))) + (((((207606 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_13 x + (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_14 x + ((-1479887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_15 x)) + ((((-1937263 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_16 x + ((3041223 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_17 x) + (((-1958480 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_18 x + ((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_19 x))) + ((((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_20 x + (((4701210 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_21 x + ((16943621 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_22 x)) + ((((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_23 x + ((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_24 x) + (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_25 x + ((-1738479 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_26 x))))) := by
  rw [node311_check, Integer.Sparse.eval_merge]
  rw [node297_eval, node310_eval]

theorem node312_check : node312 =
    Integer.Sparse.merge (Integer.Sparse.scale (204411) entry_12_1) (Integer.Sparse.scale (42736) entry_12_2) := by decide +kernel

theorem node312_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node312 x = (((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_1 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_2 x) := by
  rw [node312_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node313_check : node313 =
    Integer.Sparse.merge (Integer.Sparse.scale (8331635) entry_12_0) node312 := by decide +kernel

theorem node313_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node313 x = (((8331635 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_0 x + (((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_1 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_2 x)) := by
  rw [node313_check, Integer.Sparse.eval_merge]
  rw [node312_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node314_check : node314 =
    Integer.Sparse.merge (Integer.Sparse.scale (3939166) entry_12_4) (Integer.Sparse.scale (-1289212) entry_12_5) := by decide +kernel

theorem node314_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node314 x = (((3939166 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x + ((-1289212 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_5 x) := by
  rw [node314_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node315_check : node315 =
    Integer.Sparse.merge (Integer.Sparse.scale (1352597) entry_12_3) node314 := by decide +kernel

theorem node315_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node315 x = (((1352597 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_3 x + (((3939166 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x + ((-1289212 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_5 x)) := by
  rw [node315_check, Integer.Sparse.eval_merge]
  rw [node314_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node316_check : node316 =
    Integer.Sparse.merge node313 node315 := by decide +kernel

theorem node316_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node316 x = ((((8331635 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_0 x + (((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_1 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_2 x)) + (((1352597 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_3 x + (((3939166 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x + ((-1289212 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_5 x))) := by
  rw [node316_check, Integer.Sparse.eval_merge]
  rw [node313_eval, node315_eval]

theorem node317_check : node317 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3540810) entry_12_7) (Integer.Sparse.scale (4317945) entry_12_8) := by decide +kernel

theorem node317_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node317 x = (((-3540810 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_7 x + ((4317945 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_8 x) := by
  rw [node317_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node318_check : node318 =
    Integer.Sparse.merge (Integer.Sparse.scale (-381717) entry_12_6) node317 := by decide +kernel

theorem node318_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node318 x = (((-381717 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_6 x + (((-3540810 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_7 x + ((4317945 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_8 x)) := by
  rw [node318_check, Integer.Sparse.eval_merge]
  rw [node317_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node319_check : node319 =
    Integer.Sparse.merge (Integer.Sparse.scale (5011875) entry_12_9) (Integer.Sparse.scale (670012) entry_12_10) := by decide +kernel

theorem node319_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node319 x = (((5011875 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_9 x + ((670012 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_10 x) := by
  rw [node319_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node320_check : node320 =
    Integer.Sparse.merge (Integer.Sparse.scale (3855450) entry_12_11) (Integer.Sparse.scale (5397378) entry_12_12) := by decide +kernel

theorem node320_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node320 x = (((3855450 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_11 x + ((5397378 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_12 x) := by
  rw [node320_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node321_check : node321 =
    Integer.Sparse.merge node319 node320 := by decide +kernel

theorem node321_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node321 x = ((((5011875 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_9 x + ((670012 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_10 x) + (((3855450 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_11 x + ((5397378 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_12 x)) := by
  rw [node321_check, Integer.Sparse.eval_merge]
  rw [node319_eval, node320_eval]

theorem node322_check : node322 =
    Integer.Sparse.merge node318 node321 := by decide +kernel

theorem node322_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node322 x = ((((-381717 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_6 x + (((-3540810 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_7 x + ((4317945 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_8 x)) + ((((5011875 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_9 x + ((670012 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_10 x) + (((3855450 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_11 x + ((5397378 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_12 x))) := by
  rw [node322_check, Integer.Sparse.eval_merge]
  rw [node318_eval, node321_eval]

theorem node323_check : node323 =
    Integer.Sparse.merge node316 node322 := by decide +kernel

theorem node323_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node323 x = (((((8331635 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_0 x + (((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_1 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_2 x)) + (((1352597 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_3 x + (((3939166 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x + ((-1289212 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_5 x))) + ((((-381717 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_6 x + (((-3540810 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_7 x + ((4317945 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_8 x)) + ((((5011875 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_9 x + ((670012 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_10 x) + (((3855450 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_11 x + ((5397378 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_12 x)))) := by
  rw [node323_check, Integer.Sparse.eval_merge]
  rw [node316_eval, node322_eval]

theorem node324_check : node324 =
    Integer.Sparse.merge (Integer.Sparse.scale (962591) entry_12_14) (Integer.Sparse.scale (2637949) entry_12_15) := by decide +kernel

theorem node324_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node324 x = (((962591 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_14 x + ((2637949 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_15 x) := by
  rw [node324_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node325_check : node325 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1102075) entry_12_13) node324 := by decide +kernel

theorem node325_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node325 x = (((-1102075 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_13 x + (((962591 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_14 x + ((2637949 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_15 x)) := by
  rw [node325_check, Integer.Sparse.eval_merge]
  rw [node324_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node326_check : node326 =
    Integer.Sparse.merge (Integer.Sparse.scale (188406) entry_12_16) (Integer.Sparse.scale (4768294) entry_12_17) := by decide +kernel

theorem node326_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node326 x = (((188406 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_16 x + ((4768294 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_17 x) := by
  rw [node326_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node327_check : node327 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3725397) entry_12_18) (Integer.Sparse.scale (446791) entry_12_19) := by decide +kernel

theorem node327_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node327 x = (((-3725397 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_18 x + ((446791 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_19 x) := by
  rw [node327_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node328_check : node328 =
    Integer.Sparse.merge node326 node327 := by decide +kernel

theorem node328_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node328 x = ((((188406 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_16 x + ((4768294 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_17 x) + (((-3725397 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_18 x + ((446791 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_19 x)) := by
  rw [node328_check, Integer.Sparse.eval_merge]
  rw [node326_eval, node327_eval]

theorem node329_check : node329 =
    Integer.Sparse.merge node325 node328 := by decide +kernel

theorem node329_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node329 x = ((((-1102075 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_13 x + (((962591 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_14 x + ((2637949 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_15 x)) + ((((188406 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_16 x + ((4768294 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_17 x) + (((-3725397 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_18 x + ((446791 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_19 x))) := by
  rw [node329_check, Integer.Sparse.eval_merge]
  rw [node325_eval, node328_eval]

theorem node330_check : node330 =
    Integer.Sparse.merge (Integer.Sparse.scale (7981741) entry_12_21) (Integer.Sparse.scale (9023959) entry_12_22) := by decide +kernel

theorem node330_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node330 x = (((7981741 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_21 x + ((9023959 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_22 x) := by
  rw [node330_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node331_check : node331 =
    Integer.Sparse.merge (Integer.Sparse.scale (474966) entry_12_20) node330 := by decide +kernel

theorem node331_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node331 x = (((474966 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_20 x + (((7981741 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_21 x + ((9023959 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_22 x)) := by
  rw [node331_check, Integer.Sparse.eval_merge]
  rw [node330_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node332_check : node332 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1518183) entry_12_23) (Integer.Sparse.scale (1177088) entry_12_24) := by decide +kernel

theorem node332_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node332 x = (((-1518183 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_23 x + ((1177088 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_24 x) := by
  rw [node332_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node333_check : node333 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3205049) entry_12_25) (Integer.Sparse.scale (-1956856) entry_12_26) := by decide +kernel

theorem node333_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node333 x = (((-3205049 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_25 x + ((-1956856 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_26 x) := by
  rw [node333_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node334_check : node334 =
    Integer.Sparse.merge node332 node333 := by decide +kernel

theorem node334_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node334 x = ((((-1518183 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_23 x + ((1177088 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_24 x) + (((-3205049 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_25 x + ((-1956856 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_26 x)) := by
  rw [node334_check, Integer.Sparse.eval_merge]
  rw [node332_eval, node333_eval]

theorem node335_check : node335 =
    Integer.Sparse.merge node331 node334 := by decide +kernel

theorem node335_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node335 x = ((((474966 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_20 x + (((7981741 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_21 x + ((9023959 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_22 x)) + ((((-1518183 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_23 x + ((1177088 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_24 x) + (((-3205049 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_25 x + ((-1956856 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_26 x))) := by
  rw [node335_check, Integer.Sparse.eval_merge]
  rw [node331_eval, node334_eval]

theorem node336_check : node336 =
    Integer.Sparse.merge node329 node335 := by decide +kernel

theorem node336_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node336 x = (((((-1102075 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_13 x + (((962591 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_14 x + ((2637949 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_15 x)) + ((((188406 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_16 x + ((4768294 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_17 x) + (((-3725397 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_18 x + ((446791 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_19 x))) + ((((474966 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_20 x + (((7981741 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_21 x + ((9023959 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_22 x)) + ((((-1518183 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_23 x + ((1177088 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_24 x) + (((-3205049 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_25 x + ((-1956856 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_26 x)))) := by
  rw [node336_check, Integer.Sparse.eval_merge]
  rw [node329_eval, node335_eval]

theorem node337_check : node337 =
    Integer.Sparse.merge node323 node336 := by decide +kernel

theorem node337_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node337 x = ((((((8331635 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_0 x + (((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_1 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_2 x)) + (((1352597 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_3 x + (((3939166 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_4 x + ((-1289212 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_5 x))) + ((((-381717 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_6 x + (((-3540810 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_7 x + ((4317945 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_8 x)) + ((((5011875 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_9 x + ((670012 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_10 x) + (((3855450 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_11 x + ((5397378 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_12 x)))) + (((((-1102075 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_13 x + (((962591 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_14 x + ((2637949 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_15 x)) + ((((188406 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_16 x + ((4768294 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_17 x) + (((-3725397 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_18 x + ((446791 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_19 x))) + ((((474966 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_20 x + (((7981741 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_21 x + ((9023959 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_22 x)) + ((((-1518183 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_23 x + ((1177088 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_24 x) + (((-3205049 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_25 x + ((-1956856 : ℤ) : ℝ) * Integer.Sparse.eval entry_12_26 x))))) := by
  rw [node337_check, Integer.Sparse.eval_merge]
  rw [node323_eval, node336_eval]

theorem node338_check : node338 =
    Integer.Sparse.merge (Integer.Sparse.scale (-65538) entry_13_1) (Integer.Sparse.scale (737006) entry_13_2) := by decide +kernel

theorem node338_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node338 x = (((-65538 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_1 x + ((737006 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_2 x) := by
  rw [node338_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node339_check : node339 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2350116) entry_13_0) node338 := by decide +kernel

theorem node339_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node339 x = (((-2350116 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_0 x + (((-65538 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_1 x + ((737006 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_2 x)) := by
  rw [node339_check, Integer.Sparse.eval_merge]
  rw [node338_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node340_check : node340 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1359246) entry_13_4) (Integer.Sparse.scale (420869) entry_13_5) := by decide +kernel

theorem node340_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node340 x = (((-1359246 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_4 x + ((420869 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_5 x) := by
  rw [node340_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node341_check : node341 =
    Integer.Sparse.merge (Integer.Sparse.scale (2280274) entry_13_3) node340 := by decide +kernel

theorem node341_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node341 x = (((2280274 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_3 x + (((-1359246 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_4 x + ((420869 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_5 x)) := by
  rw [node341_check, Integer.Sparse.eval_merge]
  rw [node340_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node342_check : node342 =
    Integer.Sparse.merge node339 node341 := by decide +kernel

theorem node342_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node342 x = ((((-2350116 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_0 x + (((-65538 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_1 x + ((737006 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_2 x)) + (((2280274 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_3 x + (((-1359246 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_4 x + ((420869 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_5 x))) := by
  rw [node342_check, Integer.Sparse.eval_merge]
  rw [node339_eval, node341_eval]

theorem node343_check : node343 =
    Integer.Sparse.merge (Integer.Sparse.scale (1566438) entry_13_7) (Integer.Sparse.scale (-3579665) entry_13_8) := by decide +kernel

theorem node343_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node343 x = (((1566438 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_7 x + ((-3579665 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_8 x) := by
  rw [node343_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node344_check : node344 =
    Integer.Sparse.merge (Integer.Sparse.scale (-777936) entry_13_6) node343 := by decide +kernel

theorem node344_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node344 x = (((-777936 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_6 x + (((1566438 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_7 x + ((-3579665 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_8 x)) := by
  rw [node344_check, Integer.Sparse.eval_merge]
  rw [node343_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node345_check : node345 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2276717) entry_13_9) (Integer.Sparse.scale (1060859) entry_13_10) := by decide +kernel

theorem node345_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node345 x = (((-2276717 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_9 x + ((1060859 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_10 x) := by
  rw [node345_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node346_check : node346 =
    Integer.Sparse.merge (Integer.Sparse.scale (207606) entry_13_11) (Integer.Sparse.scale (-1102075) entry_13_12) := by decide +kernel

theorem node346_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node346 x = (((207606 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_11 x + ((-1102075 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_12 x) := by
  rw [node346_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node347_check : node347 =
    Integer.Sparse.merge node345 node346 := by decide +kernel

theorem node347_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node347 x = ((((-2276717 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_9 x + ((1060859 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_10 x) + (((207606 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_11 x + ((-1102075 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_12 x)) := by
  rw [node347_check, Integer.Sparse.eval_merge]
  rw [node345_eval, node346_eval]

theorem node348_check : node348 =
    Integer.Sparse.merge node344 node347 := by decide +kernel

theorem node348_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node348 x = ((((-777936 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_6 x + (((1566438 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_7 x + ((-3579665 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_8 x)) + ((((-2276717 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_9 x + ((1060859 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_10 x) + (((207606 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_11 x + ((-1102075 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_12 x))) := by
  rw [node348_check, Integer.Sparse.eval_merge]
  rw [node344_eval, node347_eval]

theorem node349_check : node349 =
    Integer.Sparse.merge node342 node348 := by decide +kernel

theorem node349_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node349 x = (((((-2350116 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_0 x + (((-65538 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_1 x + ((737006 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_2 x)) + (((2280274 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_3 x + (((-1359246 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_4 x + ((420869 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_5 x))) + ((((-777936 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_6 x + (((1566438 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_7 x + ((-3579665 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_8 x)) + ((((-2276717 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_9 x + ((1060859 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_10 x) + (((207606 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_11 x + ((-1102075 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_12 x)))) := by
  rw [node349_check, Integer.Sparse.eval_merge]
  rw [node342_eval, node348_eval]

theorem node350_check : node350 =
    Integer.Sparse.merge (Integer.Sparse.scale (-487516) entry_13_14) (Integer.Sparse.scale (-4116005) entry_13_15) := by decide +kernel

theorem node350_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node350 x = (((-487516 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x + ((-4116005 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x) := by
  rw [node350_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node351_check : node351 =
    Integer.Sparse.merge (Integer.Sparse.scale (2217189) entry_13_13) node350 := by decide +kernel

theorem node351_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node351 x = (((2217189 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_13 x + (((-487516 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x + ((-4116005 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x)) := by
  rw [node351_check, Integer.Sparse.eval_merge]
  rw [node350_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node352_check : node352 =
    Integer.Sparse.merge (Integer.Sparse.scale (-24349) entry_13_16) (Integer.Sparse.scale (-2063816) entry_13_17) := by decide +kernel

theorem node352_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node352 x = (((-24349 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + ((-2063816 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x) := by
  rw [node352_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node353_check : node353 =
    Integer.Sparse.merge (Integer.Sparse.scale (1117744) entry_13_18) (Integer.Sparse.scale (3592223) entry_13_19) := by decide +kernel

theorem node353_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node353 x = (((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x + ((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x) := by
  rw [node353_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node354_check : node354 =
    Integer.Sparse.merge node352 node353 := by decide +kernel

theorem node354_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node354 x = ((((-24349 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + ((-2063816 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x) + (((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x + ((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x)) := by
  rw [node354_check, Integer.Sparse.eval_merge]
  rw [node352_eval, node353_eval]

theorem node355_check : node355 =
    Integer.Sparse.merge node351 node354 := by decide +kernel

theorem node355_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node355 x = ((((2217189 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_13 x + (((-487516 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x + ((-4116005 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x)) + ((((-24349 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + ((-2063816 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x) + (((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x + ((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x))) := by
  rw [node355_check, Integer.Sparse.eval_merge]
  rw [node351_eval, node354_eval]

theorem node356_check : node356 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3987844) entry_13_21) (Integer.Sparse.scale (-147587) entry_13_22) := by decide +kernel

theorem node356_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node356 x = (((-3987844 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_21 x + ((-147587 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_22 x) := by
  rw [node356_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node357_check : node357 =
    Integer.Sparse.merge (Integer.Sparse.scale (593484) entry_13_20) node356 := by decide +kernel

theorem node357_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node357 x = (((593484 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x + (((-3987844 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_21 x + ((-147587 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_22 x)) := by
  rw [node357_check, Integer.Sparse.eval_merge]
  rw [node356_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node358_check : node358 =
    Integer.Sparse.merge (Integer.Sparse.scale (115748) entry_13_23) (Integer.Sparse.scale (503866) entry_13_24) := by decide +kernel

theorem node358_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node358 x = (((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_23 x + ((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_24 x) := by
  rw [node358_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node359_check : node359 =
    Integer.Sparse.merge (Integer.Sparse.scale (1956747) entry_13_25) (Integer.Sparse.scale (242711) entry_13_26) := by decide +kernel

theorem node359_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node359 x = (((1956747 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_25 x + ((242711 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_26 x) := by
  rw [node359_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node360_check : node360 =
    Integer.Sparse.merge node358 node359 := by decide +kernel

theorem node360_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node360 x = ((((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_23 x + ((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_24 x) + (((1956747 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_25 x + ((242711 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_26 x)) := by
  rw [node360_check, Integer.Sparse.eval_merge]
  rw [node358_eval, node359_eval]

theorem node361_check : node361 =
    Integer.Sparse.merge node357 node360 := by decide +kernel

theorem node361_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node361 x = ((((593484 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x + (((-3987844 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_21 x + ((-147587 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_22 x)) + ((((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_23 x + ((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_24 x) + (((1956747 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_25 x + ((242711 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_26 x))) := by
  rw [node361_check, Integer.Sparse.eval_merge]
  rw [node357_eval, node360_eval]

theorem node362_check : node362 =
    Integer.Sparse.merge node355 node361 := by decide +kernel

theorem node362_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node362 x = (((((2217189 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_13 x + (((-487516 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x + ((-4116005 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x)) + ((((-24349 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + ((-2063816 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x) + (((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x + ((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x))) + ((((593484 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x + (((-3987844 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_21 x + ((-147587 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_22 x)) + ((((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_23 x + ((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_24 x) + (((1956747 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_25 x + ((242711 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_26 x)))) := by
  rw [node362_check, Integer.Sparse.eval_merge]
  rw [node355_eval, node361_eval]

theorem node363_check : node363 =
    Integer.Sparse.merge node349 node362 := by decide +kernel

theorem node363_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node363 x = ((((((-2350116 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_0 x + (((-65538 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_1 x + ((737006 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_2 x)) + (((2280274 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_3 x + (((-1359246 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_4 x + ((420869 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_5 x))) + ((((-777936 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_6 x + (((1566438 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_7 x + ((-3579665 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_8 x)) + ((((-2276717 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_9 x + ((1060859 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_10 x) + (((207606 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_11 x + ((-1102075 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_12 x)))) + (((((2217189 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_13 x + (((-487516 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x + ((-4116005 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x)) + ((((-24349 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + ((-2063816 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x) + (((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x + ((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x))) + ((((593484 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x + (((-3987844 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_21 x + ((-147587 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_22 x)) + ((((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_23 x + ((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_24 x) + (((1956747 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_25 x + ((242711 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_26 x))))) := by
  rw [node363_check, Integer.Sparse.eval_merge]
  rw [node349_eval, node362_eval]

theorem node364_check : node364 =
    Integer.Sparse.merge (Integer.Sparse.scale (56758) entry_14_1) (Integer.Sparse.scale (2315448) entry_14_2) := by decide +kernel

theorem node364_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node364 x = (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x + ((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x) := by
  rw [node364_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node365_check : node365 =
    Integer.Sparse.merge (Integer.Sparse.scale (1781770) entry_14_0) node364 := by decide +kernel

theorem node365_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node365 x = (((1781770 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_0 x + (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x + ((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x)) := by
  rw [node365_check, Integer.Sparse.eval_merge]
  rw [node364_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node366_check : node366 =
    Integer.Sparse.merge (Integer.Sparse.scale (1532955) entry_14_4) (Integer.Sparse.scale (995398) entry_14_5) := by decide +kernel

theorem node366_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node366 x = (((1532955 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x + ((995398 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x) := by
  rw [node366_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node367_check : node367 =
    Integer.Sparse.merge (Integer.Sparse.scale (2706754) entry_14_3) node366 := by decide +kernel

theorem node367_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node367 x = (((2706754 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + (((1532955 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x + ((995398 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x)) := by
  rw [node367_check, Integer.Sparse.eval_merge]
  rw [node366_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node368_check : node368 =
    Integer.Sparse.merge node365 node367 := by decide +kernel

theorem node368_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node368 x = ((((1781770 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_0 x + (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x + ((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x)) + (((2706754 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + (((1532955 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x + ((995398 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x))) := by
  rw [node368_check, Integer.Sparse.eval_merge]
  rw [node365_eval, node367_eval]

theorem node369_check : node369 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1531264) entry_14_7) (Integer.Sparse.scale (2295640) entry_14_8) := by decide +kernel

theorem node369_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node369 x = (((-1531264 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x + ((2295640 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x) := by
  rw [node369_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node370_check : node370 =
    Integer.Sparse.merge (Integer.Sparse.scale (548165) entry_14_6) node369 := by decide +kernel

theorem node370_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node370 x = (((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_6 x + (((-1531264 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x + ((2295640 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x)) := by
  rw [node370_check, Integer.Sparse.eval_merge]
  rw [node369_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node371_check : node371 =
    Integer.Sparse.merge (Integer.Sparse.scale (1384567) entry_14_9) (Integer.Sparse.scale (-1536421) entry_14_10) := by decide +kernel

theorem node371_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node371 x = (((1384567 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x + ((-1536421 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x) := by
  rw [node371_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node372_check : node372 =
    Integer.Sparse.merge (Integer.Sparse.scale (919586) entry_14_11) (Integer.Sparse.scale (962591) entry_14_12) := by decide +kernel

theorem node372_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node372 x = (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x + ((962591 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x) := by
  rw [node372_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node373_check : node373 =
    Integer.Sparse.merge node371 node372 := by decide +kernel

theorem node373_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node373 x = ((((1384567 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x + ((-1536421 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x) + (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x + ((962591 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x)) := by
  rw [node373_check, Integer.Sparse.eval_merge]
  rw [node371_eval, node372_eval]

theorem node374_check : node374 =
    Integer.Sparse.merge node370 node373 := by decide +kernel

theorem node374_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node374 x = ((((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_6 x + (((-1531264 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x + ((2295640 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x)) + ((((1384567 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x + ((-1536421 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x) + (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x + ((962591 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x))) := by
  rw [node374_check, Integer.Sparse.eval_merge]
  rw [node370_eval, node373_eval]

theorem node375_check : node375 =
    Integer.Sparse.merge node368 node374 := by decide +kernel

theorem node375_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node375 x = (((((1781770 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_0 x + (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x + ((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x)) + (((2706754 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + (((1532955 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x + ((995398 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x))) + ((((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_6 x + (((-1531264 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x + ((2295640 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x)) + ((((1384567 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x + ((-1536421 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x) + (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x + ((962591 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x)))) := by
  rw [node375_check, Integer.Sparse.eval_merge]
  rw [node368_eval, node374_eval]

theorem node376_check : node376 =
    Integer.Sparse.merge (Integer.Sparse.scale (3205882) entry_14_14) (Integer.Sparse.scale (2761862) entry_14_15) := by decide +kernel

theorem node376_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node376 x = (((3205882 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x + ((2761862 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x) := by
  rw [node376_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node377_check : node377 =
    Integer.Sparse.merge (Integer.Sparse.scale (-487516) entry_14_13) node376 := by decide +kernel

theorem node377_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node377 x = (((-487516 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_13 x + (((3205882 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x + ((2761862 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x)) := by
  rw [node377_check, Integer.Sparse.eval_merge]
  rw [node376_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node378_check : node378 =
    Integer.Sparse.merge (Integer.Sparse.scale (1941024) entry_14_16) (Integer.Sparse.scale (3868069) entry_14_17) := by decide +kernel

theorem node378_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node378 x = (((1941024 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + ((3868069 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x) := by
  rw [node378_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node379_check : node379 =
    Integer.Sparse.merge (Integer.Sparse.scale (2452580) entry_14_18) (Integer.Sparse.scale (-1000408) entry_14_19) := by decide +kernel

theorem node379_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node379 x = (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x + ((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x) := by
  rw [node379_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node380_check : node380 =
    Integer.Sparse.merge node378 node379 := by decide +kernel

theorem node380_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node380 x = ((((1941024 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + ((3868069 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x) + (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x + ((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x)) := by
  rw [node380_check, Integer.Sparse.eval_merge]
  rw [node378_eval, node379_eval]

theorem node381_check : node381 =
    Integer.Sparse.merge node377 node380 := by decide +kernel

theorem node381_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node381 x = ((((-487516 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_13 x + (((3205882 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x + ((2761862 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x)) + ((((1941024 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + ((3868069 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x) + (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x + ((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x))) := by
  rw [node381_check, Integer.Sparse.eval_merge]
  rw [node377_eval, node380_eval]

theorem node382_check : node382 =
    Integer.Sparse.merge (Integer.Sparse.scale (3595017) entry_14_21) (Integer.Sparse.scale (-827728) entry_14_22) := by decide +kernel

theorem node382_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node382 x = (((3595017 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_21 x + ((-827728 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_22 x) := by
  rw [node382_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node383_check : node383 =
    Integer.Sparse.merge (Integer.Sparse.scale (392906) entry_14_20) node382 := by decide +kernel

theorem node383_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node383 x = (((392906 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_20 x + (((3595017 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_21 x + ((-827728 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_22 x)) := by
  rw [node383_check, Integer.Sparse.eval_merge]
  rw [node382_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node384_check : node384 =
    Integer.Sparse.merge (Integer.Sparse.scale (802693) entry_14_23) (Integer.Sparse.scale (-106086) entry_14_24) := by decide +kernel

theorem node384_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node384 x = (((802693 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_23 x + ((-106086 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_24 x) := by
  rw [node384_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node385_check : node385 =
    Integer.Sparse.merge (Integer.Sparse.scale (2607707) entry_14_25) (Integer.Sparse.scale (-1763362) entry_14_26) := by decide +kernel

theorem node385_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node385 x = (((2607707 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_25 x + ((-1763362 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_26 x) := by
  rw [node385_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node386_check : node386 =
    Integer.Sparse.merge node384 node385 := by decide +kernel

theorem node386_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node386 x = ((((802693 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_23 x + ((-106086 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_24 x) + (((2607707 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_25 x + ((-1763362 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_26 x)) := by
  rw [node386_check, Integer.Sparse.eval_merge]
  rw [node384_eval, node385_eval]

theorem node387_check : node387 =
    Integer.Sparse.merge node383 node386 := by decide +kernel

theorem node387_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node387 x = ((((392906 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_20 x + (((3595017 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_21 x + ((-827728 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_22 x)) + ((((802693 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_23 x + ((-106086 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_24 x) + (((2607707 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_25 x + ((-1763362 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_26 x))) := by
  rw [node387_check, Integer.Sparse.eval_merge]
  rw [node383_eval, node386_eval]

theorem node388_check : node388 =
    Integer.Sparse.merge node381 node387 := by decide +kernel

theorem node388_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node388 x = (((((-487516 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_13 x + (((3205882 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x + ((2761862 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x)) + ((((1941024 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + ((3868069 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x) + (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x + ((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x))) + ((((392906 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_20 x + (((3595017 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_21 x + ((-827728 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_22 x)) + ((((802693 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_23 x + ((-106086 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_24 x) + (((2607707 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_25 x + ((-1763362 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_26 x)))) := by
  rw [node388_check, Integer.Sparse.eval_merge]
  rw [node381_eval, node387_eval]

theorem node389_check : node389 =
    Integer.Sparse.merge node375 node388 := by decide +kernel

theorem node389_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node389 x = ((((((1781770 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_0 x + (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x + ((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x)) + (((2706754 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + (((1532955 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x + ((995398 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x))) + ((((548165 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_6 x + (((-1531264 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x + ((2295640 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x)) + ((((1384567 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x + ((-1536421 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x) + (((919586 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x + ((962591 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x)))) + (((((-487516 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_13 x + (((3205882 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x + ((2761862 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x)) + ((((1941024 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + ((3868069 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x) + (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x + ((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x))) + ((((392906 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_20 x + (((3595017 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_21 x + ((-827728 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_22 x)) + ((((802693 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_23 x + ((-106086 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_24 x) + (((2607707 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_25 x + ((-1763362 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_26 x))))) := by
  rw [node389_check, Integer.Sparse.eval_merge]
  rw [node375_eval, node388_eval]

theorem node390_check : node390 =
    Integer.Sparse.merge (Integer.Sparse.scale (-848390) entry_15_1) (Integer.Sparse.scale (-2604186) entry_15_2) := by decide +kernel

theorem node390_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node390 x = (((-848390 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_1 x + ((-2604186 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_2 x) := by
  rw [node390_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node391_check : node391 =
    Integer.Sparse.merge (Integer.Sparse.scale (196990) entry_15_0) node390 := by decide +kernel

theorem node391_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node391 x = (((196990 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_0 x + (((-848390 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_1 x + ((-2604186 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_2 x)) := by
  rw [node391_check, Integer.Sparse.eval_merge]
  rw [node390_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node392_check : node392 =
    Integer.Sparse.merge (Integer.Sparse.scale (5894401) entry_15_4) (Integer.Sparse.scale (-3671401) entry_15_5) := by decide +kernel

theorem node392_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node392 x = (((5894401 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_4 x + ((-3671401 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_5 x) := by
  rw [node392_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node393_check : node393 =
    Integer.Sparse.merge (Integer.Sparse.scale (-11269051) entry_15_3) node392 := by decide +kernel

theorem node393_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node393 x = (((-11269051 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_3 x + (((5894401 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_4 x + ((-3671401 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_5 x)) := by
  rw [node393_check, Integer.Sparse.eval_merge]
  rw [node392_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node394_check : node394 =
    Integer.Sparse.merge node391 node393 := by decide +kernel

theorem node394_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node394 x = ((((196990 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_0 x + (((-848390 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_1 x + ((-2604186 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_2 x)) + (((-11269051 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_3 x + (((5894401 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_4 x + ((-3671401 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_5 x))) := by
  rw [node394_check, Integer.Sparse.eval_merge]
  rw [node391_eval, node393_eval]

theorem node395_check : node395 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6992208) entry_15_7) (Integer.Sparse.scale (13833571) entry_15_8) := by decide +kernel

theorem node395_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node395 x = (((-6992208 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_7 x + ((13833571 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_8 x) := by
  rw [node395_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node396_check : node396 =
    Integer.Sparse.merge (Integer.Sparse.scale (7957870) entry_15_6) node395 := by decide +kernel

theorem node396_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node396 x = (((7957870 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_6 x + (((-6992208 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_7 x + ((13833571 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_8 x)) := by
  rw [node396_check, Integer.Sparse.eval_merge]
  rw [node395_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node397_check : node397 =
    Integer.Sparse.merge (Integer.Sparse.scale (12642667) entry_15_9) (Integer.Sparse.scale (-6516193) entry_15_10) := by decide +kernel

theorem node397_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node397 x = (((12642667 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_9 x + ((-6516193 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_10 x) := by
  rw [node397_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node398_check : node398 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1479887) entry_15_11) (Integer.Sparse.scale (2637949) entry_15_12) := by decide +kernel

theorem node398_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node398 x = (((-1479887 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_11 x + ((2637949 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_12 x) := by
  rw [node398_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node399_check : node399 =
    Integer.Sparse.merge node397 node398 := by decide +kernel

theorem node399_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node399 x = ((((12642667 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_9 x + ((-6516193 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_10 x) + (((-1479887 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_11 x + ((2637949 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_12 x)) := by
  rw [node399_check, Integer.Sparse.eval_merge]
  rw [node397_eval, node398_eval]

theorem node400_check : node400 =
    Integer.Sparse.merge node396 node399 := by decide +kernel

theorem node400_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node400 x = ((((7957870 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_6 x + (((-6992208 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_7 x + ((13833571 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_8 x)) + ((((12642667 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_9 x + ((-6516193 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_10 x) + (((-1479887 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_11 x + ((2637949 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_12 x))) := by
  rw [node400_check, Integer.Sparse.eval_merge]
  rw [node396_eval, node399_eval]

theorem node401_check : node401 =
    Integer.Sparse.merge node394 node400 := by decide +kernel

theorem node401_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node401 x = (((((196990 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_0 x + (((-848390 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_1 x + ((-2604186 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_2 x)) + (((-11269051 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_3 x + (((5894401 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_4 x + ((-3671401 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_5 x))) + ((((7957870 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_6 x + (((-6992208 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_7 x + ((13833571 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_8 x)) + ((((12642667 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_9 x + ((-6516193 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_10 x) + (((-1479887 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_11 x + ((2637949 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_12 x)))) := by
  rw [node401_check, Integer.Sparse.eval_merge]
  rw [node394_eval, node400_eval]

theorem node402_check : node402 =
    Integer.Sparse.merge (Integer.Sparse.scale (2761862) entry_15_14) (Integer.Sparse.scale (32801715) entry_15_15) := by decide +kernel

theorem node402_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node402 x = (((2761862 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_14 x + ((32801715 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_15 x) := by
  rw [node402_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node403_check : node403 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4116005) entry_15_13) node402 := by decide +kernel

theorem node403_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node403 x = (((-4116005 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_13 x + (((2761862 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_14 x + ((32801715 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_15 x)) := by
  rw [node403_check, Integer.Sparse.eval_merge]
  rw [node402_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node404_check : node404 =
    Integer.Sparse.merge (Integer.Sparse.scale (4724490) entry_15_16) (Integer.Sparse.scale (10794029) entry_15_17) := by decide +kernel

theorem node404_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node404 x = (((4724490 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_16 x + ((10794029 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_17 x) := by
  rw [node404_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node405_check : node405 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6316274) entry_15_18) (Integer.Sparse.scale (-25027763) entry_15_19) := by decide +kernel

theorem node405_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node405 x = (((-6316274 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_18 x + ((-25027763 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_19 x) := by
  rw [node405_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node406_check : node406 =
    Integer.Sparse.merge node404 node405 := by decide +kernel

theorem node406_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node406 x = ((((4724490 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_16 x + ((10794029 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_17 x) + (((-6316274 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_18 x + ((-25027763 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_19 x)) := by
  rw [node406_check, Integer.Sparse.eval_merge]
  rw [node404_eval, node405_eval]

theorem node407_check : node407 =
    Integer.Sparse.merge node403 node406 := by decide +kernel

theorem node407_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node407 x = ((((-4116005 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_13 x + (((2761862 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_14 x + ((32801715 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_15 x)) + ((((4724490 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_16 x + ((10794029 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_17 x) + (((-6316274 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_18 x + ((-25027763 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_19 x))) := by
  rw [node407_check, Integer.Sparse.eval_merge]
  rw [node403_eval, node406_eval]

theorem node408_check : node408 =
    Integer.Sparse.merge (Integer.Sparse.scale (16030892) entry_15_21) (Integer.Sparse.scale (-22856504) entry_15_22) := by decide +kernel

theorem node408_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node408 x = (((16030892 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_21 x + ((-22856504 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_22 x) := by
  rw [node408_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node409_check : node409 =
    Integer.Sparse.merge (Integer.Sparse.scale (-614355) entry_15_20) node408 := by decide +kernel

theorem node409_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node409 x = (((-614355 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_20 x + (((16030892 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_21 x + ((-22856504 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_22 x)) := by
  rw [node409_check, Integer.Sparse.eval_merge]
  rw [node408_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node410_check : node410 =
    Integer.Sparse.merge (Integer.Sparse.scale (8622411) entry_15_23) (Integer.Sparse.scale (-639546) entry_15_24) := by decide +kernel

theorem node410_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node410 x = (((8622411 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_23 x + ((-639546 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_24 x) := by
  rw [node410_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node411_check : node411 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4918260) entry_15_25) (Integer.Sparse.scale (-4211536) entry_15_26) := by decide +kernel

theorem node411_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node411 x = (((-4918260 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_25 x + ((-4211536 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_26 x) := by
  rw [node411_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node412_check : node412 =
    Integer.Sparse.merge node410 node411 := by decide +kernel

theorem node412_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node412 x = ((((8622411 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_23 x + ((-639546 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_24 x) + (((-4918260 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_25 x + ((-4211536 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_26 x)) := by
  rw [node412_check, Integer.Sparse.eval_merge]
  rw [node410_eval, node411_eval]

theorem node413_check : node413 =
    Integer.Sparse.merge node409 node412 := by decide +kernel

theorem node413_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node413 x = ((((-614355 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_20 x + (((16030892 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_21 x + ((-22856504 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_22 x)) + ((((8622411 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_23 x + ((-639546 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_24 x) + (((-4918260 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_25 x + ((-4211536 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_26 x))) := by
  rw [node413_check, Integer.Sparse.eval_merge]
  rw [node409_eval, node412_eval]

theorem node414_check : node414 =
    Integer.Sparse.merge node407 node413 := by decide +kernel

theorem node414_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node414 x = (((((-4116005 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_13 x + (((2761862 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_14 x + ((32801715 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_15 x)) + ((((4724490 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_16 x + ((10794029 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_17 x) + (((-6316274 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_18 x + ((-25027763 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_19 x))) + ((((-614355 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_20 x + (((16030892 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_21 x + ((-22856504 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_22 x)) + ((((8622411 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_23 x + ((-639546 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_24 x) + (((-4918260 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_25 x + ((-4211536 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_26 x)))) := by
  rw [node414_check, Integer.Sparse.eval_merge]
  rw [node407_eval, node413_eval]

theorem node415_check : node415 =
    Integer.Sparse.merge node401 node414 := by decide +kernel

theorem node415_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node415 x = ((((((196990 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_0 x + (((-848390 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_1 x + ((-2604186 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_2 x)) + (((-11269051 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_3 x + (((5894401 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_4 x + ((-3671401 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_5 x))) + ((((7957870 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_6 x + (((-6992208 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_7 x + ((13833571 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_8 x)) + ((((12642667 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_9 x + ((-6516193 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_10 x) + (((-1479887 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_11 x + ((2637949 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_12 x)))) + (((((-4116005 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_13 x + (((2761862 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_14 x + ((32801715 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_15 x)) + ((((4724490 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_16 x + ((10794029 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_17 x) + (((-6316274 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_18 x + ((-25027763 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_19 x))) + ((((-614355 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_20 x + (((16030892 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_21 x + ((-22856504 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_22 x)) + ((((8622411 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_23 x + ((-639546 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_24 x) + (((-4918260 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_25 x + ((-4211536 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_26 x))))) := by
  rw [node415_check, Integer.Sparse.eval_merge]
  rw [node401_eval, node414_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node416_check : node416 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1894747) entry_16_1) (Integer.Sparse.scale (830681) entry_16_2) := by decide +kernel

theorem node416_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node416 x = (((-1894747 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_1 x + ((830681 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_2 x) := by
  rw [node416_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node417_check : node417 =
    Integer.Sparse.merge (Integer.Sparse.scale (-196597) entry_16_0) node416 := by decide +kernel

theorem node417_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node417 x = (((-196597 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_0 x + (((-1894747 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_1 x + ((830681 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_2 x)) := by
  rw [node417_check, Integer.Sparse.eval_merge]
  rw [node416_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node418_check : node418 =
    Integer.Sparse.merge (Integer.Sparse.scale (-29611) entry_16_4) (Integer.Sparse.scale (-3970214) entry_16_5) := by decide +kernel

theorem node418_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node418 x = (((-29611 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_4 x + ((-3970214 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_5 x) := by
  rw [node418_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node419_check : node419 =
    Integer.Sparse.merge (Integer.Sparse.scale (4787889) entry_16_3) node418 := by decide +kernel

theorem node419_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node419 x = (((4787889 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_3 x + (((-29611 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_4 x + ((-3970214 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_5 x)) := by
  rw [node419_check, Integer.Sparse.eval_merge]
  rw [node418_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node420_check : node420 =
    Integer.Sparse.merge node417 node419 := by decide +kernel

theorem node420_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node420 x = ((((-196597 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_0 x + (((-1894747 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_1 x + ((830681 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_2 x)) + (((4787889 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_3 x + (((-29611 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_4 x + ((-3970214 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_5 x))) := by
  rw [node420_check, Integer.Sparse.eval_merge]
  rw [node417_eval, node419_eval]

theorem node421_check : node421 =
    Integer.Sparse.merge (Integer.Sparse.scale (-99872) entry_16_7) (Integer.Sparse.scale (730101) entry_16_8) := by decide +kernel

theorem node421_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node421 x = (((-99872 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_7 x + ((730101 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_8 x) := by
  rw [node421_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node422_check : node422 =
    Integer.Sparse.merge (Integer.Sparse.scale (1340972) entry_16_6) node421 := by decide +kernel

theorem node422_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node422 x = (((1340972 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_6 x + (((-99872 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_7 x + ((730101 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_8 x)) := by
  rw [node422_check, Integer.Sparse.eval_merge]
  rw [node421_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node423_check : node423 =
    Integer.Sparse.merge (Integer.Sparse.scale (479639) entry_16_9) (Integer.Sparse.scale (-3482292) entry_16_10) := by decide +kernel

theorem node423_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node423 x = (((479639 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_9 x + ((-3482292 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_10 x) := by
  rw [node423_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node424_check : node424 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1937263) entry_16_11) (Integer.Sparse.scale (188406) entry_16_12) := by decide +kernel

theorem node424_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node424 x = (((-1937263 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_11 x + ((188406 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_12 x) := by
  rw [node424_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node425_check : node425 =
    Integer.Sparse.merge node423 node424 := by decide +kernel

theorem node425_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node425 x = ((((479639 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_9 x + ((-3482292 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_10 x) + (((-1937263 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_11 x + ((188406 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_12 x)) := by
  rw [node425_check, Integer.Sparse.eval_merge]
  rw [node423_eval, node424_eval]

theorem node426_check : node426 =
    Integer.Sparse.merge node422 node425 := by decide +kernel

theorem node426_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node426 x = ((((1340972 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_6 x + (((-99872 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_7 x + ((730101 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_8 x)) + ((((479639 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_9 x + ((-3482292 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_10 x) + (((-1937263 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_11 x + ((188406 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_12 x))) := by
  rw [node426_check, Integer.Sparse.eval_merge]
  rw [node422_eval, node425_eval]

theorem node427_check : node427 =
    Integer.Sparse.merge node420 node426 := by decide +kernel

theorem node427_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node427 x = (((((-196597 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_0 x + (((-1894747 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_1 x + ((830681 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_2 x)) + (((4787889 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_3 x + (((-29611 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_4 x + ((-3970214 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_5 x))) + ((((1340972 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_6 x + (((-99872 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_7 x + ((730101 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_8 x)) + ((((479639 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_9 x + ((-3482292 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_10 x) + (((-1937263 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_11 x + ((188406 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_12 x)))) := by
  rw [node427_check, Integer.Sparse.eval_merge]
  rw [node420_eval, node426_eval]

theorem node428_check : node428 =
    Integer.Sparse.merge (Integer.Sparse.scale (1941024) entry_16_14) (Integer.Sparse.scale (4724490) entry_16_15) := by decide +kernel

theorem node428_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node428 x = (((1941024 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_14 x + ((4724490 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_15 x) := by
  rw [node428_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node429_check : node429 =
    Integer.Sparse.merge (Integer.Sparse.scale (-24349) entry_16_13) node428 := by decide +kernel

theorem node429_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node429 x = (((-24349 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_13 x + (((1941024 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_14 x + ((4724490 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_15 x)) := by
  rw [node429_check, Integer.Sparse.eval_merge]
  rw [node428_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node430_check : node430 =
    Integer.Sparse.merge (Integer.Sparse.scale (12353120) entry_16_16) (Integer.Sparse.scale (774544) entry_16_17) := by decide +kernel

theorem node430_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node430 x = (((12353120 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_16 x + ((774544 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_17 x) := by
  rw [node430_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node431_check : node431 =
    Integer.Sparse.merge (Integer.Sparse.scale (4523372) entry_16_18) (Integer.Sparse.scale (3167390) entry_16_19) := by decide +kernel

theorem node431_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node431 x = (((4523372 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_18 x + ((3167390 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_19 x) := by
  rw [node431_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node432_check : node432 =
    Integer.Sparse.merge node430 node431 := by decide +kernel

theorem node432_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node432 x = ((((12353120 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_16 x + ((774544 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_17 x) + (((4523372 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_18 x + ((3167390 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_19 x)) := by
  rw [node432_check, Integer.Sparse.eval_merge]
  rw [node430_eval, node431_eval]

theorem node433_check : node433 =
    Integer.Sparse.merge node429 node432 := by decide +kernel

theorem node433_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node433 x = ((((-24349 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_13 x + (((1941024 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_14 x + ((4724490 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_15 x)) + ((((12353120 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_16 x + ((774544 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_17 x) + (((4523372 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_18 x + ((3167390 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_19 x))) := by
  rw [node433_check, Integer.Sparse.eval_merge]
  rw [node429_eval, node432_eval]

theorem node434_check : node434 =
    Integer.Sparse.merge (Integer.Sparse.scale (3762949) entry_16_21) (Integer.Sparse.scale (-9242889) entry_16_22) := by decide +kernel

theorem node434_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node434 x = (((3762949 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_21 x + ((-9242889 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_22 x) := by
  rw [node434_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node435_check : node435 =
    Integer.Sparse.merge (Integer.Sparse.scale (1143666) entry_16_20) node434 := by decide +kernel

theorem node435_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node435 x = (((1143666 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_20 x + (((3762949 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_21 x + ((-9242889 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_22 x)) := by
  rw [node435_check, Integer.Sparse.eval_merge]
  rw [node434_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node436_check : node436 =
    Integer.Sparse.merge (Integer.Sparse.scale (3957804) entry_16_23) (Integer.Sparse.scale (-3010232) entry_16_24) := by decide +kernel

theorem node436_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node436 x = (((3957804 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_23 x + ((-3010232 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_24 x) := by
  rw [node436_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node437_check : node437 =
    Integer.Sparse.merge (Integer.Sparse.scale (6368365) entry_16_25) (Integer.Sparse.scale (344604) entry_16_26) := by decide +kernel

theorem node437_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node437 x = (((6368365 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_25 x + ((344604 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_26 x) := by
  rw [node437_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node438_check : node438 =
    Integer.Sparse.merge node436 node437 := by decide +kernel

theorem node438_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node438 x = ((((3957804 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_23 x + ((-3010232 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_24 x) + (((6368365 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_25 x + ((344604 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_26 x)) := by
  rw [node438_check, Integer.Sparse.eval_merge]
  rw [node436_eval, node437_eval]

theorem node439_check : node439 =
    Integer.Sparse.merge node435 node438 := by decide +kernel

theorem node439_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node439 x = ((((1143666 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_20 x + (((3762949 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_21 x + ((-9242889 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_22 x)) + ((((3957804 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_23 x + ((-3010232 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_24 x) + (((6368365 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_25 x + ((344604 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_26 x))) := by
  rw [node439_check, Integer.Sparse.eval_merge]
  rw [node435_eval, node438_eval]

theorem node440_check : node440 =
    Integer.Sparse.merge node433 node439 := by decide +kernel

theorem node440_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node440 x = (((((-24349 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_13 x + (((1941024 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_14 x + ((4724490 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_15 x)) + ((((12353120 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_16 x + ((774544 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_17 x) + (((4523372 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_18 x + ((3167390 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_19 x))) + ((((1143666 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_20 x + (((3762949 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_21 x + ((-9242889 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_22 x)) + ((((3957804 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_23 x + ((-3010232 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_24 x) + (((6368365 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_25 x + ((344604 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_26 x)))) := by
  rw [node440_check, Integer.Sparse.eval_merge]
  rw [node433_eval, node439_eval]

theorem node441_check : node441 =
    Integer.Sparse.merge node427 node440 := by decide +kernel

theorem node441_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node441 x = ((((((-196597 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_0 x + (((-1894747 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_1 x + ((830681 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_2 x)) + (((4787889 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_3 x + (((-29611 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_4 x + ((-3970214 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_5 x))) + ((((1340972 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_6 x + (((-99872 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_7 x + ((730101 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_8 x)) + ((((479639 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_9 x + ((-3482292 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_10 x) + (((-1937263 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_11 x + ((188406 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_12 x)))) + (((((-24349 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_13 x + (((1941024 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_14 x + ((4724490 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_15 x)) + ((((12353120 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_16 x + ((774544 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_17 x) + (((4523372 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_18 x + ((3167390 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_19 x))) + ((((1143666 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_20 x + (((3762949 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_21 x + ((-9242889 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_22 x)) + ((((3957804 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_23 x + ((-3010232 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_24 x) + (((6368365 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_25 x + ((344604 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_26 x))))) := by
  rw [node441_check, Integer.Sparse.eval_merge]
  rw [node427_eval, node440_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node468_check : node468 =
    Integer.Sparse.merge (Integer.Sparse.scale (37861) entry_18_1) (Integer.Sparse.scale (4672623) entry_18_2) := by decide +kernel

theorem node468_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node468 x = (((37861 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_1 x + ((4672623 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_2 x) := by
  rw [node468_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node469_check : node469 =
    Integer.Sparse.merge (Integer.Sparse.scale (-8510275) entry_18_0) node468 := by decide +kernel

theorem node469_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node469 x = (((-8510275 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_0 x + (((37861 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_1 x + ((4672623 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_2 x)) := by
  rw [node469_check, Integer.Sparse.eval_merge]
  rw [node468_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node470_check : node470 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2291217) entry_18_4) (Integer.Sparse.scale (1583616) entry_18_5) := by decide +kernel

theorem node470_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node470 x = (((-2291217 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x + ((1583616 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x) := by
  rw [node470_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node471_check : node471 =
    Integer.Sparse.merge (Integer.Sparse.scale (3611637) entry_18_3) node470 := by decide +kernel

theorem node471_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node471 x = (((3611637 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + (((-2291217 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x + ((1583616 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x)) := by
  rw [node471_check, Integer.Sparse.eval_merge]
  rw [node470_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node472_check : node472 =
    Integer.Sparse.merge node469 node471 := by decide +kernel

theorem node472_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node472 x = ((((-8510275 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_0 x + (((37861 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_1 x + ((4672623 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_2 x)) + (((3611637 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + (((-2291217 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x + ((1583616 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x))) := by
  rw [node472_check, Integer.Sparse.eval_merge]
  rw [node469_eval, node471_eval]

theorem node473_check : node473 =
    Integer.Sparse.merge (Integer.Sparse.scale (4157406) entry_18_7) (Integer.Sparse.scale (-9345834) entry_18_8) := by decide +kernel

theorem node473_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node473 x = (((4157406 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x + ((-9345834 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x) := by
  rw [node473_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node474_check : node474 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1148157) entry_18_6) node473 := by decide +kernel

theorem node474_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node474 x = (((-1148157 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x + (((4157406 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x + ((-9345834 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x)) := by
  rw [node474_check, Integer.Sparse.eval_merge]
  rw [node473_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node475_check : node475 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4897979) entry_18_9) (Integer.Sparse.scale (-6889389) entry_18_10) := by decide +kernel

theorem node475_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node475 x = (((-4897979 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x + ((-6889389 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x) := by
  rw [node475_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node476_check : node476 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1958480) entry_18_11) (Integer.Sparse.scale (-3725397) entry_18_12) := by decide +kernel

theorem node476_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node476 x = (((-1958480 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x + ((-3725397 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x) := by
  rw [node476_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node477_check : node477 =
    Integer.Sparse.merge node475 node476 := by decide +kernel

theorem node477_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node477 x = ((((-4897979 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x + ((-6889389 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x) + (((-1958480 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x + ((-3725397 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x)) := by
  rw [node477_check, Integer.Sparse.eval_merge]
  rw [node475_eval, node476_eval]

theorem node478_check : node478 =
    Integer.Sparse.merge node474 node477 := by decide +kernel

theorem node478_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node478 x = ((((-1148157 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x + (((4157406 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x + ((-9345834 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x)) + ((((-4897979 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x + ((-6889389 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x) + (((-1958480 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x + ((-3725397 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x))) := by
  rw [node478_check, Integer.Sparse.eval_merge]
  rw [node474_eval, node477_eval]

theorem node479_check : node479 =
    Integer.Sparse.merge node472 node478 := by decide +kernel

theorem node479_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node479 x = (((((-8510275 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_0 x + (((37861 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_1 x + ((4672623 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_2 x)) + (((3611637 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + (((-2291217 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x + ((1583616 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x))) + ((((-1148157 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x + (((4157406 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x + ((-9345834 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x)) + ((((-4897979 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x + ((-6889389 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x) + (((-1958480 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x + ((-3725397 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x)))) := by
  rw [node479_check, Integer.Sparse.eval_merge]
  rw [node472_eval, node478_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node480_check : node480 =
    Integer.Sparse.merge (Integer.Sparse.scale (2452580) entry_18_14) (Integer.Sparse.scale (-6316274) entry_18_15) := by decide +kernel

theorem node480_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node480 x = (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((-6316274 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x) := by
  rw [node480_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node481_check : node481 =
    Integer.Sparse.merge (Integer.Sparse.scale (1117744) entry_18_13) node480 := by decide +kernel

theorem node481_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node481 x = (((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((-6316274 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x)) := by
  rw [node481_check, Integer.Sparse.eval_merge]
  rw [node480_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node482_check : node482 =
    Integer.Sparse.merge (Integer.Sparse.scale (4523372) entry_18_16) (Integer.Sparse.scale (2066116) entry_18_17) := by decide +kernel

theorem node482_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node482 x = (((4523372 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + ((2066116 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x) := by
  rw [node482_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node483_check : node483 =
    Integer.Sparse.merge (Integer.Sparse.scale (15960711) entry_18_18) (Integer.Sparse.scale (902133) entry_18_19) := by decide +kernel

theorem node483_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node483 x = (((15960711 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x + ((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x) := by
  rw [node483_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node484_check : node484 =
    Integer.Sparse.merge node482 node483 := by decide +kernel

theorem node484_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node484 x = ((((4523372 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + ((2066116 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x) + (((15960711 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x + ((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x)) := by
  rw [node484_check, Integer.Sparse.eval_merge]
  rw [node482_eval, node483_eval]

theorem node485_check : node485 =
    Integer.Sparse.merge node481 node484 := by decide +kernel

theorem node485_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node485 x = ((((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((-6316274 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x)) + ((((4523372 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + ((2066116 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x) + (((15960711 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x + ((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x))) := by
  rw [node485_check, Integer.Sparse.eval_merge]
  rw [node481_eval, node484_eval]

theorem node486_check : node486 =
    Integer.Sparse.merge (Integer.Sparse.scale (-8554511) entry_18_21) (Integer.Sparse.scale (-16299324) entry_18_22) := by decide +kernel

theorem node486_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node486 x = (((-8554511 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x + ((-16299324 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_22 x) := by
  rw [node486_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node487_check : node487 =
    Integer.Sparse.merge (Integer.Sparse.scale (788329) entry_18_20) node486 := by decide +kernel

theorem node487_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node487 x = (((788329 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + (((-8554511 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x + ((-16299324 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_22 x)) := by
  rw [node487_check, Integer.Sparse.eval_merge]
  rw [node486_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node488_check : node488 =
    Integer.Sparse.merge (Integer.Sparse.scale (3279438) entry_18_23) (Integer.Sparse.scale (-3450350) entry_18_24) := by decide +kernel

theorem node488_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node488 x = (((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_23 x + ((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_24 x) := by
  rw [node488_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node489_check : node489 =
    Integer.Sparse.merge (Integer.Sparse.scale (17682257) entry_18_25) (Integer.Sparse.scale (3152538) entry_18_26) := by decide +kernel

theorem node489_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node489 x = (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_25 x + ((3152538 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_26 x) := by
  rw [node489_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node490_check : node490 =
    Integer.Sparse.merge node488 node489 := by decide +kernel

theorem node490_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node490 x = ((((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_23 x + ((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_24 x) + (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_25 x + ((3152538 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_26 x)) := by
  rw [node490_check, Integer.Sparse.eval_merge]
  rw [node488_eval, node489_eval]

theorem node491_check : node491 =
    Integer.Sparse.merge node487 node490 := by decide +kernel

theorem node491_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node491 x = ((((788329 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + (((-8554511 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x + ((-16299324 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_22 x)) + ((((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_23 x + ((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_24 x) + (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_25 x + ((3152538 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_26 x))) := by
  rw [node491_check, Integer.Sparse.eval_merge]
  rw [node487_eval, node490_eval]

theorem node492_check : node492 =
    Integer.Sparse.merge node485 node491 := by decide +kernel

theorem node492_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node492 x = (((((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((-6316274 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x)) + ((((4523372 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + ((2066116 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x) + (((15960711 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x + ((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x))) + ((((788329 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + (((-8554511 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x + ((-16299324 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_22 x)) + ((((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_23 x + ((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_24 x) + (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_25 x + ((3152538 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_26 x)))) := by
  rw [node492_check, Integer.Sparse.eval_merge]
  rw [node485_eval, node491_eval]

theorem node493_check : node493 =
    Integer.Sparse.merge node479 node492 := by decide +kernel

theorem node493_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node493 x = ((((((-8510275 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_0 x + (((37861 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_1 x + ((4672623 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_2 x)) + (((3611637 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + (((-2291217 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x + ((1583616 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x))) + ((((-1148157 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x + (((4157406 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x + ((-9345834 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x)) + ((((-4897979 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x + ((-6889389 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x) + (((-1958480 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x + ((-3725397 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x)))) + (((((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((-6316274 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x)) + ((((4523372 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + ((2066116 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x) + (((15960711 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x + ((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x))) + ((((788329 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + (((-8554511 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x + ((-16299324 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_22 x)) + ((((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_23 x + ((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_24 x) + (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_25 x + ((3152538 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_26 x))))) := by
  rw [node493_check, Integer.Sparse.eval_merge]
  rw [node479_eval, node492_eval]

theorem node494_check : node494 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2357894) entry_19_1) (Integer.Sparse.scale (-140249) entry_19_2) := by decide +kernel

theorem node494_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node494 x = (((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x) := by
  rw [node494_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node495_check : node495 =
    Integer.Sparse.merge (Integer.Sparse.scale (4751159) entry_19_0) node494 := by decide +kernel

theorem node495_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node495 x = (((4751159 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + (((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x)) := by
  rw [node495_check, Integer.Sparse.eval_merge]
  rw [node494_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node496_check : node496 =
    Integer.Sparse.merge (Integer.Sparse.scale (-481138) entry_19_4) (Integer.Sparse.scale (-2751073) entry_19_5) := by decide +kernel

theorem node496_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node496 x = (((-481138 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x + ((-2751073 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x) := by
  rw [node496_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node497_check : node497 =
    Integer.Sparse.merge (Integer.Sparse.scale (21924365) entry_19_3) node496 := by decide +kernel

theorem node497_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node497 x = (((21924365 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + (((-481138 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x + ((-2751073 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x)) := by
  rw [node497_check, Integer.Sparse.eval_merge]
  rw [node496_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node498_check : node498 =
    Integer.Sparse.merge node495 node497 := by decide +kernel

theorem node498_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node498 x = ((((4751159 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + (((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x)) + (((21924365 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + (((-481138 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x + ((-2751073 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x))) := by
  rw [node498_check, Integer.Sparse.eval_merge]
  rw [node495_eval, node497_eval]

theorem node499_check : node499 =
    Integer.Sparse.merge (Integer.Sparse.scale (380152) entry_19_7) (Integer.Sparse.scale (-1057876) entry_19_8) := by decide +kernel

theorem node499_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node499 x = (((380152 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x + ((-1057876 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x) := by
  rw [node499_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node500_check : node500 =
    Integer.Sparse.merge (Integer.Sparse.scale (-5852439) entry_19_6) node499 := by decide +kernel

theorem node500_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node500 x = (((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + (((380152 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x + ((-1057876 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x)) := by
  rw [node500_check, Integer.Sparse.eval_merge]
  rw [node499_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node501_check : node501 =
    Integer.Sparse.merge (Integer.Sparse.scale (-9757133) entry_19_9) (Integer.Sparse.scale (9482366) entry_19_10) := by decide +kernel

theorem node501_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node501 x = (((-9757133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((9482366 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x) := by
  rw [node501_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node502_check : node502 =
    Integer.Sparse.merge (Integer.Sparse.scale (5974596) entry_19_11) (Integer.Sparse.scale (446791) entry_19_12) := by decide +kernel

theorem node502_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node502 x = (((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x + ((446791 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x) := by
  rw [node502_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node503_check : node503 =
    Integer.Sparse.merge node501 node502 := by decide +kernel

theorem node503_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node503 x = ((((-9757133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((9482366 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x) + (((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x + ((446791 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x)) := by
  rw [node503_check, Integer.Sparse.eval_merge]
  rw [node501_eval, node502_eval]

theorem node504_check : node504 =
    Integer.Sparse.merge node500 node503 := by decide +kernel

theorem node504_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node504 x = ((((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + (((380152 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x + ((-1057876 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x)) + ((((-9757133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((9482366 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x) + (((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x + ((446791 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x))) := by
  rw [node504_check, Integer.Sparse.eval_merge]
  rw [node500_eval, node503_eval]

theorem node505_check : node505 =
    Integer.Sparse.merge node498 node504 := by decide +kernel

theorem node505_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node505 x = (((((4751159 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + (((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x)) + (((21924365 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + (((-481138 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x + ((-2751073 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x))) + ((((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + (((380152 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x + ((-1057876 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x)) + ((((-9757133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((9482366 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x) + (((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x + ((446791 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x)))) := by
  rw [node505_check, Integer.Sparse.eval_merge]
  rw [node498_eval, node504_eval]

theorem node506_check : node506 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1000408) entry_19_14) (Integer.Sparse.scale (-25027763) entry_19_15) := by decide +kernel

theorem node506_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node506 x = (((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-25027763 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x) := by
  rw [node506_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node507_check : node507 =
    Integer.Sparse.merge (Integer.Sparse.scale (3592223) entry_19_13) node506 := by decide +kernel

theorem node507_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node507 x = (((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + (((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-25027763 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x)) := by
  rw [node507_check, Integer.Sparse.eval_merge]
  rw [node506_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node508_check : node508 =
    Integer.Sparse.merge (Integer.Sparse.scale (3167390) entry_19_16) (Integer.Sparse.scale (-13574800) entry_19_17) := by decide +kernel

theorem node508_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node508 x = (((3167390 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + ((-13574800 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x) := by
  rw [node508_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node509_check : node509 =
    Integer.Sparse.merge (Integer.Sparse.scale (902133) entry_19_18) (Integer.Sparse.scale (41963642) entry_19_19) := by decide +kernel

theorem node509_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node509 x = (((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x + ((41963642 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x) := by
  rw [node509_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node510_check : node510 =
    Integer.Sparse.merge node508 node509 := by decide +kernel

theorem node510_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node510 x = ((((3167390 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + ((-13574800 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x) + (((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x + ((41963642 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x)) := by
  rw [node510_check, Integer.Sparse.eval_merge]
  rw [node508_eval, node509_eval]

theorem node511_check : node511 =
    Integer.Sparse.merge node507 node510 := by decide +kernel

theorem node511_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node511 x = ((((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + (((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-25027763 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x)) + ((((3167390 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + ((-13574800 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x) + (((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x + ((41963642 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x))) := by
  rw [node511_check, Integer.Sparse.eval_merge]
  rw [node507_eval, node510_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node512_check : node512 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1690663) entry_19_21) (Integer.Sparse.scale (32194445) entry_19_22) := by decide +kernel

theorem node512_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node512 x = (((-1690663 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_21 x + ((32194445 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_22 x) := by
  rw [node512_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node513_check : node513 =
    Integer.Sparse.merge (Integer.Sparse.scale (2913559) entry_19_20) node512 := by decide +kernel

theorem node513_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node513 x = (((2913559 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x + (((-1690663 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_21 x + ((32194445 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_22 x)) := by
  rw [node513_check, Integer.Sparse.eval_merge]
  rw [node512_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node514_check : node514 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2228810) entry_19_23) (Integer.Sparse.scale (1782706) entry_19_24) := by decide +kernel

theorem node514_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node514 x = (((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_23 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_24 x) := by
  rw [node514_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node515_check : node515 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1930609) entry_19_25) (Integer.Sparse.scale (618762) entry_19_26) := by decide +kernel

theorem node515_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node515 x = (((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_25 x + ((618762 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_26 x) := by
  rw [node515_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node516_check : node516 =
    Integer.Sparse.merge node514 node515 := by decide +kernel

theorem node516_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node516 x = ((((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_23 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_24 x) + (((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_25 x + ((618762 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_26 x)) := by
  rw [node516_check, Integer.Sparse.eval_merge]
  rw [node514_eval, node515_eval]

theorem node517_check : node517 =
    Integer.Sparse.merge node513 node516 := by decide +kernel

theorem node517_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node517 x = ((((2913559 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x + (((-1690663 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_21 x + ((32194445 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_22 x)) + ((((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_23 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_24 x) + (((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_25 x + ((618762 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_26 x))) := by
  rw [node517_check, Integer.Sparse.eval_merge]
  rw [node513_eval, node516_eval]

theorem node518_check : node518 =
    Integer.Sparse.merge node511 node517 := by decide +kernel

theorem node518_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node518 x = (((((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + (((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-25027763 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x)) + ((((3167390 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + ((-13574800 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x) + (((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x + ((41963642 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x))) + ((((2913559 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x + (((-1690663 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_21 x + ((32194445 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_22 x)) + ((((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_23 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_24 x) + (((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_25 x + ((618762 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_26 x)))) := by
  rw [node518_check, Integer.Sparse.eval_merge]
  rw [node511_eval, node517_eval]

theorem node519_check : node519 =
    Integer.Sparse.merge node505 node518 := by decide +kernel

theorem node519_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node519 x = ((((((4751159 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + (((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x)) + (((21924365 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + (((-481138 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x + ((-2751073 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x))) + ((((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + (((380152 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x + ((-1057876 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x)) + ((((-9757133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((9482366 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x) + (((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x + ((446791 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x)))) + (((((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + (((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-25027763 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x)) + ((((3167390 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + ((-13574800 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x) + (((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x + ((41963642 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x))) + ((((2913559 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_20 x + (((-1690663 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_21 x + ((32194445 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_22 x)) + ((((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_23 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_24 x) + (((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_25 x + ((618762 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_26 x))))) := by
  rw [node519_check, Integer.Sparse.eval_merge]
  rw [node505_eval, node518_eval]

theorem node520_check : node520 =
    Integer.Sparse.merge (Integer.Sparse.scale (-256571) entry_20_1) (Integer.Sparse.scale (456406) entry_20_2) := by decide +kernel

theorem node520_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node520 x = (((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x + ((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x) := by
  rw [node520_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node521_check : node521 =
    Integer.Sparse.merge (Integer.Sparse.scale (70965) entry_20_0) node520 := by decide +kernel

theorem node521_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node521 x = (((70965 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_0 x + (((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x + ((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x)) := by
  rw [node521_check, Integer.Sparse.eval_merge]
  rw [node520_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node522_check : node522 =
    Integer.Sparse.merge (Integer.Sparse.scale (684539) entry_20_4) (Integer.Sparse.scale (-341589) entry_20_5) := by decide +kernel

theorem node522_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node522 x = (((684539 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x + ((-341589 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x) := by
  rw [node522_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node523_check : node523 =
    Integer.Sparse.merge (Integer.Sparse.scale (2276614) entry_20_3) node522 := by decide +kernel

theorem node523_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node523 x = (((2276614 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + (((684539 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x + ((-341589 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x)) := by
  rw [node523_check, Integer.Sparse.eval_merge]
  rw [node522_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node524_check : node524 =
    Integer.Sparse.merge node521 node523 := by decide +kernel

theorem node524_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node524 x = ((((70965 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_0 x + (((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x + ((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x)) + (((2276614 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + (((684539 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x + ((-341589 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x))) := by
  rw [node524_check, Integer.Sparse.eval_merge]
  rw [node521_eval, node523_eval]

theorem node525_check : node525 =
    Integer.Sparse.merge (Integer.Sparse.scale (-257758) entry_20_7) (Integer.Sparse.scale (-83947) entry_20_8) := by decide +kernel

theorem node525_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node525 x = (((-257758 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x + ((-83947 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x) := by
  rw [node525_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node526_check : node526 =
    Integer.Sparse.merge (Integer.Sparse.scale (-380245) entry_20_6) node525 := by decide +kernel

theorem node526_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node526 x = (((-380245 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_6 x + (((-257758 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x + ((-83947 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x)) := by
  rw [node526_check, Integer.Sparse.eval_merge]
  rw [node525_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node527_check : node527 =
    Integer.Sparse.merge (Integer.Sparse.scale (-304344) entry_20_9) (Integer.Sparse.scale (-31994) entry_20_10) := by decide +kernel

theorem node527_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node527 x = (((-304344 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x + ((-31994 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x) := by
  rw [node527_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node528_check : node528 =
    Integer.Sparse.merge (Integer.Sparse.scale (1576779) entry_20_11) (Integer.Sparse.scale (474966) entry_20_12) := by decide +kernel

theorem node528_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node528 x = (((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x + ((474966 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x) := by
  rw [node528_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node529_check : node529 =
    Integer.Sparse.merge node527 node528 := by decide +kernel

theorem node529_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node529 x = ((((-304344 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x + ((-31994 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x) + (((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x + ((474966 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x)) := by
  rw [node529_check, Integer.Sparse.eval_merge]
  rw [node527_eval, node528_eval]

theorem node530_check : node530 =
    Integer.Sparse.merge node526 node529 := by decide +kernel

theorem node530_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node530 x = ((((-380245 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_6 x + (((-257758 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x + ((-83947 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x)) + ((((-304344 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x + ((-31994 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x) + (((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x + ((474966 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x))) := by
  rw [node530_check, Integer.Sparse.eval_merge]
  rw [node526_eval, node529_eval]

theorem node531_check : node531 =
    Integer.Sparse.merge node524 node530 := by decide +kernel

theorem node531_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node531 x = (((((70965 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_0 x + (((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x + ((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x)) + (((2276614 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + (((684539 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x + ((-341589 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x))) + ((((-380245 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_6 x + (((-257758 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x + ((-83947 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x)) + ((((-304344 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x + ((-31994 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x) + (((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x + ((474966 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x)))) := by
  rw [node531_check, Integer.Sparse.eval_merge]
  rw [node524_eval, node530_eval]

theorem node532_check : node532 =
    Integer.Sparse.merge (Integer.Sparse.scale (392906) entry_20_14) (Integer.Sparse.scale (-614355) entry_20_15) := by decide +kernel

theorem node532_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node532 x = (((392906 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x + ((-614355 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x) := by
  rw [node532_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node533_check : node533 =
    Integer.Sparse.merge (Integer.Sparse.scale (593484) entry_20_13) node532 := by decide +kernel

theorem node533_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node533 x = (((593484 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_13 x + (((392906 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x + ((-614355 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x)) := by
  rw [node533_check, Integer.Sparse.eval_merge]
  rw [node532_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node534_check : node534 =
    Integer.Sparse.merge (Integer.Sparse.scale (1143666) entry_20_16) (Integer.Sparse.scale (196572) entry_20_17) := by decide +kernel

theorem node534_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node534 x = (((1143666 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + ((196572 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x) := by
  rw [node534_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node535_check : node535 =
    Integer.Sparse.merge (Integer.Sparse.scale (788329) entry_20_18) (Integer.Sparse.scale (2913559) entry_20_19) := by decide +kernel

theorem node535_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node535 x = (((788329 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x + ((2913559 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x) := by
  rw [node535_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node536_check : node536 =
    Integer.Sparse.merge node534 node535 := by decide +kernel

theorem node536_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node536 x = ((((1143666 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + ((196572 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x) + (((788329 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x + ((2913559 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x)) := by
  rw [node536_check, Integer.Sparse.eval_merge]
  rw [node534_eval, node535_eval]

theorem node537_check : node537 =
    Integer.Sparse.merge node533 node536 := by decide +kernel

theorem node537_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node537 x = ((((593484 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_13 x + (((392906 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x + ((-614355 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x)) + ((((1143666 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + ((196572 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x) + (((788329 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x + ((2913559 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x))) := by
  rw [node537_check, Integer.Sparse.eval_merge]
  rw [node533_eval, node536_eval]

theorem node538_check : node538 =
    Integer.Sparse.merge (Integer.Sparse.scale (954088) entry_20_21) (Integer.Sparse.scale (1261245) entry_20_22) := by decide +kernel

theorem node538_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node538 x = (((954088 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_21 x + ((1261245 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_22 x) := by
  rw [node538_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node539_check : node539 =
    Integer.Sparse.merge (Integer.Sparse.scale (935757) entry_20_20) node538 := by decide +kernel

theorem node539_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node539 x = (((935757 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_20 x + (((954088 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_21 x + ((1261245 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_22 x)) := by
  rw [node539_check, Integer.Sparse.eval_merge]
  rw [node538_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node540_check : node540 =
    Integer.Sparse.merge (Integer.Sparse.scale (918772) entry_20_23) (Integer.Sparse.scale (233548) entry_20_24) := by decide +kernel

theorem node540_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node540 x = (((918772 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_23 x + ((233548 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_24 x) := by
  rw [node540_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node541_check : node541 =
    Integer.Sparse.merge (Integer.Sparse.scale (1646149) entry_20_25) (Integer.Sparse.scale (-428236) entry_20_26) := by decide +kernel

theorem node541_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node541 x = (((1646149 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_25 x + ((-428236 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_26 x) := by
  rw [node541_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node542_check : node542 =
    Integer.Sparse.merge node540 node541 := by decide +kernel

theorem node542_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node542 x = ((((918772 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_23 x + ((233548 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_24 x) + (((1646149 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_25 x + ((-428236 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_26 x)) := by
  rw [node542_check, Integer.Sparse.eval_merge]
  rw [node540_eval, node541_eval]

theorem node543_check : node543 =
    Integer.Sparse.merge node539 node542 := by decide +kernel

theorem node543_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node543 x = ((((935757 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_20 x + (((954088 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_21 x + ((1261245 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_22 x)) + ((((918772 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_23 x + ((233548 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_24 x) + (((1646149 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_25 x + ((-428236 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_26 x))) := by
  rw [node543_check, Integer.Sparse.eval_merge]
  rw [node539_eval, node542_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node544_check : node544 =
    Integer.Sparse.merge node537 node543 := by decide +kernel

theorem node544_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node544 x = (((((593484 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_13 x + (((392906 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x + ((-614355 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x)) + ((((1143666 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + ((196572 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x) + (((788329 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x + ((2913559 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x))) + ((((935757 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_20 x + (((954088 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_21 x + ((1261245 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_22 x)) + ((((918772 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_23 x + ((233548 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_24 x) + (((1646149 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_25 x + ((-428236 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_26 x)))) := by
  rw [node544_check, Integer.Sparse.eval_merge]
  rw [node537_eval, node543_eval]

theorem node545_check : node545 =
    Integer.Sparse.merge node531 node544 := by decide +kernel

theorem node545_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node545 x = ((((((70965 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_0 x + (((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x + ((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x)) + (((2276614 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + (((684539 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x + ((-341589 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x))) + ((((-380245 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_6 x + (((-257758 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x + ((-83947 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x)) + ((((-304344 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x + ((-31994 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x) + (((1576779 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x + ((474966 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x)))) + (((((593484 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_13 x + (((392906 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x + ((-614355 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x)) + ((((1143666 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + ((196572 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x) + (((788329 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x + ((2913559 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x))) + ((((935757 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_20 x + (((954088 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_21 x + ((1261245 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_22 x)) + ((((918772 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_23 x + ((233548 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_24 x) + (((1646149 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_25 x + ((-428236 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_26 x))))) := by
  rw [node545_check, Integer.Sparse.eval_merge]
  rw [node531_eval, node544_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node598_check : node598 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1361624) entry_23_1) (Integer.Sparse.scale (-483957) entry_23_2) := by decide +kernel

theorem node598_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node598 x = (((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_1 x + ((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_2 x) := by
  rw [node598_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node599_check : node599 =
    Integer.Sparse.merge (Integer.Sparse.scale (-9014352) entry_23_0) node598 := by decide +kernel

theorem node599_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node599 x = (((-9014352 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_0 x + (((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_1 x + ((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_2 x)) := by
  rw [node599_check, Integer.Sparse.eval_merge]
  rw [node598_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node600_check : node600 =
    Integer.Sparse.merge (Integer.Sparse.scale (3406557) entry_23_4) (Integer.Sparse.scale (-3406562) entry_23_5) := by decide +kernel

theorem node600_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node600 x = (((3406557 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_4 x + ((-3406562 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_5 x) := by
  rw [node600_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node601_check : node601 =
    Integer.Sparse.merge (Integer.Sparse.scale (-685263) entry_23_3) node600 := by decide +kernel

theorem node601_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node601 x = (((-685263 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_3 x + (((3406557 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_4 x + ((-3406562 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_5 x)) := by
  rw [node601_check, Integer.Sparse.eval_merge]
  rw [node600_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node602_check : node602 =
    Integer.Sparse.merge node599 node601 := by decide +kernel

theorem node602_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node602 x = ((((-9014352 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_0 x + (((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_1 x + ((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_2 x)) + (((-685263 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_3 x + (((3406557 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_4 x + ((-3406562 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_5 x))) := by
  rw [node602_check, Integer.Sparse.eval_merge]
  rw [node599_eval, node601_eval]

theorem node603_check : node603 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1431032) entry_23_7) (Integer.Sparse.scale (5283323) entry_23_8) := by decide +kernel

theorem node603_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node603 x = (((-1431032 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_7 x + ((5283323 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_8 x) := by
  rw [node603_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node604_check : node604 =
    Integer.Sparse.merge (Integer.Sparse.scale (2933849) entry_23_6) node603 := by decide +kernel

theorem node604_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node604 x = (((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_6 x + (((-1431032 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_7 x + ((5283323 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_8 x)) := by
  rw [node604_check, Integer.Sparse.eval_merge]
  rw [node603_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node605_check : node605 =
    Integer.Sparse.merge (Integer.Sparse.scale (4687144) entry_23_9) (Integer.Sparse.scale (-5584492) entry_23_10) := by decide +kernel

theorem node605_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node605 x = (((4687144 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_9 x + ((-5584492 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_10 x) := by
  rw [node605_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node606_check : node606 =
    Integer.Sparse.merge (Integer.Sparse.scale (-736999) entry_23_11) (Integer.Sparse.scale (-1518183) entry_23_12) := by decide +kernel

theorem node606_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node606 x = (((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_11 x + ((-1518183 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_12 x) := by
  rw [node606_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node607_check : node607 =
    Integer.Sparse.merge node605 node606 := by decide +kernel

theorem node607_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node607 x = ((((4687144 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_9 x + ((-5584492 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_10 x) + (((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_11 x + ((-1518183 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_12 x)) := by
  rw [node607_check, Integer.Sparse.eval_merge]
  rw [node605_eval, node606_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node608_check : node608 =
    Integer.Sparse.merge node604 node607 := by decide +kernel

theorem node608_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node608 x = ((((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_6 x + (((-1431032 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_7 x + ((5283323 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_8 x)) + ((((4687144 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_9 x + ((-5584492 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_10 x) + (((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_11 x + ((-1518183 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_12 x))) := by
  rw [node608_check, Integer.Sparse.eval_merge]
  rw [node604_eval, node607_eval]

theorem node609_check : node609 =
    Integer.Sparse.merge node602 node608 := by decide +kernel

theorem node609_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node609 x = (((((-9014352 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_0 x + (((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_1 x + ((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_2 x)) + (((-685263 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_3 x + (((3406557 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_4 x + ((-3406562 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_5 x))) + ((((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_6 x + (((-1431032 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_7 x + ((5283323 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_8 x)) + ((((4687144 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_9 x + ((-5584492 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_10 x) + (((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_11 x + ((-1518183 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_12 x)))) := by
  rw [node609_check, Integer.Sparse.eval_merge]
  rw [node602_eval, node608_eval]

theorem node610_check : node610 =
    Integer.Sparse.merge (Integer.Sparse.scale (802693) entry_23_14) (Integer.Sparse.scale (8622411) entry_23_15) := by decide +kernel

theorem node610_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node610 x = (((802693 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_14 x + ((8622411 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_15 x) := by
  rw [node610_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node611_check : node611 =
    Integer.Sparse.merge (Integer.Sparse.scale (115748) entry_23_13) node610 := by decide +kernel

theorem node611_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node611 x = (((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_13 x + (((802693 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_14 x + ((8622411 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_15 x)) := by
  rw [node611_check, Integer.Sparse.eval_merge]
  rw [node610_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node612_check : node612 =
    Integer.Sparse.merge (Integer.Sparse.scale (3957804) entry_23_16) (Integer.Sparse.scale (3932306) entry_23_17) := by decide +kernel

theorem node612_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node612 x = (((3957804 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_16 x + ((3932306 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_17 x) := by
  rw [node612_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node613_check : node613 =
    Integer.Sparse.merge (Integer.Sparse.scale (3279438) entry_23_18) (Integer.Sparse.scale (-2228810) entry_23_19) := by decide +kernel

theorem node613_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node613 x = (((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_18 x + ((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_19 x) := by
  rw [node613_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node614_check : node614 =
    Integer.Sparse.merge node612 node613 := by decide +kernel

theorem node614_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node614 x = ((((3957804 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_16 x + ((3932306 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_17 x) + (((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_18 x + ((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_19 x)) := by
  rw [node614_check, Integer.Sparse.eval_merge]
  rw [node612_eval, node613_eval]

theorem node615_check : node615 =
    Integer.Sparse.merge node611 node614 := by decide +kernel

theorem node615_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node615 x = ((((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_13 x + (((802693 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_14 x + ((8622411 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_15 x)) + ((((3957804 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_16 x + ((3932306 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_17 x) + (((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_18 x + ((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_19 x))) := by
  rw [node615_check, Integer.Sparse.eval_merge]
  rw [node611_eval, node614_eval]

theorem node616_check : node616 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3684421) entry_23_21) (Integer.Sparse.scale (-18865439) entry_23_22) := by decide +kernel

theorem node616_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node616 x = (((-3684421 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_21 x + ((-18865439 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_22 x) := by
  rw [node616_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node617_check : node617 =
    Integer.Sparse.merge (Integer.Sparse.scale (918772) entry_23_20) node616 := by decide +kernel

theorem node617_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node617 x = (((918772 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_20 x + (((-3684421 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_21 x + ((-18865439 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_22 x)) := by
  rw [node617_check, Integer.Sparse.eval_merge]
  rw [node616_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node618_check : node618 =
    Integer.Sparse.merge (Integer.Sparse.scale (14224969) entry_23_23) (Integer.Sparse.scale (472) entry_23_24) := by decide +kernel

theorem node618_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node618 x = (((14224969 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_23 x + ((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_24 x) := by
  rw [node618_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node619_check : node619 =
    Integer.Sparse.merge (Integer.Sparse.scale (6264265) entry_23_25) (Integer.Sparse.scale (1201176) entry_23_26) := by decide +kernel

theorem node619_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node619 x = (((6264265 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_25 x + ((1201176 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_26 x) := by
  rw [node619_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node620_check : node620 =
    Integer.Sparse.merge node618 node619 := by decide +kernel

theorem node620_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node620 x = ((((14224969 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_23 x + ((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_24 x) + (((6264265 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_25 x + ((1201176 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_26 x)) := by
  rw [node620_check, Integer.Sparse.eval_merge]
  rw [node618_eval, node619_eval]

theorem node621_check : node621 =
    Integer.Sparse.merge node617 node620 := by decide +kernel

theorem node621_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node621 x = ((((918772 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_20 x + (((-3684421 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_21 x + ((-18865439 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_22 x)) + ((((14224969 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_23 x + ((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_24 x) + (((6264265 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_25 x + ((1201176 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_26 x))) := by
  rw [node621_check, Integer.Sparse.eval_merge]
  rw [node617_eval, node620_eval]

theorem node622_check : node622 =
    Integer.Sparse.merge node615 node621 := by decide +kernel

theorem node622_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node622 x = (((((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_13 x + (((802693 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_14 x + ((8622411 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_15 x)) + ((((3957804 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_16 x + ((3932306 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_17 x) + (((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_18 x + ((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_19 x))) + ((((918772 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_20 x + (((-3684421 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_21 x + ((-18865439 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_22 x)) + ((((14224969 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_23 x + ((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_24 x) + (((6264265 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_25 x + ((1201176 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_26 x)))) := by
  rw [node622_check, Integer.Sparse.eval_merge]
  rw [node615_eval, node621_eval]

theorem node623_check : node623 =
    Integer.Sparse.merge node609 node622 := by decide +kernel

theorem node623_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node623 x = ((((((-9014352 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_0 x + (((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_1 x + ((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_2 x)) + (((-685263 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_3 x + (((3406557 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_4 x + ((-3406562 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_5 x))) + ((((2933849 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_6 x + (((-1431032 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_7 x + ((5283323 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_8 x)) + ((((4687144 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_9 x + ((-5584492 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_10 x) + (((-736999 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_11 x + ((-1518183 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_12 x)))) + (((((115748 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_13 x + (((802693 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_14 x + ((8622411 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_15 x)) + ((((3957804 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_16 x + ((3932306 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_17 x) + (((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_18 x + ((-2228810 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_19 x))) + ((((918772 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_20 x + (((-3684421 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_21 x + ((-18865439 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_22 x)) + ((((14224969 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_23 x + ((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_24 x) + (((6264265 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_25 x + ((1201176 : ℤ) : ℝ) * Integer.Sparse.eval entry_23_26 x))))) := by
  rw [node623_check, Integer.Sparse.eval_merge]
  rw [node609_eval, node622_eval]

theorem node624_check : node624 =
    Integer.Sparse.merge (Integer.Sparse.scale (449476) entry_24_1) (Integer.Sparse.scale (-124524) entry_24_2) := by decide +kernel

theorem node624_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node624 x = (((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_1 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_2 x) := by
  rw [node624_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node625_check : node625 =
    Integer.Sparse.merge (Integer.Sparse.scale (2605212) entry_24_0) node624 := by decide +kernel

theorem node625_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node625 x = (((2605212 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_0 x + (((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_1 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_2 x)) := by
  rw [node625_check, Integer.Sparse.eval_merge]
  rw [node624_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node626_check : node626 =
    Integer.Sparse.merge (Integer.Sparse.scale (1483542) entry_24_4) (Integer.Sparse.scale (619147) entry_24_5) := by decide +kernel

theorem node626_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node626 x = (((1483542 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_4 x + ((619147 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_5 x) := by
  rw [node626_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node627_check : node627 =
    Integer.Sparse.merge (Integer.Sparse.scale (1227195) entry_24_3) node626 := by decide +kernel

theorem node627_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node627 x = (((1227195 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_3 x + (((1483542 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_4 x + ((619147 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_5 x)) := by
  rw [node627_check, Integer.Sparse.eval_merge]
  rw [node626_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node628_check : node628 =
    Integer.Sparse.merge node625 node627 := by decide +kernel

theorem node628_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node628 x = ((((2605212 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_0 x + (((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_1 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_2 x)) + (((1227195 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_3 x + (((1483542 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_4 x + ((619147 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_5 x))) := by
  rw [node628_check, Integer.Sparse.eval_merge]
  rw [node625_eval, node627_eval]

theorem node629_check : node629 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1723883) entry_24_7) (Integer.Sparse.scale (2916394) entry_24_8) := by decide +kernel

theorem node629_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node629 x = (((-1723883 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_7 x + ((2916394 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_8 x) := by
  rw [node629_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node630_check : node630 =
    Integer.Sparse.merge (Integer.Sparse.scale (-467475) entry_24_6) node629 := by decide +kernel

theorem node630_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node630 x = (((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_6 x + (((-1723883 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_7 x + ((2916394 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_8 x)) := by
  rw [node630_check, Integer.Sparse.eval_merge]
  rw [node629_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node631_check : node631 =
    Integer.Sparse.merge (Integer.Sparse.scale (2310344) entry_24_9) (Integer.Sparse.scale (2189272) entry_24_10) := by decide +kernel

theorem node631_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node631 x = (((2310344 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_9 x + ((2189272 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_10 x) := by
  rw [node631_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node632_check : node632 =
    Integer.Sparse.merge (Integer.Sparse.scale (2493931) entry_24_11) (Integer.Sparse.scale (1177088) entry_24_12) := by decide +kernel

theorem node632_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node632 x = (((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_11 x + ((1177088 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_12 x) := by
  rw [node632_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node633_check : node633 =
    Integer.Sparse.merge node631 node632 := by decide +kernel

theorem node633_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node633 x = ((((2310344 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_9 x + ((2189272 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_10 x) + (((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_11 x + ((1177088 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_12 x)) := by
  rw [node633_check, Integer.Sparse.eval_merge]
  rw [node631_eval, node632_eval]

theorem node634_check : node634 =
    Integer.Sparse.merge node630 node633 := by decide +kernel

theorem node634_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node634 x = ((((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_6 x + (((-1723883 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_7 x + ((2916394 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_8 x)) + ((((2310344 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_9 x + ((2189272 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_10 x) + (((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_11 x + ((1177088 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_12 x))) := by
  rw [node634_check, Integer.Sparse.eval_merge]
  rw [node630_eval, node633_eval]

theorem node635_check : node635 =
    Integer.Sparse.merge node628 node634 := by decide +kernel

theorem node635_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node635 x = (((((2605212 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_0 x + (((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_1 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_2 x)) + (((1227195 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_3 x + (((1483542 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_4 x + ((619147 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_5 x))) + ((((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_6 x + (((-1723883 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_7 x + ((2916394 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_8 x)) + ((((2310344 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_9 x + ((2189272 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_10 x) + (((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_11 x + ((1177088 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_12 x)))) := by
  rw [node635_check, Integer.Sparse.eval_merge]
  rw [node628_eval, node634_eval]

theorem node636_check : node636 =
    Integer.Sparse.merge (Integer.Sparse.scale (-106086) entry_24_14) (Integer.Sparse.scale (-639546) entry_24_15) := by decide +kernel

theorem node636_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node636 x = (((-106086 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_14 x + ((-639546 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_15 x) := by
  rw [node636_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node637_check : node637 =
    Integer.Sparse.merge (Integer.Sparse.scale (503866) entry_24_13) node636 := by decide +kernel

theorem node637_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node637 x = (((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_13 x + (((-106086 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_14 x + ((-639546 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_15 x)) := by
  rw [node637_check, Integer.Sparse.eval_merge]
  rw [node636_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node638_check : node638 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3010232) entry_24_16) (Integer.Sparse.scale (1121311) entry_24_17) := by decide +kernel

theorem node638_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node638 x = (((-3010232 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_16 x + ((1121311 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_17 x) := by
  rw [node638_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node639_check : node639 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3450350) entry_24_18) (Integer.Sparse.scale (1782706) entry_24_19) := by decide +kernel

theorem node639_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node639 x = (((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_18 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_19 x) := by
  rw [node639_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node640_check : node640 =
    Integer.Sparse.merge node638 node639 := by decide +kernel

theorem node640_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node640 x = ((((-3010232 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_16 x + ((1121311 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_17 x) + (((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_18 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_19 x)) := by
  rw [node640_check, Integer.Sparse.eval_merge]
  rw [node638_eval, node639_eval]

theorem node641_check : node641 =
    Integer.Sparse.merge node637 node640 := by decide +kernel

theorem node641_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node641 x = ((((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_13 x + (((-106086 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_14 x + ((-639546 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_15 x)) + ((((-3010232 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_16 x + ((1121311 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_17 x) + (((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_18 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_19 x))) := by
  rw [node641_check, Integer.Sparse.eval_merge]
  rw [node637_eval, node640_eval]

theorem node642_check : node642 =
    Integer.Sparse.merge (Integer.Sparse.scale (-299084) entry_24_21) (Integer.Sparse.scale (7037228) entry_24_22) := by decide +kernel

theorem node642_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node642 x = (((-299084 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_21 x + ((7037228 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_22 x) := by
  rw [node642_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node643_check : node643 =
    Integer.Sparse.merge (Integer.Sparse.scale (233548) entry_24_20) node642 := by decide +kernel

theorem node643_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node643 x = (((233548 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_20 x + (((-299084 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_21 x + ((7037228 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_22 x)) := by
  rw [node643_check, Integer.Sparse.eval_merge]
  rw [node642_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node644_check : node644 =
    Integer.Sparse.merge (Integer.Sparse.scale (472) entry_24_23) (Integer.Sparse.scale (2520573) entry_24_24) := by decide +kernel

theorem node644_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node644 x = (((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_23 x + ((2520573 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_24 x) := by
  rw [node644_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node645_check : node645 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3319037) entry_24_25) (Integer.Sparse.scale (-1287392) entry_24_26) := by decide +kernel

theorem node645_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node645 x = (((-3319037 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_25 x + ((-1287392 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_26 x) := by
  rw [node645_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node646_check : node646 =
    Integer.Sparse.merge node644 node645 := by decide +kernel

theorem node646_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node646 x = ((((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_23 x + ((2520573 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_24 x) + (((-3319037 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_25 x + ((-1287392 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_26 x)) := by
  rw [node646_check, Integer.Sparse.eval_merge]
  rw [node644_eval, node645_eval]

theorem node647_check : node647 =
    Integer.Sparse.merge node643 node646 := by decide +kernel

theorem node647_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node647 x = ((((233548 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_20 x + (((-299084 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_21 x + ((7037228 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_22 x)) + ((((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_23 x + ((2520573 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_24 x) + (((-3319037 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_25 x + ((-1287392 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_26 x))) := by
  rw [node647_check, Integer.Sparse.eval_merge]
  rw [node643_eval, node646_eval]

theorem node648_check : node648 =
    Integer.Sparse.merge node641 node647 := by decide +kernel

theorem node648_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node648 x = (((((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_13 x + (((-106086 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_14 x + ((-639546 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_15 x)) + ((((-3010232 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_16 x + ((1121311 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_17 x) + (((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_18 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_19 x))) + ((((233548 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_20 x + (((-299084 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_21 x + ((7037228 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_22 x)) + ((((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_23 x + ((2520573 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_24 x) + (((-3319037 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_25 x + ((-1287392 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_26 x)))) := by
  rw [node648_check, Integer.Sparse.eval_merge]
  rw [node641_eval, node647_eval]

theorem node649_check : node649 =
    Integer.Sparse.merge node635 node648 := by decide +kernel

theorem node649_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node649 x = ((((((2605212 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_0 x + (((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_1 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_2 x)) + (((1227195 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_3 x + (((1483542 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_4 x + ((619147 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_5 x))) + ((((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_6 x + (((-1723883 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_7 x + ((2916394 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_8 x)) + ((((2310344 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_9 x + ((2189272 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_10 x) + (((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_11 x + ((1177088 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_12 x)))) + (((((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_13 x + (((-106086 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_14 x + ((-639546 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_15 x)) + ((((-3010232 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_16 x + ((1121311 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_17 x) + (((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_18 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_19 x))) + ((((233548 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_20 x + (((-299084 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_21 x + ((7037228 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_22 x)) + ((((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_23 x + ((2520573 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_24 x) + (((-3319037 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_25 x + ((-1287392 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_26 x))))) := by
  rw [node649_check, Integer.Sparse.eval_merge]
  rw [node635_eval, node648_eval]

theorem node650_check : node650 =
    Integer.Sparse.merge (Integer.Sparse.scale (312826) entry_25_1) (Integer.Sparse.scale (5876220) entry_25_2) := by decide +kernel

theorem node650_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node650 x = (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_1 x + ((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_2 x) := by
  rw [node650_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node651_check : node651 =
    Integer.Sparse.merge (Integer.Sparse.scale (-9952367) entry_25_0) node650 := by decide +kernel

theorem node651_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node651 x = (((-9952367 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_0 x + (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_1 x + ((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_2 x)) := by
  rw [node651_check, Integer.Sparse.eval_merge]
  rw [node650_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node652_check : node652 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1112872) entry_25_4) (Integer.Sparse.scale (869639) entry_25_5) := by decide +kernel

theorem node652_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node652 x = (((-1112872 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_4 x + ((869639 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_5 x) := by
  rw [node652_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node653_check : node653 =
    Integer.Sparse.merge (Integer.Sparse.scale (2993143) entry_25_3) node652 := by decide +kernel

theorem node653_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node653 x = (((2993143 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_3 x + (((-1112872 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_4 x + ((869639 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_5 x)) := by
  rw [node653_check, Integer.Sparse.eval_merge]
  rw [node652_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node654_check : node654 =
    Integer.Sparse.merge node651 node653 := by decide +kernel

theorem node654_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node654 x = ((((-9952367 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_0 x + (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_1 x + ((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_2 x)) + (((2993143 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_3 x + (((-1112872 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_4 x + ((869639 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_5 x))) := by
  rw [node654_check, Integer.Sparse.eval_merge]
  rw [node651_eval, node653_eval]

theorem node655_check : node655 =
    Integer.Sparse.merge (Integer.Sparse.scale (4284472) entry_25_7) (Integer.Sparse.scale (-10448615) entry_25_8) := by decide +kernel

theorem node655_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node655 x = (((4284472 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_7 x + ((-10448615 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_8 x) := by
  rw [node655_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node656_check : node656 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1973233) entry_25_6) node655 := by decide +kernel

theorem node656_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node656 x = (((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_6 x + (((4284472 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_7 x + ((-10448615 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_8 x)) := by
  rw [node656_check, Integer.Sparse.eval_merge]
  rw [node655_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node657_check : node657 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1413894) entry_25_9) (Integer.Sparse.scale (-9602945) entry_25_10) := by decide +kernel

theorem node657_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node657 x = (((-1413894 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_9 x + ((-9602945 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_10 x) := by
  rw [node657_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node658_check : node658 =
    Integer.Sparse.merge (Integer.Sparse.scale (458016) entry_25_11) (Integer.Sparse.scale (-3205049) entry_25_12) := by decide +kernel

theorem node658_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node658 x = (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_11 x + ((-3205049 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_12 x) := by
  rw [node658_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node659_check : node659 =
    Integer.Sparse.merge node657 node658 := by decide +kernel

theorem node659_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node659 x = ((((-1413894 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_9 x + ((-9602945 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_10 x) + (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_11 x + ((-3205049 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_12 x)) := by
  rw [node659_check, Integer.Sparse.eval_merge]
  rw [node657_eval, node658_eval]

theorem node660_check : node660 =
    Integer.Sparse.merge node656 node659 := by decide +kernel

theorem node660_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node660 x = ((((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_6 x + (((4284472 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_7 x + ((-10448615 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_8 x)) + ((((-1413894 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_9 x + ((-9602945 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_10 x) + (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_11 x + ((-3205049 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_12 x))) := by
  rw [node660_check, Integer.Sparse.eval_merge]
  rw [node656_eval, node659_eval]

theorem node661_check : node661 =
    Integer.Sparse.merge node654 node660 := by decide +kernel

theorem node661_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node661 x = (((((-9952367 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_0 x + (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_1 x + ((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_2 x)) + (((2993143 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_3 x + (((-1112872 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_4 x + ((869639 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_5 x))) + ((((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_6 x + (((4284472 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_7 x + ((-10448615 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_8 x)) + ((((-1413894 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_9 x + ((-9602945 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_10 x) + (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_11 x + ((-3205049 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_12 x)))) := by
  rw [node661_check, Integer.Sparse.eval_merge]
  rw [node654_eval, node660_eval]

theorem node662_check : node662 =
    Integer.Sparse.merge (Integer.Sparse.scale (2607707) entry_25_14) (Integer.Sparse.scale (-4918260) entry_25_15) := by decide +kernel

theorem node662_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node662 x = (((2607707 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_14 x + ((-4918260 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_15 x) := by
  rw [node662_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node663_check : node663 =
    Integer.Sparse.merge (Integer.Sparse.scale (1956747) entry_25_13) node662 := by decide +kernel

theorem node663_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node663 x = (((1956747 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_13 x + (((2607707 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_14 x + ((-4918260 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_15 x)) := by
  rw [node663_check, Integer.Sparse.eval_merge]
  rw [node662_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node664_check : node664 =
    Integer.Sparse.merge (Integer.Sparse.scale (6368365) entry_25_16) (Integer.Sparse.scale (6669123) entry_25_17) := by decide +kernel

theorem node664_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node664 x = (((6368365 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_16 x + ((6669123 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_17 x) := by
  rw [node664_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node665_check : node665 =
    Integer.Sparse.merge (Integer.Sparse.scale (17682257) entry_25_18) (Integer.Sparse.scale (-1930609) entry_25_19) := by decide +kernel

theorem node665_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node665 x = (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_18 x + ((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_19 x) := by
  rw [node665_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node666_check : node666 =
    Integer.Sparse.merge node664 node665 := by decide +kernel

theorem node666_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node666 x = ((((6368365 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_16 x + ((6669123 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_17 x) + (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_18 x + ((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_19 x)) := by
  rw [node666_check, Integer.Sparse.eval_merge]
  rw [node664_eval, node665_eval]

theorem node667_check : node667 =
    Integer.Sparse.merge node663 node666 := by decide +kernel

theorem node667_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node667 x = ((((1956747 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_13 x + (((2607707 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_14 x + ((-4918260 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_15 x)) + ((((6368365 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_16 x + ((6669123 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_17 x) + (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_18 x + ((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_19 x))) := by
  rw [node667_check, Integer.Sparse.eval_merge]
  rw [node663_eval, node666_eval]

theorem node668_check : node668 =
    Integer.Sparse.merge (Integer.Sparse.scale (-12045329) entry_25_21) (Integer.Sparse.scale (-20572372) entry_25_22) := by decide +kernel

theorem node668_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node668 x = (((-12045329 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_21 x + ((-20572372 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_22 x) := by
  rw [node668_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node669_check : node669 =
    Integer.Sparse.merge (Integer.Sparse.scale (1646149) entry_25_20) node668 := by decide +kernel

theorem node669_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node669 x = (((1646149 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_20 x + (((-12045329 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_21 x + ((-20572372 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_22 x)) := by
  rw [node669_check, Integer.Sparse.eval_merge]
  rw [node668_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node670_check : node670 =
    Integer.Sparse.merge (Integer.Sparse.scale (6264265) entry_25_23) (Integer.Sparse.scale (-3319037) entry_25_24) := by decide +kernel

theorem node670_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node670 x = (((6264265 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_23 x + ((-3319037 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_24 x) := by
  rw [node670_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node671_check : node671 =
    Integer.Sparse.merge (Integer.Sparse.scale (24934572) entry_25_25) (Integer.Sparse.scale (4540900) entry_25_26) := by decide +kernel

theorem node671_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node671 x = (((24934572 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_25 x + ((4540900 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_26 x) := by
  rw [node671_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node672_check : node672 =
    Integer.Sparse.merge node670 node671 := by decide +kernel

theorem node672_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node672 x = ((((6264265 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_23 x + ((-3319037 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_24 x) + (((24934572 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_25 x + ((4540900 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_26 x)) := by
  rw [node672_check, Integer.Sparse.eval_merge]
  rw [node670_eval, node671_eval]

theorem node673_check : node673 =
    Integer.Sparse.merge node669 node672 := by decide +kernel

theorem node673_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node673 x = ((((1646149 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_20 x + (((-12045329 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_21 x + ((-20572372 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_22 x)) + ((((6264265 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_23 x + ((-3319037 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_24 x) + (((24934572 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_25 x + ((4540900 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_26 x))) := by
  rw [node673_check, Integer.Sparse.eval_merge]
  rw [node669_eval, node672_eval]

theorem node674_check : node674 =
    Integer.Sparse.merge node667 node673 := by decide +kernel

theorem node674_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node674 x = (((((1956747 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_13 x + (((2607707 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_14 x + ((-4918260 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_15 x)) + ((((6368365 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_16 x + ((6669123 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_17 x) + (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_18 x + ((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_19 x))) + ((((1646149 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_20 x + (((-12045329 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_21 x + ((-20572372 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_22 x)) + ((((6264265 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_23 x + ((-3319037 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_24 x) + (((24934572 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_25 x + ((4540900 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_26 x)))) := by
  rw [node674_check, Integer.Sparse.eval_merge]
  rw [node667_eval, node673_eval]

theorem node675_check : node675 =
    Integer.Sparse.merge node661 node674 := by decide +kernel

theorem node675_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node675 x = ((((((-9952367 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_0 x + (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_1 x + ((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_2 x)) + (((2993143 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_3 x + (((-1112872 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_4 x + ((869639 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_5 x))) + ((((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_6 x + (((4284472 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_7 x + ((-10448615 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_8 x)) + ((((-1413894 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_9 x + ((-9602945 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_10 x) + (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_11 x + ((-3205049 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_12 x)))) + (((((1956747 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_13 x + (((2607707 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_14 x + ((-4918260 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_15 x)) + ((((6368365 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_16 x + ((6669123 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_17 x) + (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_18 x + ((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_19 x))) + ((((1646149 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_20 x + (((-12045329 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_21 x + ((-20572372 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_22 x)) + ((((6264265 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_23 x + ((-3319037 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_24 x) + (((24934572 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_25 x + ((4540900 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_26 x))))) := by
  rw [node675_check, Integer.Sparse.eval_merge]
  rw [node661_eval, node674_eval]

end MUB6.Certificate.GramAssembly.Block3

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

theorem sum_expand_27 {R : Type*} [AddCommMonoid R] (F : Fin 27 → R) :
    (∑ i, F i) = ((((F 0 + (F 1 + F 2)) + (F 3 + (F 4 + F 5))) + ((F 6 + (F 7 + F 8)) + ((F 9 + F 10) + (F 11 + F 12)))) + (((F 13 + (F 14 + F 15)) + ((F 16 + F 17) + (F 18 + F 19))) + ((F 20 + (F 21 + F 22)) + ((F 23 + F 24) + (F 25 + F 26))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F 0 + (F 1 + (F 2 + (F 3 + (F 4 + (F 5 + (F 6 + (F 7 + (F 8 + (F 9 + (F 10 + (F 11 + (F 12 + (F 13 + (F 14 + (F 15 + (F 16 + (F 17 + (F 18 + (F 19 + (F 20 + (F 21 + (F 22 + (F 23 + (F 24 + (F 25 + (F 26 + 0))))))))))))))))))))))))))) = ((((F 0 + (F 1 + F 2)) + (F 3 + (F 4 + F 5))) + ((F 6 + (F 7 + F 8)) + ((F 9 + F 10) + (F 11 + F 12)))) + (((F 13 + (F 14 + F 15)) + ((F 16 + F 17) + (F 18 + F 19))) + ((F 20 + (F 21 + F 22)) + ((F 23 + F 24) + (F 25 + F 26)))))
  simp only [add_zero, add_assoc]

end MUB6.Certificate.GramAssembly

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

open scoped BigOperators

theorem row_eval_0 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node25 x =
      ∑ j : Fin 27, (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x := by
  rw [node25_eval]
  exact (sum_expand_27 (fun j => (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x)).symm

theorem row_eval_1 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node51 x =
      ∑ j : Fin 27, (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x := by
  rw [node51_eval]
  exact (sum_expand_27 (fun j => (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x)).symm

theorem row_eval_2 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node77 x =
      ∑ j : Fin 27, (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x := by
  rw [node77_eval]
  exact (sum_expand_27 (fun j => (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x)).symm

theorem row_eval_3 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node103 x =
      ∑ j : Fin 27, (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x := by
  rw [node103_eval]
  exact (sum_expand_27 (fun j => (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x)).symm

theorem row_eval_4 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node129 x =
      ∑ j : Fin 27, (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x := by
  rw [node129_eval]
  exact (sum_expand_27 (fun j => (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x)).symm

theorem row_eval_6 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node181 x =
      ∑ j : Fin 27, (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x := by
  rw [node181_eval]
  exact (sum_expand_27 (fun j => (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x)).symm

theorem row_eval_10 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node285 x =
      ∑ j : Fin 27, (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x := by
  rw [node285_eval]
  exact (sum_expand_27 (fun j => (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x)).symm

theorem row_eval_11 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node311 x =
      ∑ j : Fin 27, (weights 11 j : ℝ) * Integer.Sparse.eval (entries 11 j) x := by
  rw [node311_eval]
  exact (sum_expand_27 (fun j => (weights 11 j : ℝ) * Integer.Sparse.eval (entries 11 j) x)).symm

theorem row_eval_12 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node337 x =
      ∑ j : Fin 27, (weights 12 j : ℝ) * Integer.Sparse.eval (entries 12 j) x := by
  rw [node337_eval]
  exact (sum_expand_27 (fun j => (weights 12 j : ℝ) * Integer.Sparse.eval (entries 12 j) x)).symm

theorem row_eval_13 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node363 x =
      ∑ j : Fin 27, (weights 13 j : ℝ) * Integer.Sparse.eval (entries 13 j) x := by
  rw [node363_eval]
  exact (sum_expand_27 (fun j => (weights 13 j : ℝ) * Integer.Sparse.eval (entries 13 j) x)).symm

theorem row_eval_14 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node389 x =
      ∑ j : Fin 27, (weights 14 j : ℝ) * Integer.Sparse.eval (entries 14 j) x := by
  rw [node389_eval]
  exact (sum_expand_27 (fun j => (weights 14 j : ℝ) * Integer.Sparse.eval (entries 14 j) x)).symm

theorem row_eval_15 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node415 x =
      ∑ j : Fin 27, (weights 15 j : ℝ) * Integer.Sparse.eval (entries 15 j) x := by
  rw [node415_eval]
  exact (sum_expand_27 (fun j => (weights 15 j : ℝ) * Integer.Sparse.eval (entries 15 j) x)).symm

theorem row_eval_16 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node441 x =
      ∑ j : Fin 27, (weights 16 j : ℝ) * Integer.Sparse.eval (entries 16 j) x := by
  rw [node441_eval]
  exact (sum_expand_27 (fun j => (weights 16 j : ℝ) * Integer.Sparse.eval (entries 16 j) x)).symm

theorem row_eval_18 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node493 x =
      ∑ j : Fin 27, (weights 18 j : ℝ) * Integer.Sparse.eval (entries 18 j) x := by
  rw [node493_eval]
  exact (sum_expand_27 (fun j => (weights 18 j : ℝ) * Integer.Sparse.eval (entries 18 j) x)).symm

theorem row_eval_19 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node519 x =
      ∑ j : Fin 27, (weights 19 j : ℝ) * Integer.Sparse.eval (entries 19 j) x := by
  rw [node519_eval]
  exact (sum_expand_27 (fun j => (weights 19 j : ℝ) * Integer.Sparse.eval (entries 19 j) x)).symm

theorem row_eval_20 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node545 x =
      ∑ j : Fin 27, (weights 20 j : ℝ) * Integer.Sparse.eval (entries 20 j) x := by
  rw [node545_eval]
  exact (sum_expand_27 (fun j => (weights 20 j : ℝ) * Integer.Sparse.eval (entries 20 j) x)).symm

theorem row_eval_23 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node623 x =
      ∑ j : Fin 27, (weights 23 j : ℝ) * Integer.Sparse.eval (entries 23 j) x := by
  rw [node623_eval]
  exact (sum_expand_27 (fun j => (weights 23 j : ℝ) * Integer.Sparse.eval (entries 23 j) x)).symm

theorem row_eval_24 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node649 x =
      ∑ j : Fin 27, (weights 24 j : ℝ) * Integer.Sparse.eval (entries 24 j) x := by
  rw [node649_eval]
  exact (sum_expand_27 (fun j => (weights 24 j : ℝ) * Integer.Sparse.eval (entries 24 j) x)).symm

theorem row_eval_25 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node675 x =
      ∑ j : Fin 27, (weights 25 j : ℝ) * Integer.Sparse.eval (entries 25 j) x := by
  rw [node675_eval]
  exact (sum_expand_27 (fun j => (weights 25 j : ℝ) * Integer.Sparse.eval (entries 25 j) x)).symm

theorem rows_eval_e_oai (i : Fin 27) (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval (rows i) x =
      ∑ j : Fin 27, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  fin_cases i
  · exact row_eval_0 x
  · exact row_eval_1 x
  · exact row_eval_2 x
  · exact row_eval_3 x
  · exact row_eval_4 x
  · exact row_eval_5_e x
  · exact row_eval_6 x
  · exact row_eval_7_e x
  · exact row_eval_8_e x
  · exact row_eval_9_e x
  · exact row_eval_10 x
  · exact row_eval_11 x
  · exact row_eval_12 x
  · exact row_eval_13 x
  · exact row_eval_14 x
  · exact row_eval_15 x
  · exact row_eval_16 x
  · exact row_eval_17_e x
  · exact row_eval_18 x
  · exact row_eval_19 x
  · exact row_eval_20 x
  · exact row_eval_21_e x
  · exact row_eval_22_e x
  · exact row_eval_23 x
  · exact row_eval_24 x
  · exact row_eval_25 x
  · exact row_eval_26_e x

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block3.rows_eval_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block3.rows_eval_e_oai
