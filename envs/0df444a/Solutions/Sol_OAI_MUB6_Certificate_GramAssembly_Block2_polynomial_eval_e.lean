-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block2.polynomial_eval_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:28:35.066239+00:00
-- url     : https://prove2.me/submissions/b47e4215-4b25-4c1b-af13-569e448e1789

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E004
import Definitions.Def_OAIQ106E005
import Definitions.Def_OAIQ106E196

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block2Part0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

theorem node0_check : node0 =
    Integer.Sparse.merge (Integer.Sparse.scale (4921588) entry_0_0) (Integer.Sparse.scale (1243280) entry_0_1) := by decide +kernel

theorem node0_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node0 x = (((4921588 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + ((1243280 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x) := by
  rw [node0_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node1_check : node1 =
    Integer.Sparse.merge (Integer.Sparse.scale (-624690) entry_0_3) (Integer.Sparse.scale (1603998) entry_0_4) := by decide +kernel

theorem node1_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node1 x = (((-624690 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((1603998 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x) := by
  rw [node1_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node2_check : node2 =
    Integer.Sparse.merge (Integer.Sparse.scale (-7309127) entry_0_2) node1 := by decide +kernel

theorem node2_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node2 x = (((-7309127 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x + (((-624690 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((1603998 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x)) := by
  rw [node2_check, Integer.Sparse.eval_merge]
  rw [node1_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node3_check : node3 =
    Integer.Sparse.merge node0 node2 := by decide +kernel

theorem node3_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node3 x = ((((4921588 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + ((1243280 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x) + (((-7309127 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x + (((-624690 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((1603998 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x))) := by
  rw [node3_check, Integer.Sparse.eval_merge]
  rw [node0_eval, node2_eval]

theorem node4_check : node4 =
    Integer.Sparse.merge (Integer.Sparse.scale (3367935) entry_0_6) (Integer.Sparse.scale (-1583320) entry_0_7) := by decide +kernel

theorem node4_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node4 x = (((3367935 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x + ((-1583320 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x) := by
  rw [node4_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node5_check : node5 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2795071) entry_0_5) node4 := by decide +kernel

theorem node5_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node5 x = (((-2795071 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x + (((3367935 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x + ((-1583320 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x)) := by
  rw [node5_check, Integer.Sparse.eval_merge]
  rw [node4_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node6_check : node6 =
    Integer.Sparse.merge (Integer.Sparse.scale (-248222) entry_0_9) (Integer.Sparse.scale (702355) entry_0_10) := by decide +kernel

theorem node6_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node6 x = (((-248222 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + ((702355 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x) := by
  rw [node6_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node7_check : node7 =
    Integer.Sparse.merge (Integer.Sparse.scale (2340968) entry_0_8) node6 := by decide +kernel

theorem node7_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node7 x = (((2340968 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x + (((-248222 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + ((702355 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x)) := by
  rw [node7_check, Integer.Sparse.eval_merge]
  rw [node6_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node8_check : node8 =
    Integer.Sparse.merge node5 node7 := by decide +kernel

theorem node8_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node8 x = ((((-2795071 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x + (((3367935 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x + ((-1583320 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x)) + (((2340968 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x + (((-248222 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + ((702355 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x))) := by
  rw [node8_check, Integer.Sparse.eval_merge]
  rw [node5_eval, node7_eval]

theorem node9_check : node9 =
    Integer.Sparse.merge node3 node8 := by decide +kernel

theorem node9_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node9 x = (((((4921588 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + ((1243280 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x) + (((-7309127 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x + (((-624690 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((1603998 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x))) + ((((-2795071 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x + (((3367935 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x + ((-1583320 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x)) + (((2340968 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x + (((-248222 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x + ((702355 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x)))) := by
  rw [node9_check, Integer.Sparse.eval_merge]
  rw [node3_eval, node8_eval]

theorem node10_check : node10 =
    Integer.Sparse.merge (Integer.Sparse.scale (1243280) entry_1_0) (Integer.Sparse.scale (1259868) entry_1_1) := by decide +kernel

theorem node10_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node10 x = (((1243280 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + ((1259868 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x) := by
  rw [node10_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node11_check : node11 =
    Integer.Sparse.merge (Integer.Sparse.scale (-210702) entry_1_3) (Integer.Sparse.scale (1253342) entry_1_4) := by decide +kernel

theorem node11_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node11 x = (((-210702 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((1253342 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x) := by
  rw [node11_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node12_check : node12 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2872973) entry_1_2) node11 := by decide +kernel

theorem node12_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node12 x = (((-2872973 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x + (((-210702 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((1253342 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x)) := by
  rw [node12_check, Integer.Sparse.eval_merge]
  rw [node11_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node13_check : node13 =
    Integer.Sparse.merge node10 node12 := by decide +kernel

theorem node13_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node13 x = ((((1243280 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + ((1259868 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x) + (((-2872973 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x + (((-210702 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((1253342 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x))) := by
  rw [node13_check, Integer.Sparse.eval_merge]
  rw [node10_eval, node12_eval]

theorem node14_check : node14 =
    Integer.Sparse.merge (Integer.Sparse.scale (1682712) entry_1_6) (Integer.Sparse.scale (-885538) entry_1_7) := by decide +kernel

theorem node14_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node14 x = (((1682712 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + ((-885538 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x) := by
  rw [node14_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node15_check : node15 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2034588) entry_1_5) node14 := by decide +kernel

theorem node15_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node15 x = (((-2034588 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x + (((1682712 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + ((-885538 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x)) := by
  rw [node15_check, Integer.Sparse.eval_merge]
  rw [node14_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node16_check : node16 =
    Integer.Sparse.merge (Integer.Sparse.scale (-409660) entry_1_9) (Integer.Sparse.scale (794) entry_1_10) := by decide +kernel

theorem node16_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node16 x = (((-409660 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((794 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x) := by
  rw [node16_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node17_check : node17 =
    Integer.Sparse.merge (Integer.Sparse.scale (2724267) entry_1_8) node16 := by decide +kernel

theorem node17_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node17 x = (((2724267 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x + (((-409660 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((794 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x)) := by
  rw [node17_check, Integer.Sparse.eval_merge]
  rw [node16_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node18_check : node18 =
    Integer.Sparse.merge node15 node17 := by decide +kernel

theorem node18_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node18 x = ((((-2034588 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x + (((1682712 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + ((-885538 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x)) + (((2724267 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x + (((-409660 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((794 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x))) := by
  rw [node18_check, Integer.Sparse.eval_merge]
  rw [node15_eval, node17_eval]

theorem node19_check : node19 =
    Integer.Sparse.merge node13 node18 := by decide +kernel

theorem node19_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node19 x = (((((1243280 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + ((1259868 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x) + (((-2872973 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x + (((-210702 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + ((1253342 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x))) + ((((-2034588 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x + (((1682712 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + ((-885538 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x)) + (((2724267 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x + (((-409660 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((794 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x)))) := by
  rw [node19_check, Integer.Sparse.eval_merge]
  rw [node13_eval, node18_eval]

theorem node20_check : node20 =
    Integer.Sparse.merge (Integer.Sparse.scale (-7309127) entry_2_0) (Integer.Sparse.scale (-2872973) entry_2_1) := by decide +kernel

theorem node20_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node20 x = (((-7309127 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + ((-2872973 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x) := by
  rw [node20_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node21_check : node21 =
    Integer.Sparse.merge (Integer.Sparse.scale (1150717) entry_2_3) (Integer.Sparse.scale (-3887583) entry_2_4) := by decide +kernel

theorem node21_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node21 x = (((1150717 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((-3887583 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x) := by
  rw [node21_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node22_check : node22 =
    Integer.Sparse.merge (Integer.Sparse.scale (13379731) entry_2_2) node21 := by decide +kernel

theorem node22_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node22 x = (((13379731 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x + (((1150717 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((-3887583 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x)) := by
  rw [node22_check, Integer.Sparse.eval_merge]
  rw [node21_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node23_check : node23 =
    Integer.Sparse.merge node20 node22 := by decide +kernel

theorem node23_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node23 x = ((((-7309127 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + ((-2872973 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x) + (((13379731 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x + (((1150717 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((-3887583 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x))) := by
  rw [node23_check, Integer.Sparse.eval_merge]
  rw [node20_eval, node22_eval]

theorem node24_check : node24 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6302383) entry_2_6) (Integer.Sparse.scale (2324542) entry_2_7) := by decide +kernel

theorem node24_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node24 x = (((-6302383 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + ((2324542 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x) := by
  rw [node24_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node25_check : node25 =
    Integer.Sparse.merge (Integer.Sparse.scale (6470784) entry_2_5) node24 := by decide +kernel

theorem node25_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node25 x = (((6470784 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x + (((-6302383 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + ((2324542 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x)) := by
  rw [node25_check, Integer.Sparse.eval_merge]
  rw [node24_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node26_check : node26 =
    Integer.Sparse.merge (Integer.Sparse.scale (725259) entry_2_9) (Integer.Sparse.scale (-836950) entry_2_10) := by decide +kernel

theorem node26_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node26 x = (((725259 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((-836950 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x) := by
  rw [node26_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node27_check : node27 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6055529) entry_2_8) node26 := by decide +kernel

theorem node27_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node27 x = (((-6055529 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x + (((725259 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((-836950 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x)) := by
  rw [node27_check, Integer.Sparse.eval_merge]
  rw [node26_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node28_check : node28 =
    Integer.Sparse.merge node25 node27 := by decide +kernel

theorem node28_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node28 x = ((((6470784 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x + (((-6302383 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + ((2324542 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x)) + (((-6055529 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x + (((725259 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((-836950 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x))) := by
  rw [node28_check, Integer.Sparse.eval_merge]
  rw [node25_eval, node27_eval]

theorem node29_check : node29 =
    Integer.Sparse.merge node23 node28 := by decide +kernel

theorem node29_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node29 x = (((((-7309127 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + ((-2872973 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x) + (((13379731 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x + (((1150717 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((-3887583 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x))) + ((((6470784 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x + (((-6302383 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + ((2324542 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x)) + (((-6055529 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x + (((725259 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((-836950 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x)))) := by
  rw [node29_check, Integer.Sparse.eval_merge]
  rw [node23_eval, node28_eval]

theorem node30_check : node30 =
    Integer.Sparse.merge (Integer.Sparse.scale (-624690) entry_3_0) (Integer.Sparse.scale (-210702) entry_3_1) := by decide +kernel

theorem node30_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node30 x = (((-624690 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-210702 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) := by
  rw [node30_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node31_check : node31 =
    Integer.Sparse.merge (Integer.Sparse.scale (690108) entry_3_3) (Integer.Sparse.scale (8436) entry_3_4) := by decide +kernel

theorem node31_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node31 x = (((690108 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((8436 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x) := by
  rw [node31_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block2Part1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

theorem node32_check : node32 =
    Integer.Sparse.merge (Integer.Sparse.scale (1150717) entry_3_2) node31 := by decide +kernel

theorem node32_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node32 x = (((1150717 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((690108 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((8436 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x)) := by
  rw [node32_check, Integer.Sparse.eval_merge]
  rw [node31_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node33_check : node33 =
    Integer.Sparse.merge node30 node32 := by decide +kernel

theorem node33_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node33 x = ((((-624690 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-210702 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) + (((1150717 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((690108 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((8436 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x))) := by
  rw [node33_check, Integer.Sparse.eval_merge]
  rw [node30_eval, node32_eval]

theorem node34_check : node34 =
    Integer.Sparse.merge (Integer.Sparse.scale (-693384) entry_3_6) (Integer.Sparse.scale (-181298) entry_3_7) := by decide +kernel

theorem node34_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node34 x = (((-693384 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + ((-181298 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x) := by
  rw [node34_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node35_check : node35 =
    Integer.Sparse.merge (Integer.Sparse.scale (557254) entry_3_5) node34 := by decide +kernel

theorem node35_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node35 x = (((557254 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + (((-693384 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + ((-181298 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x)) := by
  rw [node35_check, Integer.Sparse.eval_merge]
  rw [node34_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node36_check : node36 =
    Integer.Sparse.merge (Integer.Sparse.scale (-526328) entry_3_9) (Integer.Sparse.scale (-588904) entry_3_10) := by decide +kernel

theorem node36_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node36 x = (((-526328 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((-588904 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x) := by
  rw [node36_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node37_check : node37 =
    Integer.Sparse.merge (Integer.Sparse.scale (1653368) entry_3_8) node36 := by decide +kernel

theorem node37_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node37 x = (((1653368 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + (((-526328 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((-588904 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x)) := by
  rw [node37_check, Integer.Sparse.eval_merge]
  rw [node36_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node38_check : node38 =
    Integer.Sparse.merge node35 node37 := by decide +kernel

theorem node38_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node38 x = ((((557254 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + (((-693384 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + ((-181298 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x)) + (((1653368 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + (((-526328 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((-588904 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x))) := by
  rw [node38_check, Integer.Sparse.eval_merge]
  rw [node35_eval, node37_eval]

theorem node39_check : node39 =
    Integer.Sparse.merge node33 node38 := by decide +kernel

theorem node39_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node39 x = (((((-624690 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-210702 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) + (((1150717 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((690108 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((8436 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x))) + ((((557254 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + (((-693384 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + ((-181298 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x)) + (((1653368 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + (((-526328 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((-588904 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x)))) := by
  rw [node39_check, Integer.Sparse.eval_merge]
  rw [node33_eval, node38_eval]

theorem node40_check : node40 =
    Integer.Sparse.merge (Integer.Sparse.scale (1603998) entry_4_0) (Integer.Sparse.scale (1253342) entry_4_1) := by decide +kernel

theorem node40_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node40 x = (((1603998 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((1253342 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) := by
  rw [node40_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node41_check : node41 =
    Integer.Sparse.merge (Integer.Sparse.scale (8436) entry_4_3) (Integer.Sparse.scale (1940509) entry_4_4) := by decide +kernel

theorem node41_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node41 x = (((8436 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((1940509 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x) := by
  rw [node41_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node42_check : node42 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3887583) entry_4_2) node41 := by decide +kernel

theorem node42_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node42 x = (((-3887583 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((8436 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((1940509 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x)) := by
  rw [node42_check, Integer.Sparse.eval_merge]
  rw [node41_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node43_check : node43 =
    Integer.Sparse.merge node40 node42 := by decide +kernel

theorem node43_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node43 x = ((((1603998 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((1253342 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) + (((-3887583 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((8436 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((1940509 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x))) := by
  rw [node43_check, Integer.Sparse.eval_merge]
  rw [node40_eval, node42_eval]

theorem node44_check : node44 =
    Integer.Sparse.merge (Integer.Sparse.scale (1935441) entry_4_6) (Integer.Sparse.scale (-879724) entry_4_7) := by decide +kernel

theorem node44_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node44 x = (((1935441 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + ((-879724 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x) := by
  rw [node44_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node45_check : node45 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2484968) entry_4_5) node44 := by decide +kernel

theorem node45_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node45 x = (((-2484968 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + (((1935441 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + ((-879724 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x)) := by
  rw [node45_check, Integer.Sparse.eval_merge]
  rw [node44_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node46_check : node46 =
    Integer.Sparse.merge (Integer.Sparse.scale (-709322) entry_4_9) (Integer.Sparse.scale (-233345) entry_4_10) := by decide +kernel

theorem node46_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node46 x = (((-709322 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((-233345 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x) := by
  rw [node46_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node47_check : node47 =
    Integer.Sparse.merge (Integer.Sparse.scale (3975384) entry_4_8) node46 := by decide +kernel

theorem node47_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node47 x = (((3975384 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + (((-709322 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((-233345 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x)) := by
  rw [node47_check, Integer.Sparse.eval_merge]
  rw [node46_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node48_check : node48 =
    Integer.Sparse.merge node45 node47 := by decide +kernel

theorem node48_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node48 x = ((((-2484968 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + (((1935441 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + ((-879724 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x)) + (((3975384 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + (((-709322 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((-233345 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x))) := by
  rw [node48_check, Integer.Sparse.eval_merge]
  rw [node45_eval, node47_eval]

theorem node49_check : node49 =
    Integer.Sparse.merge node43 node48 := by decide +kernel

theorem node49_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node49 x = (((((1603998 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((1253342 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) + (((-3887583 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((8436 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((1940509 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x))) + ((((-2484968 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + (((1935441 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x + ((-879724 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x)) + (((3975384 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + (((-709322 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x + ((-233345 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x)))) := by
  rw [node49_check, Integer.Sparse.eval_merge]
  rw [node43_eval, node48_eval]

theorem node50_check : node50 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2795071) entry_5_0) (Integer.Sparse.scale (-2034588) entry_5_1) := by decide +kernel

theorem node50_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node50 x = (((-2795071 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + ((-2034588 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x) := by
  rw [node50_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node51_check : node51 =
    Integer.Sparse.merge (Integer.Sparse.scale (557254) entry_5_3) (Integer.Sparse.scale (-2484968) entry_5_4) := by decide +kernel

theorem node51_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node51 x = (((557254 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + ((-2484968 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x) := by
  rw [node51_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node52_check : node52 =
    Integer.Sparse.merge (Integer.Sparse.scale (6470784) entry_5_2) node51 := by decide +kernel

theorem node52_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node52 x = (((6470784 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x + (((557254 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + ((-2484968 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x)) := by
  rw [node52_check, Integer.Sparse.eval_merge]
  rw [node51_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node53_check : node53 =
    Integer.Sparse.merge node50 node52 := by decide +kernel

theorem node53_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node53 x = ((((-2795071 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + ((-2034588 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x) + (((6470784 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x + (((557254 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + ((-2484968 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x))) := by
  rw [node53_check, Integer.Sparse.eval_merge]
  rw [node50_eval, node52_eval]

theorem node54_check : node54 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3363650) entry_5_6) (Integer.Sparse.scale (1243475) entry_5_7) := by decide +kernel

theorem node54_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node54 x = (((-3363650 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + ((1243475 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x) := by
  rw [node54_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node55_check : node55 =
    Integer.Sparse.merge (Integer.Sparse.scale (4332981) entry_5_5) node54 := by decide +kernel

theorem node55_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node55 x = (((4332981 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x + (((-3363650 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + ((1243475 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x)) := by
  rw [node55_check, Integer.Sparse.eval_merge]
  rw [node54_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node56_check : node56 =
    Integer.Sparse.merge (Integer.Sparse.scale (537643) entry_5_9) (Integer.Sparse.scale (-211242) entry_5_10) := by decide +kernel

theorem node56_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node56 x = (((537643 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + ((-211242 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x) := by
  rw [node56_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node57_check : node57 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4427358) entry_5_8) node56 := by decide +kernel

theorem node57_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node57 x = (((-4427358 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x + (((537643 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + ((-211242 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x)) := by
  rw [node57_check, Integer.Sparse.eval_merge]
  rw [node56_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node58_check : node58 =
    Integer.Sparse.merge node55 node57 := by decide +kernel

theorem node58_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node58 x = ((((4332981 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x + (((-3363650 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + ((1243475 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x)) + (((-4427358 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x + (((537643 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + ((-211242 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x))) := by
  rw [node58_check, Integer.Sparse.eval_merge]
  rw [node55_eval, node57_eval]

theorem node59_check : node59 =
    Integer.Sparse.merge node53 node58 := by decide +kernel

theorem node59_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node59 x = (((((-2795071 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + ((-2034588 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x) + (((6470784 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x + (((557254 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + ((-2484968 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x))) + ((((4332981 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x + (((-3363650 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + ((1243475 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x)) + (((-4427358 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x + (((537643 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + ((-211242 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x)))) := by
  rw [node59_check, Integer.Sparse.eval_merge]
  rw [node53_eval, node58_eval]

theorem node60_check : node60 =
    Integer.Sparse.merge (Integer.Sparse.scale (3367935) entry_6_0) (Integer.Sparse.scale (1682712) entry_6_1) := by decide +kernel

theorem node60_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node60 x = (((3367935 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + ((1682712 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x) := by
  rw [node60_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node61_check : node61 =
    Integer.Sparse.merge (Integer.Sparse.scale (-693384) entry_6_3) (Integer.Sparse.scale (1935441) entry_6_4) := by decide +kernel

theorem node61_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node61 x = (((-693384 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + ((1935441 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x) := by
  rw [node61_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node62_check : node62 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6302383) entry_6_2) node61 := by decide +kernel

theorem node62_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node62 x = (((-6302383 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x + (((-693384 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + ((1935441 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x)) := by
  rw [node62_check, Integer.Sparse.eval_merge]
  rw [node61_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node63_check : node63 =
    Integer.Sparse.merge node60 node62 := by decide +kernel

theorem node63_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node63 x = ((((3367935 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + ((1682712 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x) + (((-6302383 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x + (((-693384 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + ((1935441 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x))) := by
  rw [node63_check, Integer.Sparse.eval_merge]
  rw [node60_eval, node62_eval]

end MUB6.Certificate.GramAssembly.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block2Part2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

theorem node64_check : node64 =
    Integer.Sparse.merge (Integer.Sparse.scale (3298003) entry_6_6) (Integer.Sparse.scale (-1116848) entry_6_7) := by decide +kernel

theorem node64_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node64 x = (((3298003 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + ((-1116848 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x) := by
  rw [node64_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node65_check : node65 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3363650) entry_6_5) node64 := by decide +kernel

theorem node65_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node65 x = (((-3363650 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x + (((3298003 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + ((-1116848 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x)) := by
  rw [node65_check, Integer.Sparse.eval_merge]
  rw [node64_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node66_check : node66 =
    Integer.Sparse.merge (Integer.Sparse.scale (-234978) entry_6_9) (Integer.Sparse.scale (508720) entry_6_10) := by decide +kernel

theorem node66_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node66 x = (((-234978 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((508720 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x) := by
  rw [node66_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node67_check : node67 =
    Integer.Sparse.merge (Integer.Sparse.scale (2778884) entry_6_8) node66 := by decide +kernel

theorem node67_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node67 x = (((2778884 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x + (((-234978 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((508720 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x)) := by
  rw [node67_check, Integer.Sparse.eval_merge]
  rw [node66_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node68_check : node68 =
    Integer.Sparse.merge node65 node67 := by decide +kernel

theorem node68_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node68 x = ((((-3363650 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x + (((3298003 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + ((-1116848 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x)) + (((2778884 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x + (((-234978 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((508720 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x))) := by
  rw [node68_check, Integer.Sparse.eval_merge]
  rw [node65_eval, node67_eval]

theorem node69_check : node69 =
    Integer.Sparse.merge node63 node68 := by decide +kernel

theorem node69_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node69 x = (((((3367935 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + ((1682712 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x) + (((-6302383 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x + (((-693384 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + ((1935441 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x))) + ((((-3363650 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x + (((3298003 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + ((-1116848 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x)) + (((2778884 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x + (((-234978 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((508720 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x)))) := by
  rw [node69_check, Integer.Sparse.eval_merge]
  rw [node63_eval, node68_eval]

theorem node70_check : node70 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1583320) entry_7_0) (Integer.Sparse.scale (-885538) entry_7_1) := by decide +kernel

theorem node70_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node70 x = (((-1583320 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + ((-885538 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x) := by
  rw [node70_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node71_check : node71 =
    Integer.Sparse.merge (Integer.Sparse.scale (-181298) entry_7_3) (Integer.Sparse.scale (-879724) entry_7_4) := by decide +kernel

theorem node71_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node71 x = (((-181298 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + ((-879724 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x) := by
  rw [node71_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node72_check : node72 =
    Integer.Sparse.merge (Integer.Sparse.scale (2324542) entry_7_2) node71 := by decide +kernel

theorem node72_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node72 x = (((2324542 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x + (((-181298 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + ((-879724 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x)) := by
  rw [node72_check, Integer.Sparse.eval_merge]
  rw [node71_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node73_check : node73 =
    Integer.Sparse.merge node70 node72 := by decide +kernel

theorem node73_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node73 x = ((((-1583320 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + ((-885538 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x) + (((2324542 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x + (((-181298 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + ((-879724 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x))) := by
  rw [node73_check, Integer.Sparse.eval_merge]
  rw [node70_eval, node72_eval]

theorem node74_check : node74 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1116848) entry_7_6) (Integer.Sparse.scale (1720010) entry_7_7) := by decide +kernel

theorem node74_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node74 x = (((-1116848 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + ((1720010 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x) := by
  rw [node74_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node75_check : node75 =
    Integer.Sparse.merge (Integer.Sparse.scale (1243475) entry_7_5) node74 := by decide +kernel

theorem node75_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node75 x = (((1243475 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x + (((-1116848 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + ((1720010 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x)) := by
  rw [node75_check, Integer.Sparse.eval_merge]
  rw [node74_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node76_check : node76 =
    Integer.Sparse.merge (Integer.Sparse.scale (821982) entry_7_9) (Integer.Sparse.scale (282809) entry_7_10) := by decide +kernel

theorem node76_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node76 x = (((821982 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((282809 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x) := by
  rw [node76_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node77_check : node77 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3611042) entry_7_8) node76 := by decide +kernel

theorem node77_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node77 x = (((-3611042 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x + (((821982 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((282809 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x)) := by
  rw [node77_check, Integer.Sparse.eval_merge]
  rw [node76_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node78_check : node78 =
    Integer.Sparse.merge node75 node77 := by decide +kernel

theorem node78_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node78 x = ((((1243475 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x + (((-1116848 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + ((1720010 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x)) + (((-3611042 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x + (((821982 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((282809 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x))) := by
  rw [node78_check, Integer.Sparse.eval_merge]
  rw [node75_eval, node77_eval]

theorem node79_check : node79 =
    Integer.Sparse.merge node73 node78 := by decide +kernel

theorem node79_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node79 x = (((((-1583320 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + ((-885538 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x) + (((2324542 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x + (((-181298 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + ((-879724 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x))) + ((((1243475 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x + (((-1116848 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + ((1720010 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x)) + (((-3611042 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x + (((821982 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((282809 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x)))) := by
  rw [node79_check, Integer.Sparse.eval_merge]
  rw [node73_eval, node78_eval]

theorem node80_check : node80 =
    Integer.Sparse.merge (Integer.Sparse.scale (2340968) entry_8_0) (Integer.Sparse.scale (2724267) entry_8_1) := by decide +kernel

theorem node80_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node80 x = (((2340968 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + ((2724267 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x) := by
  rw [node80_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node81_check : node81 =
    Integer.Sparse.merge (Integer.Sparse.scale (1653368) entry_8_3) (Integer.Sparse.scale (3975384) entry_8_4) := by decide +kernel

theorem node81_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node81 x = (((1653368 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((3975384 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x) := by
  rw [node81_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node82_check : node82 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6055529) entry_8_2) node81 := by decide +kernel

theorem node82_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node82 x = (((-6055529 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x + (((1653368 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((3975384 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x)) := by
  rw [node82_check, Integer.Sparse.eval_merge]
  rw [node81_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node83_check : node83 =
    Integer.Sparse.merge node80 node82 := by decide +kernel

theorem node83_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node83 x = ((((2340968 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + ((2724267 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x) + (((-6055529 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x + (((1653368 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((3975384 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x))) := by
  rw [node83_check, Integer.Sparse.eval_merge]
  rw [node80_eval, node82_eval]

theorem node84_check : node84 =
    Integer.Sparse.merge (Integer.Sparse.scale (2778884) entry_8_6) (Integer.Sparse.scale (-3611042) entry_8_7) := by decide +kernel

theorem node84_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node84 x = (((2778884 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + ((-3611042 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x) := by
  rw [node84_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node85_check : node85 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4427358) entry_8_5) node84 := by decide +kernel

theorem node85_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node85 x = (((-4427358 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x + (((2778884 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + ((-3611042 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x)) := by
  rw [node85_check, Integer.Sparse.eval_merge]
  rw [node84_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node86_check : node86 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3403183) entry_8_9) (Integer.Sparse.scale (-2223239) entry_8_10) := by decide +kernel

theorem node86_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node86 x = (((-3403183 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((-2223239 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x) := by
  rw [node86_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node87_check : node87 =
    Integer.Sparse.merge (Integer.Sparse.scale (15022074) entry_8_8) node86 := by decide +kernel

theorem node87_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node87 x = (((15022074 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x + (((-3403183 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((-2223239 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x)) := by
  rw [node87_check, Integer.Sparse.eval_merge]
  rw [node86_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node88_check : node88 =
    Integer.Sparse.merge node85 node87 := by decide +kernel

theorem node88_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node88 x = ((((-4427358 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x + (((2778884 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + ((-3611042 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x)) + (((15022074 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x + (((-3403183 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((-2223239 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x))) := by
  rw [node88_check, Integer.Sparse.eval_merge]
  rw [node85_eval, node87_eval]

theorem node89_check : node89 =
    Integer.Sparse.merge node83 node88 := by decide +kernel

theorem node89_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node89 x = (((((2340968 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + ((2724267 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x) + (((-6055529 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x + (((1653368 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + ((3975384 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x))) + ((((-4427358 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x + (((2778884 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + ((-3611042 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x)) + (((15022074 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x + (((-3403183 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((-2223239 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x)))) := by
  rw [node89_check, Integer.Sparse.eval_merge]
  rw [node83_eval, node88_eval]

theorem node90_check : node90 =
    Integer.Sparse.merge (Integer.Sparse.scale (-248222) entry_9_0) (Integer.Sparse.scale (-409660) entry_9_1) := by decide +kernel

theorem node90_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node90 x = (((-248222 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + ((-409660 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x) := by
  rw [node90_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node91_check : node91 =
    Integer.Sparse.merge (Integer.Sparse.scale (-526328) entry_9_3) (Integer.Sparse.scale (-709322) entry_9_4) := by decide +kernel

theorem node91_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node91 x = (((-526328 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + ((-709322 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x) := by
  rw [node91_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node92_check : node92 =
    Integer.Sparse.merge (Integer.Sparse.scale (725259) entry_9_2) node91 := by decide +kernel

theorem node92_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node92 x = (((725259 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x + (((-526328 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + ((-709322 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x)) := by
  rw [node92_check, Integer.Sparse.eval_merge]
  rw [node91_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node93_check : node93 =
    Integer.Sparse.merge node90 node92 := by decide +kernel

theorem node93_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node93 x = ((((-248222 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + ((-409660 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x) + (((725259 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x + (((-526328 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + ((-709322 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x))) := by
  rw [node93_check, Integer.Sparse.eval_merge]
  rw [node90_eval, node92_eval]

theorem node94_check : node94 =
    Integer.Sparse.merge (Integer.Sparse.scale (-234978) entry_9_6) (Integer.Sparse.scale (821982) entry_9_7) := by decide +kernel

theorem node94_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node94 x = (((-234978 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + ((821982 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x) := by
  rw [node94_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node95_check : node95 =
    Integer.Sparse.merge (Integer.Sparse.scale (537643) entry_9_5) node94 := by decide +kernel

theorem node95_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node95 x = (((537643 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x + (((-234978 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + ((821982 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x)) := by
  rw [node95_check, Integer.Sparse.eval_merge]
  rw [node94_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block2Part3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

theorem node96_check : node96 =
    Integer.Sparse.merge (Integer.Sparse.scale (873834) entry_9_9) (Integer.Sparse.scale (642996) entry_9_10) := by decide +kernel

theorem node96_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node96 x = (((873834 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + ((642996 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x) := by
  rw [node96_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node97_check : node97 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3403183) entry_9_8) node96 := by decide +kernel

theorem node97_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node97 x = (((-3403183 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x + (((873834 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + ((642996 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x)) := by
  rw [node97_check, Integer.Sparse.eval_merge]
  rw [node96_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node98_check : node98 =
    Integer.Sparse.merge node95 node97 := by decide +kernel

theorem node98_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node98 x = ((((537643 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x + (((-234978 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + ((821982 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x)) + (((-3403183 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x + (((873834 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + ((642996 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x))) := by
  rw [node98_check, Integer.Sparse.eval_merge]
  rw [node95_eval, node97_eval]

theorem node99_check : node99 =
    Integer.Sparse.merge node93 node98 := by decide +kernel

theorem node99_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node99 x = (((((-248222 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + ((-409660 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x) + (((725259 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x + (((-526328 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + ((-709322 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x))) + ((((537643 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x + (((-234978 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + ((821982 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x)) + (((-3403183 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x + (((873834 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + ((642996 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x)))) := by
  rw [node99_check, Integer.Sparse.eval_merge]
  rw [node93_eval, node98_eval]

theorem node100_check : node100 =
    Integer.Sparse.merge (Integer.Sparse.scale (702355) entry_10_0) (Integer.Sparse.scale (794) entry_10_1) := by decide +kernel

theorem node100_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node100 x = (((702355 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + ((794 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x) := by
  rw [node100_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node101_check : node101 =
    Integer.Sparse.merge (Integer.Sparse.scale (-588904) entry_10_3) (Integer.Sparse.scale (-233345) entry_10_4) := by decide +kernel

theorem node101_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node101 x = (((-588904 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + ((-233345 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x) := by
  rw [node101_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node102_check : node102 =
    Integer.Sparse.merge (Integer.Sparse.scale (-836950) entry_10_2) node101 := by decide +kernel

theorem node102_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node102 x = (((-836950 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x + (((-588904 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + ((-233345 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x)) := by
  rw [node102_check, Integer.Sparse.eval_merge]
  rw [node101_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node103_check : node103 =
    Integer.Sparse.merge node100 node102 := by decide +kernel

theorem node103_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node103 x = ((((702355 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + ((794 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x) + (((-836950 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x + (((-588904 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + ((-233345 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x))) := by
  rw [node103_check, Integer.Sparse.eval_merge]
  rw [node100_eval, node102_eval]

theorem node104_check : node104 =
    Integer.Sparse.merge (Integer.Sparse.scale (508720) entry_10_6) (Integer.Sparse.scale (282809) entry_10_7) := by decide +kernel

theorem node104_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node104 x = (((508720 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + ((282809 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x) := by
  rw [node104_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node105_check : node105 =
    Integer.Sparse.merge (Integer.Sparse.scale (-211242) entry_10_5) node104 := by decide +kernel

theorem node105_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node105 x = (((-211242 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x + (((508720 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + ((282809 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x)) := by
  rw [node105_check, Integer.Sparse.eval_merge]
  rw [node104_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node106_check : node106 =
    Integer.Sparse.merge (Integer.Sparse.scale (642996) entry_10_9) (Integer.Sparse.scale (680229) entry_10_10) := by decide +kernel

theorem node106_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node106 x = (((642996 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + ((680229 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x) := by
  rw [node106_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node107_check : node107 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2223239) entry_10_8) node106 := by decide +kernel

theorem node107_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node107 x = (((-2223239 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x + (((642996 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + ((680229 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x)) := by
  rw [node107_check, Integer.Sparse.eval_merge]
  rw [node106_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node108_check : node108 =
    Integer.Sparse.merge node105 node107 := by decide +kernel

theorem node108_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node108 x = ((((-211242 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x + (((508720 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + ((282809 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x)) + (((-2223239 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x + (((642996 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + ((680229 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x))) := by
  rw [node108_check, Integer.Sparse.eval_merge]
  rw [node105_eval, node107_eval]

theorem node109_check : node109 =
    Integer.Sparse.merge node103 node108 := by decide +kernel

theorem node109_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node109 x = (((((702355 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + ((794 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x) + (((-836950 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x + (((-588904 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + ((-233345 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x))) + ((((-211242 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x + (((508720 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + ((282809 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x)) + (((-2223239 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x + (((642996 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + ((680229 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x)))) := by
  rw [node109_check, Integer.Sparse.eval_merge]
  rw [node103_eval, node108_eval]

theorem node110_check : node110 =
    Integer.Sparse.merge node9 node19 := by decide +kernel

theorem node110_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node110 x = (Integer.Sparse.eval node9 x + Integer.Sparse.eval node19 x) := by
  rw [node110_check, Integer.Sparse.eval_merge]

theorem node111_check : node111 =
    Integer.Sparse.merge node39 node49 := by decide +kernel

theorem node111_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node111 x = (Integer.Sparse.eval node39 x + Integer.Sparse.eval node49 x) := by
  rw [node111_check, Integer.Sparse.eval_merge]

theorem node112_check : node112 =
    Integer.Sparse.merge node29 node111 := by decide +kernel

theorem node112_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node112 x = (Integer.Sparse.eval node29 x + (Integer.Sparse.eval node39 x + Integer.Sparse.eval node49 x)) := by
  rw [node112_check, Integer.Sparse.eval_merge]
  rw [node111_eval]

theorem node113_check : node113 =
    Integer.Sparse.merge node110 node112 := by decide +kernel

theorem node113_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node113 x = ((Integer.Sparse.eval node9 x + Integer.Sparse.eval node19 x) + (Integer.Sparse.eval node29 x + (Integer.Sparse.eval node39 x + Integer.Sparse.eval node49 x))) := by
  rw [node113_check, Integer.Sparse.eval_merge]
  rw [node110_eval, node112_eval]

theorem node114_check : node114 =
    Integer.Sparse.merge node69 node79 := by decide +kernel

theorem node114_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node114 x = (Integer.Sparse.eval node69 x + Integer.Sparse.eval node79 x) := by
  rw [node114_check, Integer.Sparse.eval_merge]

theorem node115_check : node115 =
    Integer.Sparse.merge node59 node114 := by decide +kernel

theorem node115_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node115 x = (Integer.Sparse.eval node59 x + (Integer.Sparse.eval node69 x + Integer.Sparse.eval node79 x)) := by
  rw [node115_check, Integer.Sparse.eval_merge]
  rw [node114_eval]

theorem node116_check : node116 =
    Integer.Sparse.merge node99 node109 := by decide +kernel

theorem node116_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node116 x = (Integer.Sparse.eval node99 x + Integer.Sparse.eval node109 x) := by
  rw [node116_check, Integer.Sparse.eval_merge]

theorem node117_check : node117 =
    Integer.Sparse.merge node89 node116 := by decide +kernel

theorem node117_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node117 x = (Integer.Sparse.eval node89 x + (Integer.Sparse.eval node99 x + Integer.Sparse.eval node109 x)) := by
  rw [node117_check, Integer.Sparse.eval_merge]
  rw [node116_eval]

theorem node118_check : node118 =
    Integer.Sparse.merge node115 node117 := by decide +kernel

theorem node118_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node118 x = ((Integer.Sparse.eval node59 x + (Integer.Sparse.eval node69 x + Integer.Sparse.eval node79 x)) + (Integer.Sparse.eval node89 x + (Integer.Sparse.eval node99 x + Integer.Sparse.eval node109 x))) := by
  rw [node118_check, Integer.Sparse.eval_merge]
  rw [node115_eval, node117_eval]

theorem node119_check : node119 =
    Integer.Sparse.merge node113 node118 := by decide +kernel

theorem node119_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node119 x = (((Integer.Sparse.eval node9 x + Integer.Sparse.eval node19 x) + (Integer.Sparse.eval node29 x + (Integer.Sparse.eval node39 x + Integer.Sparse.eval node49 x))) + ((Integer.Sparse.eval node59 x + (Integer.Sparse.eval node69 x + Integer.Sparse.eval node79 x)) + (Integer.Sparse.eval node89 x + (Integer.Sparse.eval node99 x + Integer.Sparse.eval node109 x)))) := by
  rw [node119_check, Integer.Sparse.eval_merge]
  rw [node113_eval, node118_eval]

end MUB6.Certificate.GramAssembly.Block2

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

theorem sum_expand_11 {R : Type*} [AddCommMonoid R] (F : Fin 11 → R) :
    (∑ i, F i) = (((F 0 + F 1) + (F 2 + (F 3 + F 4))) + ((F 5 + (F 6 + F 7)) + (F 8 + (F 9 + F 10)))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F 0 + (F 1 + (F 2 + (F 3 + (F 4 + (F 5 + (F 6 + (F 7 + (F 8 + (F 9 + (F 10 + 0))))))))))) = (((F 0 + F 1) + (F 2 + (F 3 + F 4))) + ((F 5 + (F 6 + F 7)) + (F 8 + (F 9 + F 10))))
  simp only [add_zero, add_assoc]

end MUB6.Certificate.GramAssembly

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

open scoped BigOperators

theorem row_eval_0 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node9 x =
      ∑ j : Fin 11, (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x := by
  rw [node9_eval]
  exact (sum_expand_11 (fun j => (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x)).symm

theorem row_eval_1 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node19 x =
      ∑ j : Fin 11, (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x := by
  rw [node19_eval]
  exact (sum_expand_11 (fun j => (weights 1 j : ℝ) * Integer.Sparse.eval (entries 1 j) x)).symm

theorem row_eval_2 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node29 x =
      ∑ j : Fin 11, (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x := by
  rw [node29_eval]
  exact (sum_expand_11 (fun j => (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x)).symm

theorem row_eval_3 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node39 x =
      ∑ j : Fin 11, (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x := by
  rw [node39_eval]
  exact (sum_expand_11 (fun j => (weights 3 j : ℝ) * Integer.Sparse.eval (entries 3 j) x)).symm

theorem row_eval_4 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node49 x =
      ∑ j : Fin 11, (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x := by
  rw [node49_eval]
  exact (sum_expand_11 (fun j => (weights 4 j : ℝ) * Integer.Sparse.eval (entries 4 j) x)).symm

theorem row_eval_5 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node59 x =
      ∑ j : Fin 11, (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x := by
  rw [node59_eval]
  exact (sum_expand_11 (fun j => (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x)).symm

theorem row_eval_6 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node69 x =
      ∑ j : Fin 11, (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x := by
  rw [node69_eval]
  exact (sum_expand_11 (fun j => (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x)).symm

theorem row_eval_7 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node79 x =
      ∑ j : Fin 11, (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x := by
  rw [node79_eval]
  exact (sum_expand_11 (fun j => (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x)).symm

theorem row_eval_8 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node89 x =
      ∑ j : Fin 11, (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x := by
  rw [node89_eval]
  exact (sum_expand_11 (fun j => (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x)).symm

theorem row_eval_9 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node99 x =
      ∑ j : Fin 11, (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x := by
  rw [node99_eval]
  exact (sum_expand_11 (fun j => (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x)).symm

theorem row_eval_10 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node109 x =
      ∑ j : Fin 11, (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x := by
  rw [node109_eval]
  exact (sum_expand_11 (fun j => (weights 10 j : ℝ) * Integer.Sparse.eval (entries 10 j) x)).symm

theorem rows_eval (i : Fin 11) (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval (rows i) x =
      ∑ j : Fin 11, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
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

theorem polynomial_eval_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval polynomial x =
      ∑ i : Fin 11, ∑ j : Fin 11, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  calc
    _ = ∑ i : Fin 11, Integer.Sparse.eval (rows i) x := by
      rw [polynomial, node119_eval]
      exact (sum_expand_11 (fun i => Integer.Sparse.eval (rows i) x)).symm
    _ = _ := by simp_rw [rows_eval]

end MUB6.Certificate.GramAssembly.Block2

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block2.polynomial_eval_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block2.polynomial_eval_e_oai
