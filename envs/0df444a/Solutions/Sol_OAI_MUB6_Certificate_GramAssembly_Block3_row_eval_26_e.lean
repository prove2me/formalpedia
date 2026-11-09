-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_26_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:32:38.448419+00:00
-- url     : https://prove2.me/submissions/550d3dfa-22ad-40cd-ba3c-71af3edce825

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E005
import Definitions.Def_OAIQ106E006
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node676_check : node676 =
    Integer.Sparse.merge (Integer.Sparse.scale (206227) entry_26_1) (Integer.Sparse.scale (-1320981) entry_26_2) := by decide +kernel

theorem node676_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node676 x = (((206227 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_1 x + ((-1320981 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_2 x) := by
  rw [node676_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node677_check : node677 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3848880) entry_26_0) node676 := by decide +kernel

theorem node677_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node677 x = (((-3848880 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_0 x + (((206227 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_1 x + ((-1320981 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_2 x)) := by
  rw [node677_check, Integer.Sparse.eval_merge]
  rw [node676_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node678_check : node678 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1483981) entry_26_4) (Integer.Sparse.scale (-393268) entry_26_5) := by decide +kernel

theorem node678_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node678 x = (((-1483981 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_4 x + ((-393268 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_5 x) := by
  rw [node678_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node679_check : node679 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2602804) entry_26_3) node678 := by decide +kernel

theorem node679_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node679 x = (((-2602804 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_3 x + (((-1483981 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_4 x + ((-393268 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_5 x)) := by
  rw [node679_check, Integer.Sparse.eval_merge]
  rw [node678_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node680_check : node680 =
    Integer.Sparse.merge node677 node679 := by decide +kernel

theorem node680_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node680 x = ((((-3848880 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_0 x + (((206227 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_1 x + ((-1320981 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_2 x)) + (((-2602804 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_3 x + (((-1483981 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_4 x + ((-393268 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_5 x))) := by
  rw [node680_check, Integer.Sparse.eval_merge]
  rw [node677_eval, node679_eval]

theorem node681_check : node681 =
    Integer.Sparse.merge (Integer.Sparse.scale (2854925) entry_26_7) (Integer.Sparse.scale (-3097019) entry_26_8) := by decide +kernel

theorem node681_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node681 x = (((2854925 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_7 x + ((-3097019 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_8 x) := by
  rw [node681_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node682_check : node682 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1032694) entry_26_6) node681 := by decide +kernel

theorem node682_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node682 x = (((-1032694 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_6 x + (((2854925 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_7 x + ((-3097019 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_8 x)) := by
  rw [node682_check, Integer.Sparse.eval_merge]
  rw [node681_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node683_check : node683 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2054950) entry_26_9) (Integer.Sparse.scale (-1745575) entry_26_10) := by decide +kernel

theorem node683_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node683 x = (((-2054950 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_9 x + ((-1745575 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_10 x) := by
  rw [node683_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node684_check : node684 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1738479) entry_26_11) (Integer.Sparse.scale (-1956856) entry_26_12) := by decide +kernel

theorem node684_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node684 x = (((-1738479 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_11 x + ((-1956856 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_12 x) := by
  rw [node684_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node685_check : node685 =
    Integer.Sparse.merge node683 node684 := by decide +kernel

theorem node685_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node685 x = ((((-2054950 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_9 x + ((-1745575 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_10 x) + (((-1738479 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_11 x + ((-1956856 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_12 x)) := by
  rw [node685_check, Integer.Sparse.eval_merge]
  rw [node683_eval, node684_eval]

theorem node686_check : node686 =
    Integer.Sparse.merge node682 node685 := by decide +kernel

theorem node686_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node686 x = ((((-1032694 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_6 x + (((2854925 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_7 x + ((-3097019 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_8 x)) + ((((-2054950 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_9 x + ((-1745575 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_10 x) + (((-1738479 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_11 x + ((-1956856 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_12 x))) := by
  rw [node686_check, Integer.Sparse.eval_merge]
  rw [node682_eval, node685_eval]

theorem node687_check : node687 =
    Integer.Sparse.merge node680 node686 := by decide +kernel

theorem node687_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node687 x = (((((-3848880 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_0 x + (((206227 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_1 x + ((-1320981 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_2 x)) + (((-2602804 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_3 x + (((-1483981 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_4 x + ((-393268 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_5 x))) + ((((-1032694 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_6 x + (((2854925 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_7 x + ((-3097019 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_8 x)) + ((((-2054950 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_9 x + ((-1745575 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_10 x) + (((-1738479 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_11 x + ((-1956856 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_12 x)))) := by
  rw [node687_check, Integer.Sparse.eval_merge]
  rw [node680_eval, node686_eval]

theorem node688_check : node688 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1763362) entry_26_14) (Integer.Sparse.scale (-4211536) entry_26_15) := by decide +kernel

theorem node688_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node688 x = (((-1763362 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_14 x + ((-4211536 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_15 x) := by
  rw [node688_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node689_check : node689 =
    Integer.Sparse.merge (Integer.Sparse.scale (242711) entry_26_13) node688 := by decide +kernel

theorem node689_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node689 x = (((242711 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_13 x + (((-1763362 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_14 x + ((-4211536 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_15 x)) := by
  rw [node689_check, Integer.Sparse.eval_merge]
  rw [node688_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node690_check : node690 =
    Integer.Sparse.merge (Integer.Sparse.scale (344604) entry_26_16) (Integer.Sparse.scale (-1006711) entry_26_17) := by decide +kernel

theorem node690_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node690 x = (((344604 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_16 x + ((-1006711 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_17 x) := by
  rw [node690_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node691_check : node691 =
    Integer.Sparse.merge (Integer.Sparse.scale (3152538) entry_26_18) (Integer.Sparse.scale (618762) entry_26_19) := by decide +kernel

theorem node691_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node691 x = (((3152538 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_18 x + ((618762 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_19 x) := by
  rw [node691_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node692_check : node692 =
    Integer.Sparse.merge node690 node691 := by decide +kernel

theorem node692_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node692 x = ((((344604 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_16 x + ((-1006711 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_17 x) + (((3152538 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_18 x + ((618762 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_19 x)) := by
  rw [node692_check, Integer.Sparse.eval_merge]
  rw [node690_eval, node691_eval]

theorem node693_check : node693 =
    Integer.Sparse.merge node689 node692 := by decide +kernel

theorem node693_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node693 x = ((((242711 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_13 x + (((-1763362 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_14 x + ((-4211536 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_15 x)) + ((((344604 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_16 x + ((-1006711 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_17 x) + (((3152538 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_18 x + ((618762 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_19 x))) := by
  rw [node693_check, Integer.Sparse.eval_merge]
  rw [node689_eval, node692_eval]

theorem node694_check : node694 =
    Integer.Sparse.merge (Integer.Sparse.scale (-8338454) entry_26_21) (Integer.Sparse.scale (-5290054) entry_26_22) := by decide +kernel

theorem node694_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node694 x = (((-8338454 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_21 x + ((-5290054 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_22 x) := by
  rw [node694_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node695_check : node695 =
    Integer.Sparse.merge (Integer.Sparse.scale (-428236) entry_26_20) node694 := by decide +kernel

theorem node695_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node695 x = (((-428236 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_20 x + (((-8338454 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_21 x + ((-5290054 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_22 x)) := by
  rw [node695_check, Integer.Sparse.eval_merge]
  rw [node694_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node696_check : node696 =
    Integer.Sparse.merge (Integer.Sparse.scale (1201176) entry_26_23) (Integer.Sparse.scale (-1287392) entry_26_24) := by decide +kernel

theorem node696_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node696 x = (((1201176 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_23 x + ((-1287392 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_24 x) := by
  rw [node696_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node697_check : node697 =
    Integer.Sparse.merge (Integer.Sparse.scale (4540900) entry_26_25) (Integer.Sparse.scale (5497571) entry_26_26) := by decide +kernel

theorem node697_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node697 x = (((4540900 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_25 x + ((5497571 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_26 x) := by
  rw [node697_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node698_check : node698 =
    Integer.Sparse.merge node696 node697 := by decide +kernel

theorem node698_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node698 x = ((((1201176 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_23 x + ((-1287392 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_24 x) + (((4540900 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_25 x + ((5497571 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_26 x)) := by
  rw [node698_check, Integer.Sparse.eval_merge]
  rw [node696_eval, node697_eval]

theorem node699_check : node699 =
    Integer.Sparse.merge node695 node698 := by decide +kernel

theorem node699_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node699 x = ((((-428236 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_20 x + (((-8338454 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_21 x + ((-5290054 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_22 x)) + ((((1201176 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_23 x + ((-1287392 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_24 x) + (((4540900 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_25 x + ((5497571 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_26 x))) := by
  rw [node699_check, Integer.Sparse.eval_merge]
  rw [node695_eval, node698_eval]

theorem node700_check : node700 =
    Integer.Sparse.merge node693 node699 := by decide +kernel

theorem node700_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node700 x = (((((242711 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_13 x + (((-1763362 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_14 x + ((-4211536 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_15 x)) + ((((344604 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_16 x + ((-1006711 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_17 x) + (((3152538 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_18 x + ((618762 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_19 x))) + ((((-428236 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_20 x + (((-8338454 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_21 x + ((-5290054 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_22 x)) + ((((1201176 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_23 x + ((-1287392 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_24 x) + (((4540900 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_25 x + ((5497571 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_26 x)))) := by
  rw [node700_check, Integer.Sparse.eval_merge]
  rw [node693_eval, node699_eval]

theorem node701_check : node701 =
    Integer.Sparse.merge node687 node700 := by decide +kernel

theorem node701_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node701 x = ((((((-3848880 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_0 x + (((206227 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_1 x + ((-1320981 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_2 x)) + (((-2602804 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_3 x + (((-1483981 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_4 x + ((-393268 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_5 x))) + ((((-1032694 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_6 x + (((2854925 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_7 x + ((-3097019 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_8 x)) + ((((-2054950 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_9 x + ((-1745575 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_10 x) + (((-1738479 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_11 x + ((-1956856 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_12 x)))) + (((((242711 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_13 x + (((-1763362 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_14 x + ((-4211536 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_15 x)) + ((((344604 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_16 x + ((-1006711 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_17 x) + (((3152538 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_18 x + ((618762 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_19 x))) + ((((-428236 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_20 x + (((-8338454 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_21 x + ((-5290054 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_22 x)) + ((((1201176 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_23 x + ((-1287392 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_24 x) + (((4540900 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_25 x + ((5497571 : ℤ) : ℝ) * Integer.Sparse.eval entry_26_26 x))))) := by
  rw [node701_check, Integer.Sparse.eval_merge]
  rw [node687_eval, node700_eval]

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

theorem row_eval_26_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node701 x =
      ∑ j : Fin 27, (weights 26 j : ℝ) * Integer.Sparse.eval (entries 26 j) x := by
  rw [node701_eval]
  exact (sum_expand_27 (fun j => (weights 26 j : ℝ) * Integer.Sparse.eval (entries 26 j) x)).symm

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_26_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_26_e_oai
