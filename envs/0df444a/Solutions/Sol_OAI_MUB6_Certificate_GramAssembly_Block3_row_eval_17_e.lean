-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_17_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:29:05.079697+00:00
-- url     : https://prove2.me/submissions/75bed9e1-95b6-44fe-8cab-2e20c5db2ad6

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E176
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node442_check : node442 =
    Integer.Sparse.merge (Integer.Sparse.scale (1697129) entry_17_1) (Integer.Sparse.scale (2358685) entry_17_2) := by decide +kernel

theorem node442_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node442 x = (((1697129 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_1 x + ((2358685 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_2 x) := by
  rw [node442_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node443_check : node443 =
    Integer.Sparse.merge (Integer.Sparse.scale (6566227) entry_17_0) node442 := by decide +kernel

theorem node443_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node443 x = (((6566227 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_0 x + (((1697129 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_1 x + ((2358685 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_2 x)) := by
  rw [node443_check, Integer.Sparse.eval_merge]
  rw [node442_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node444_check : node444 =
    Integer.Sparse.merge (Integer.Sparse.scale (6202189) entry_17_4) (Integer.Sparse.scale (728173) entry_17_5) := by decide +kernel

theorem node444_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node444 x = (((6202189 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_4 x + ((728173 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_5 x) := by
  rw [node444_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node445_check : node445 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3225514) entry_17_3) node444 := by decide +kernel

theorem node445_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node445 x = (((-3225514 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_3 x + (((6202189 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_4 x + ((728173 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_5 x)) := by
  rw [node445_check, Integer.Sparse.eval_merge]
  rw [node444_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node446_check : node446 =
    Integer.Sparse.merge node443 node445 := by decide +kernel

theorem node446_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node446 x = ((((6566227 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_0 x + (((1697129 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_1 x + ((2358685 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_2 x)) + (((-3225514 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_3 x + (((6202189 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_4 x + ((728173 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_5 x))) := by
  rw [node446_check, Integer.Sparse.eval_merge]
  rw [node443_eval, node445_eval]

theorem node447_check : node447 =
    Integer.Sparse.merge (Integer.Sparse.scale (-5499711) entry_17_7) (Integer.Sparse.scale (6141615) entry_17_8) := by decide +kernel

theorem node447_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node447 x = (((-5499711 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_7 x + ((6141615 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_8 x) := by
  rw [node447_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

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

theorem node448_check : node448 =
    Integer.Sparse.merge (Integer.Sparse.scale (1639448) entry_17_6) node447 := by decide +kernel

theorem node448_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node448 x = (((1639448 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_6 x + (((-5499711 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_7 x + ((6141615 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_8 x)) := by
  rw [node448_check, Integer.Sparse.eval_merge]
  rw [node447_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node449_check : node449 =
    Integer.Sparse.merge (Integer.Sparse.scale (12059339) entry_17_9) (Integer.Sparse.scale (-6804900) entry_17_10) := by decide +kernel

theorem node449_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node449 x = (((12059339 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_9 x + ((-6804900 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_10 x) := by
  rw [node449_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node450_check : node450 =
    Integer.Sparse.merge (Integer.Sparse.scale (3041223) entry_17_11) (Integer.Sparse.scale (4768294) entry_17_12) := by decide +kernel

theorem node450_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node450 x = (((3041223 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_11 x + ((4768294 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_12 x) := by
  rw [node450_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node451_check : node451 =
    Integer.Sparse.merge node449 node450 := by decide +kernel

theorem node451_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node451 x = ((((12059339 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_9 x + ((-6804900 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_10 x) + (((3041223 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_11 x + ((4768294 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_12 x)) := by
  rw [node451_check, Integer.Sparse.eval_merge]
  rw [node449_eval, node450_eval]

theorem node452_check : node452 =
    Integer.Sparse.merge node448 node451 := by decide +kernel

theorem node452_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node452 x = ((((1639448 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_6 x + (((-5499711 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_7 x + ((6141615 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_8 x)) + ((((12059339 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_9 x + ((-6804900 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_10 x) + (((3041223 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_11 x + ((4768294 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_12 x))) := by
  rw [node452_check, Integer.Sparse.eval_merge]
  rw [node448_eval, node451_eval]

theorem node453_check : node453 =
    Integer.Sparse.merge node446 node452 := by decide +kernel

theorem node453_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node453 x = (((((6566227 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_0 x + (((1697129 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_1 x + ((2358685 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_2 x)) + (((-3225514 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_3 x + (((6202189 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_4 x + ((728173 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_5 x))) + ((((1639448 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_6 x + (((-5499711 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_7 x + ((6141615 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_8 x)) + ((((12059339 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_9 x + ((-6804900 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_10 x) + (((3041223 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_11 x + ((4768294 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_12 x)))) := by
  rw [node453_check, Integer.Sparse.eval_merge]
  rw [node446_eval, node452_eval]

theorem node454_check : node454 =
    Integer.Sparse.merge (Integer.Sparse.scale (3868069) entry_17_14) (Integer.Sparse.scale (10794029) entry_17_15) := by decide +kernel

theorem node454_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node454 x = (((3868069 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_14 x + ((10794029 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_15 x) := by
  rw [node454_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node455_check : node455 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2063816) entry_17_13) node454 := by decide +kernel

theorem node455_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node455 x = (((-2063816 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_13 x + (((3868069 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_14 x + ((10794029 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_15 x)) := by
  rw [node455_check, Integer.Sparse.eval_merge]
  rw [node454_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node456_check : node456 =
    Integer.Sparse.merge (Integer.Sparse.scale (774544) entry_17_16) (Integer.Sparse.scale (17833685) entry_17_17) := by decide +kernel

theorem node456_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node456 x = (((774544 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_16 x + ((17833685 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_17 x) := by
  rw [node456_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node457_check : node457 =
    Integer.Sparse.merge (Integer.Sparse.scale (2066116) entry_17_18) (Integer.Sparse.scale (-13574800) entry_17_19) := by decide +kernel

theorem node457_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node457 x = (((2066116 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_18 x + ((-13574800 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_19 x) := by
  rw [node457_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node458_check : node458 =
    Integer.Sparse.merge node456 node457 := by decide +kernel

theorem node458_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node458 x = ((((774544 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_16 x + ((17833685 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_17 x) + (((2066116 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_18 x + ((-13574800 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_19 x)) := by
  rw [node458_check, Integer.Sparse.eval_merge]
  rw [node456_eval, node457_eval]

theorem node459_check : node459 =
    Integer.Sparse.merge node455 node458 := by decide +kernel

theorem node459_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node459 x = ((((-2063816 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_13 x + (((3868069 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_14 x + ((10794029 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_15 x)) + ((((774544 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_16 x + ((17833685 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_17 x) + (((2066116 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_18 x + ((-13574800 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_19 x))) := by
  rw [node459_check, Integer.Sparse.eval_merge]
  rw [node455_eval, node458_eval]

theorem node460_check : node460 =
    Integer.Sparse.merge (Integer.Sparse.scale (4428060) entry_17_21) (Integer.Sparse.scale (-8076457) entry_17_22) := by decide +kernel

theorem node460_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node460 x = (((4428060 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_21 x + ((-8076457 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_22 x) := by
  rw [node460_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node461_check : node461 =
    Integer.Sparse.merge (Integer.Sparse.scale (196572) entry_17_20) node460 := by decide +kernel

theorem node461_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node461 x = (((196572 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_20 x + (((4428060 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_21 x + ((-8076457 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_22 x)) := by
  rw [node461_check, Integer.Sparse.eval_merge]
  rw [node460_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node462_check : node462 =
    Integer.Sparse.merge (Integer.Sparse.scale (3932306) entry_17_23) (Integer.Sparse.scale (1121311) entry_17_24) := by decide +kernel

theorem node462_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node462 x = (((3932306 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_23 x + ((1121311 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_24 x) := by
  rw [node462_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node463_check : node463 =
    Integer.Sparse.merge (Integer.Sparse.scale (6669123) entry_17_25) (Integer.Sparse.scale (-1006711) entry_17_26) := by decide +kernel

theorem node463_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node463 x = (((6669123 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_25 x + ((-1006711 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_26 x) := by
  rw [node463_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node464_check : node464 =
    Integer.Sparse.merge node462 node463 := by decide +kernel

theorem node464_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node464 x = ((((3932306 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_23 x + ((1121311 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_24 x) + (((6669123 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_25 x + ((-1006711 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_26 x)) := by
  rw [node464_check, Integer.Sparse.eval_merge]
  rw [node462_eval, node463_eval]

theorem node465_check : node465 =
    Integer.Sparse.merge node461 node464 := by decide +kernel

theorem node465_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node465 x = ((((196572 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_20 x + (((4428060 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_21 x + ((-8076457 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_22 x)) + ((((3932306 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_23 x + ((1121311 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_24 x) + (((6669123 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_25 x + ((-1006711 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_26 x))) := by
  rw [node465_check, Integer.Sparse.eval_merge]
  rw [node461_eval, node464_eval]

theorem node466_check : node466 =
    Integer.Sparse.merge node459 node465 := by decide +kernel

theorem node466_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node466 x = (((((-2063816 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_13 x + (((3868069 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_14 x + ((10794029 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_15 x)) + ((((774544 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_16 x + ((17833685 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_17 x) + (((2066116 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_18 x + ((-13574800 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_19 x))) + ((((196572 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_20 x + (((4428060 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_21 x + ((-8076457 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_22 x)) + ((((3932306 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_23 x + ((1121311 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_24 x) + (((6669123 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_25 x + ((-1006711 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_26 x)))) := by
  rw [node466_check, Integer.Sparse.eval_merge]
  rw [node459_eval, node465_eval]

theorem node467_check : node467 =
    Integer.Sparse.merge node453 node466 := by decide +kernel

theorem node467_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node467 x = ((((((6566227 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_0 x + (((1697129 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_1 x + ((2358685 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_2 x)) + (((-3225514 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_3 x + (((6202189 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_4 x + ((728173 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_5 x))) + ((((1639448 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_6 x + (((-5499711 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_7 x + ((6141615 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_8 x)) + ((((12059339 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_9 x + ((-6804900 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_10 x) + (((3041223 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_11 x + ((4768294 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_12 x)))) + (((((-2063816 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_13 x + (((3868069 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_14 x + ((10794029 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_15 x)) + ((((774544 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_16 x + ((17833685 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_17 x) + (((2066116 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_18 x + ((-13574800 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_19 x))) + ((((196572 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_20 x + (((4428060 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_21 x + ((-8076457 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_22 x)) + ((((3932306 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_23 x + ((1121311 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_24 x) + (((6669123 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_25 x + ((-1006711 : ℤ) : ℝ) * Integer.Sparse.eval entry_17_26 x))))) := by
  rw [node467_check, Integer.Sparse.eval_merge]
  rw [node453_eval, node466_eval]

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

theorem row_eval_17_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node467 x =
      ∑ j : Fin 27, (weights 17 j : ℝ) * Integer.Sparse.eval (entries 17 j) x := by
  rw [node467_eval]
  exact (sum_expand_27 (fun j => (weights 17 j : ℝ) * Integer.Sparse.eval (entries 17 j) x)).symm

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_17_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_17_e_oai
