-- Prove2me | solution 1 for GlobalTheory.apply_add_intCast_vec_of_unit_periods
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:26:13.473194+00:00
-- url     : https://prove2.me/submissions/67b5a566-8ea0-4576-92d4-47f1ca2323fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ShiftSingleInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Theorems.Thm_GlobalTheory_IntegerShiftSingle_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι R E : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] {F : (ι → R) → E} (hF : ∀ (i : ι) x, F (x + Pi.single i 1) = F x)
    (n : ι → ℤ) (x : ι → R) : F (x + fun i => (n i : R)) = F x := by
  first
  | exact @_root_.GlobalTheory.IntegerShiftSingle.main
  | exact _root_.GlobalTheory.IntegerShiftSingle.main
  | (apply _root_.GlobalTheory.IntegerShiftSingle.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerShiftSingle.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerShiftSingle.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerShiftSingle.main ..)
end GlobalTheory
