-- Prove2me | solution 1 for GlobalTheory.T.exists_valuationSubring_algClosed_not_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:57:44.435529+00:00
-- url     : https://prove2.me/submissions/6b0035d4-868e-4eae-b9e6-e43f5cc44cd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsValuationSubringAlgClosedNotIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsValuationSubringAlgClosedNotIsUnitStatement
import Theorems.Thm_GlobalTheory_exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Type) [CommRing S] (u : S), ¬ IsUnit u → ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L) (f : S →+* ↥V), ¬ IsUnit (f u) ∧ ∀ s ∈ nonZeroDivisors S, f s ≠ 0 := by
  first | exact @GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero | exact GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero | (intros; apply GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero <;> assumption)
end _root_.GlobalTheory.T
