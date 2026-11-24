-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.NormValU.lift_of_val_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:01:53.253995+00:00
-- url     : https://prove2.me/submissions/79b370d8-3fb8-4af4-9d31-d1d1030e947e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrFractionFieldAddValNormUnramifiedLocalExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.NormValU
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E]
namespace GlobalTheory.UnitLemma.Unr.NormValU
theorem _root_.solution {x : E} (hx : x ≠ 0) (h : val O x = 0) : ∃ a : O, algebraMap O E a = x := by
  have hx' : (IsDiscreteValuationRing.maximalIdeal O).valuation E x ≠ 0 := by simpa using hx
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation E x = 1 := by
    unfold val at h
    rw [← WithZero.exp_log hx']
    have : WithZero.log ((IsDiscreteValuationRing.maximalIdeal O).valuation E x) = 0 := by omega
    rw [this, WithZero.exp_zero]
  exact IsDiscreteValuationRing.exists_lift_of_le_one h1.le
end GlobalTheory.UnitLemma.Unr.NormValU
