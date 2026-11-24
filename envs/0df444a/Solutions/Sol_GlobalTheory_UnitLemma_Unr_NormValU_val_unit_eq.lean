-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.NormValU.val_unit_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:01:41.297885+00:00
-- url     : https://prove2.me/submissions/5d010ae7-177e-4c31-bb7a-64e56d52bce3

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
theorem _root_.solution (a : O) (ha : IsUnit a) : val O (algebraMap O E a) = 0 := by
  unfold val
  have : (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E a) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact fun h => (IsLocalRing.mem_maximalIdeal a).1 h ha
  rw [this]; simp
end GlobalTheory.UnitLemma.Unr.NormValU
