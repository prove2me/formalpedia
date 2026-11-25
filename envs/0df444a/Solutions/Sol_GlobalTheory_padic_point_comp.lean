-- Prove2me | solution 1 for GlobalTheory.padic_point_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:32:57.86284+00:00
-- url     : https://prove2.me/submissions/330a05b3-49f9-4495-aa0f-638376fa76e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Theorems.Thm_GlobalTheory_mapIntegralClosure_padicInt_injective
import Theorems.Thm_GlobalTheory_comap_maximalIdeal_mapIntegralClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing TensorProduct
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory
theorem _root_.solution {A : Type*} [CommRing A] {K L : Type*}
    [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L]
    [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L] (σ : K →ₐ[ℚ_[p]] L)
    (y : A →+* integralClosure ℤ_[p] K) :
    (maximalIdeal (integralClosure ℤ_[p] L)).comap
        ((σ.restrictScalars ℤ_[p]).mapIntegralClosure.toRingHom.comp y) =
      (maximalIdeal (integralClosure ℤ_[p] K)).comap y ∧
    RingHom.ker ((σ.restrictScalars ℤ_[p]).mapIntegralClosure.toRingHom.comp y) =
      RingHom.ker y := by
  refine ⟨by rw [← Ideal.comap_comap, ← comap_maximalIdeal_mapIntegralClosure σ]; rfl, ?_⟩
  exact RingHom.ker_comp_of_injective y (mapIntegralClosure_padicInt_injective σ)
end GlobalTheory
