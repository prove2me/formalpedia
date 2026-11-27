-- Prove2me | solution 1 for GroundTheory.LocalField.exists_ramificationIndex_mul_lowerIndex_eq_sum_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:47:31.458352+00:00
-- url     : https://prove2.me/submissions/1208e126-3015-4f91-9356-65f4c313f80f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RamificationLowerIndex
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_GeneralBFactAlt
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
import Theorems.Thm_GroundTheory_LocalField_restrictNormalHom_restrictScalars
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_mul_lowerIndex_restrictNormalHom
import Theorems.Thm_GroundTheory_LocalField_exists_lowerIndex_mul_eq_min

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable (M : IntermediateField K L)
variable [IsGalois K L]
namespace GroundTheory.LocalField
theorem _root_.solution [Normal K M] (σ : L ≃ₐ[K] L) :
    ∃ σ₀ : L ≃ₐ[K] L, AlgEquiv.restrictNormalHom M σ₀ = AlgEquiv.restrictNormalHom M σ ∧
      (∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) ≤ lowerIndex K L σ₀) ∧
      (ramificationIndex M L : ℕ∞) * lowerIndex K M (AlgEquiv.restrictNormalHom M σ) =
        ∑ τ : L ≃ₐ[M] L, min (lowerIndex M L τ) (lowerIndex K L σ₀) := by
  obtain ⟨τ₀, hmax, hmin⟩ := exists_lowerIndex_mul_eq_min M σ
  have hres : AlgEquiv.restrictNormalHom M (σ * τ₀.restrictScalars K) =
      AlgEquiv.restrictNormalHom M σ := by
    rw [map_mul, restrictNormalHom_restrictScalars, mul_one]
  refine ⟨σ * τ₀.restrictScalars K, hres, hmax, ?_⟩
  rw [← hres, ramificationIndex_mul_lowerIndex_restrictNormalHom]
  exact Finset.sum_congr rfl fun τ _ ↦ hmin τ
end GroundTheory.LocalField
