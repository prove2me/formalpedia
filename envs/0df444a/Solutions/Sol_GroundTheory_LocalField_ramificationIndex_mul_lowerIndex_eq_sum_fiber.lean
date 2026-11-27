-- Prove2me | solution 1 for GroundTheory.LocalField.ramificationIndex_mul_lowerIndex_eq_sum_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:49:36.752792+00:00
-- url     : https://prove2.me/submissions/722225f9-318e-4349-b5d4-9716d2e73f87

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RamificationLowerIndex
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_GeneralBFactAlt
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
import Theorems.Thm_GroundTheory_LocalField_restrictNormalHom_restrictScalars
import Theorems.Thm_GroundTheory_LocalField_exists_eq_mul_restrictScalars_of_restrictNormalHom_eq
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_mul_lowerIndex_restrictNormalHom

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
open Classical
namespace GroundTheory.LocalField
theorem _root_.solution [Normal K M] (s : M ≃ₐ[K] M) :
    (ramificationIndex M L : ℕ∞) * lowerIndex K M s =
      ∑ σ ∈ Finset.univ.filter (fun σ : L ≃ₐ[K] L ↦ AlgEquiv.restrictNormalHom M σ = s),
        lowerIndex K L σ := by
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) L s
  rw [ramificationIndex_mul_lowerIndex_restrictNormalHom]
  refine Finset.sum_bij (fun τ _ ↦ σ * τ.restrictScalars K) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro τ _
    rw [Finset.mem_filter, map_mul, restrictNormalHom_restrictScalars, mul_one]
    exact ⟨Finset.mem_univ _, rfl⟩
  · intro a _ b _ hab
    exact AlgEquiv.restrictScalars_injective K (mul_left_cancel hab)
  · intro ρ hρ
    obtain ⟨τ, hτ⟩ := exists_eq_mul_restrictScalars_of_restrictNormalHom_eq M
      (Finset.mem_filter.mp hρ).2
    exact ⟨τ, Finset.mem_univ _, hτ⟩
end GroundTheory.LocalField
