-- Prove2me | solution 1 for GroundTheory.LocalField.exists_lowerIndex_mul_eq_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:37:34.593896+00:00
-- url     : https://prove2.me/submissions/4275869d-9ddc-4a35-b8ea-cb0fce0515f8

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RamificationLowerIndex
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_GeneralBFactAlt
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_trans
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_mul_of_lt
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_restrictScalars
import Theorems.Thm_GroundTheory_LocalField_min_le_lowerIndex_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.lowerIndex_restrictScalars



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
omit [IsGalois K L]
namespace GroundTheory.LocalField
theorem _root_.solution (σ : L ≃ₐ[K] L) :
    ∃ τ₀ : L ≃ₐ[M] L,
      (∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) ≤
        lowerIndex K L (σ * τ₀.restrictScalars K)) ∧
      ∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ₀.restrictScalars K * τ.restrictScalars K) =
        min (lowerIndex M L τ) (lowerIndex K L (σ * τ₀.restrictScalars K)) := by
  obtain ⟨τ₀, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun τ : L ≃ₐ[M] L ↦ lowerIndex K L (σ * τ.restrictScalars K)) Finset.univ_nonempty
  refine ⟨τ₀, fun τ ↦ hmax τ (Finset.mem_univ _), fun τ ↦ ?_⟩
  set σ₀ := σ * τ₀.restrictScalars K with hσ₀
  rw [← lowerIndex_restrictScalars (K := K)]
  rcases lt_or_ge (lowerIndex K L (τ.restrictScalars K)) (lowerIndex K L σ₀) with h | h
  · rw [lowerIndex_mul_of_lt h, min_eq_left h.le]
  · rw [min_eq_right h]
    refine le_antisymm ?_ ((min_eq_left h).symm.le.trans (min_le_lowerIndex_mul _ _))
    have hm : (τ₀ * τ).restrictScalars K = τ₀.restrictScalars K * τ.restrictScalars K :=
      AlgEquiv.ext fun _ ↦ rfl
    have := hmax (τ₀ * τ) (Finset.mem_univ _)
    rwa [hm, ← mul_assoc] at this
end GroundTheory.LocalField
