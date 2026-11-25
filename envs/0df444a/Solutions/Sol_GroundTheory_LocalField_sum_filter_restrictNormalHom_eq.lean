-- Prove2me | solution 1 for GroundTheory.LocalField.sum_filter_restrictNormalHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:32.471052+00:00
-- url     : https://prove2.me/submissions/01b44349-a267-450c-950a-58d07db61f3d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
import Definitions.Def_GroundTheory_LocalFields_UpperNumbering
import Theorems.Thm_GroundTheory_LocalField_exists_eq_mul_restrictScalars_of_restrictNormalHom_eq
import Theorems.Thm_GroundTheory_LocalField_restrictNormalHom_restrictScalars


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
open ValuativeRel
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) [Normal K M]
open Classical
namespace GroundTheory.LocalField
theorem _root_.solution {β : Type*} [AddCommMonoid β] [Fintype (L ≃ₐ[K] L)]
    [Fintype (L ≃ₐ[M] L)] (F : (L ≃ₐ[K] L) → β) (σ : L ≃ₐ[K] L) :
    ∑ ρ ∈ Finset.univ.filter
        (fun ρ ↦ AlgEquiv.restrictNormalHom M ρ = AlgEquiv.restrictNormalHom M σ), F ρ =
      ∑ τ : L ≃ₐ[M] L, F (σ * τ.restrictScalars K) := by
  symm
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
