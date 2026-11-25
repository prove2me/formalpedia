-- Prove2me | solution 1 for GroundTheory.LocalField.exists_smul_div_eq_of_tateNorm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:59:53.948051+00:00
-- url     : https://prove2.me/submissions/e044976b-48ba-49a5-bb98-f5606d32a6b4

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Theorems.Thm_GroundTheory_LocalField_partialNorm_add
import Theorems.Thm_GroundTheory_LocalField_partialNorm_one
import Theorems.Thm_GroundTheory_LocalField_partialNorm_eq_of_pow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution {σ : L ≃ₐ[K] L}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x : Lˣ} (hx : tateNorm (L ≃ₐ[K] L) Lˣ x = 1) :
    ∃ y : Lˣ, σ • y / y = x := by
  have hk : ∀ g : L ≃ₐ[K] L, ∃ k : ℕ, σ ^ k = g := fun g => by
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (x := σ) (y := g)).mpr (hσ g)
    exact ⟨k, hk⟩
  choose k hk using hk
  let f : (L ≃ₐ[K] L) → Lˣ := fun g => partialNorm σ x (k g)
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    have e : σ ^ k (g * h) = σ ^ (k g + k h) := by rw [hk, pow_add, hk, hk]
    change partialNorm σ x (k (g * h)) = g • partialNorm σ x (k h) * partialNorm σ x (k g)
    rw [partialNorm_eq_of_pow_eq hσ hx e, partialNorm_add, hk, mul_comm]
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  refine ⟨β, ?_⟩
  rw [hβ σ]
  change partialNorm σ x (k σ) = x
  rw [partialNorm_eq_of_pow_eq hσ hx (show σ ^ k σ = σ ^ 1 by rw [hk, pow_one]), partialNorm_one]
end GroundTheory.LocalField
