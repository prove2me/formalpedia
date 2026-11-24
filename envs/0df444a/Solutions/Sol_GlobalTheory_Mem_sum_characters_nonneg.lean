-- Prove2me | solution 1 for GlobalTheory.Mem.sum_characters_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:00:44.540171+00:00
-- url     : https://prove2.me/submissions/ba1768fe-4e5a-464e-818f-8c27c0affd56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem
namespace GlobalTheory.Mem
theorem _root_.solution {G : Type} [CommGroup G] [Fintype (G →* ℂˣ)] (g : G) :
    0 ≤ ∑ χ : G →* ℂˣ, (χ g : ℂ) := by
  by_cases h : ∀ χ : G →* ℂˣ, χ g = 1
  · exact Finset.sum_nonneg fun χ _ => by simp [h χ]
  · push_neg at h
    obtain ⟨ψ, hψ⟩ := h
    have h1 : ∑ χ : G →* ℂˣ, (χ g : ℂ) = (ψ g : ℂ) * ∑ χ : G →* ℂˣ, (χ g : ℂ) := by
      rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft ψ)]
      simp
    have h2 : (1 - (ψ g : ℂ)) * ∑ χ : G →* ℂˣ, (χ g : ℂ) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (Units.ext (sub_eq_zero.1 h3).symm) hψ
    · exact h3.ge
end GlobalTheory.Mem
