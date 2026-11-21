-- Prove2me | solution 1 for MasulloGRH.bounded_disk_scalar_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:16:37.505123+00:00
-- url     : https://prove2.me/submissions/481dd969-359d-4d30-b1d7-60d2f64b6acc

import Theorems.Thm_MasulloGRH_bounded_scalar_expansion_of_domination
import Theorems.Thm_MasulloGRH_nuclearFrechet_bounded_nuclear_domination
import Theorems.Thm_MasulloGRH_completeNuclearDF_bounded_nuclear_domination

set_option autoImplicit false

open MasulloGRH

theorem solution (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hN : IsNuclear G)
    (hclass : IsFrechet G ∨
      ((∃ B : ℕ → Set G, (∀ n, Bornology.IsVonNBounded ℂ (B n)) ∧
      ∀ S : Set G, Bornology.IsVonNBounded ℂ S → ∃ n, S ⊆ B n) ∧
       (∀ U : ℕ → Set G, (∀ n, U n ∈ nhds (0 : G) ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧ Convex ℝ (U n)) →
      (∀ S : Set G, Bornology.IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) →
      (⋂ n, U n) ∈ nhds (0 : G))))
    (B : Set G) (hBb : Bornology.IsVonNBounded ℂ B) :
    ∃ (y : ℕ → G) (c : ℕ → ℝ) (a : ℕ → (Submodule.span ℂ B) →ₗ[ℂ] ℂ),
      Filter.Tendsto y Filter.atTop (nhds (0 : G)) ∧
      (∀ n, 0 ≤ c n) ∧ Summable c ∧
      (∀ n (x : Submodule.span ℂ B), (x : G) ∈ B → ‖a n x‖ ≤ c n) ∧
      ∀ x : Submodule.span ℂ B, HasSum (fun n => a n x • y n) (x : G) := by
  apply bounded_scalar_expansion_of_domination G hC hN _ B hBb
  intro D hD
  rcases hclass with hF | ⟨hB, hDF⟩
  · exact nuclearFrechet_bounded_nuclear_domination G hF hN D hD
  · exact completeNuclearDF_bounded_nuclear_domination G hC hN hB hDF D hD
