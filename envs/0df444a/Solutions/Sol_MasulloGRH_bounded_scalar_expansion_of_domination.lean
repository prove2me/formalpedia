-- Prove2me | solution 1 for MasulloGRH.bounded_scalar_expansion_of_domination
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:20:49.897251+00:00
-- url     : https://prove2.me/submissions/dae934c6-3c89-4f34-a18b-d20a9a1e4ace

import Theorems.Thm_MasulloGRH_bounded_weak_nuclear_repr_of_domination
import Theorems.Thm_MasulloGRH_scalar_expansion_of_weak_expansion

set_option autoImplicit false

open MasulloGRH

theorem solution (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hN : IsNuclear G)
    (hdom : ∀ D : Set G, Bornology.IsVonNBounded ℂ D →
      ∃ (y : ℕ → G) (c : ℕ → ℝ), Bornology.IsVonNBounded ℂ (Set.range y) ∧ (∀ n, 0 ≤ c n) ∧
        Summable c ∧ ∀ (f : StrongDual ℂ G), ∀ x ∈ D, ‖f x‖ ≤ ∑' n, c n * ‖f (y n)‖)
    (B : Set G) (hBb : Bornology.IsVonNBounded ℂ B) :
    ∃ (y : ℕ → G) (c : ℕ → ℝ) (a : ℕ → (Submodule.span ℂ B) →ₗ[ℂ] ℂ),
      Filter.Tendsto y Filter.atTop (nhds (0 : G)) ∧
      (∀ n, 0 ≤ c n) ∧ Summable c ∧
      (∀ n (x : Submodule.span ℂ B), (x : G) ∈ B → ‖a n x‖ ≤ c n) ∧
      ∀ x : Submodule.span ℂ B, HasSum (fun n => a n x • y n) (x : G) := by
  obtain ⟨w, Y, c, hw, hc0, hc, hY, hrep⟩ :=
    bounded_weak_nuclear_repr_of_domination G hC hN hdom B hBb
  exact scalar_expansion_of_weak_expansion G hC hN.1 B w Y c hw hc0 hc hY hrep
