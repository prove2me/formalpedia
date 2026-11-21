-- Prove2me | solution 2 for MasulloGRH.pietsch_hilbertian_two_summing
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:33:09.240125+00:00
-- url     : https://prove2.me/submissions/6a199df2-9b88-4fd3-9da1-15ac77651bdf

import Theorems.Thm_MasulloGRH_pietsch_domination_state
import Theorems.Thm_MasulloGRH_hilbertian_of_pietsch_state

set_option autoImplicit false

open MasulloGRH

universe u

theorem solution (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (p q : Seminorm ℂ E) (hp : Continuous p) (hq : Continuous q)
    (hAS : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖ ≤ c) →
      ∑ i, p (x i) ≤ c) :
    ∃ h : Seminorm ℂ E, Continuous h ∧ (∀ x, p x ≤ h x) ∧ (∀ x, h x ≤ q x) ∧
      (∀ x y, h (x + y) ^ 2 + h (x - y) ^ 2 = 2 * h x ^ 2 + 2 * h y ^ 2) ∧
      ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
        (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
        ∑ i, h (x i) ^ 2 ≤ c := by
  obtain ⟨Λ, hadd, hsmul, hmono, hone, hdom⟩ := pietsch_domination_state E p q hAS
  exact hilbertian_of_pietsch_state E hE p q hp hq Λ hadd hsmul hmono hone hdom
