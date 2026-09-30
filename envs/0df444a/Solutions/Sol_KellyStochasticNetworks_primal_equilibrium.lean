-- Prove2me | solution 1 for KellyStochasticNetworks.primal_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:24:28.608842+00:00
-- url     : https://prove2.me/submissions/2b96c2b8-3948-45be-8063-8403561c7a94

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

theorem pr_equilibrium {J R : ℕ} (A : Fin J → Fin R → ℝ) (w κ : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hκ : ∀ r, 0 < κ r) (x : Fin R → ℝ) (hx : ∀ r, 0 < x r) :
    (∀ r, w r / x r - ∑ j, A j r * p j (linkFlow A x j) = 0)
      ↔ ∀ r, primalDrift A w κ p x r = 0 := by
  refine forall_congr' fun r => ?_
  unfold primalDrift
  have hx0 := (hx r).ne'
  have hκ0 := (hκ r).ne'
  have e : w r / x r - ∑ j, A j r * p j (linkFlow A x j) =
      (w r - x r * ∑ j, A j r * p j (linkFlow A x j)) / x r := by
    field_simp
  rw [e, div_eq_zero_iff, mul_eq_zero, or_iff_left hx0, or_iff_right hκ0]

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℝ) (w κ : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hκ : ∀ r, 0 < κ r) (x : Fin R → ℝ) (hx : ∀ r, 0 < x r) :
    (∀ r, w r / x r - ∑ j, A j r * p j (linkFlow A x j) = 0)
      ↔ ∀ r, primalDrift A w κ p x r = 0 := by
  exact pr_equilibrium A w κ p hκ x hx
