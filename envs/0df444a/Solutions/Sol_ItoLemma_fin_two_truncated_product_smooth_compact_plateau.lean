-- Prove2me | solution 1 for ItoLemma.fin_two_truncated_product_smooth_compact_plateau
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:12:41.685447+00:00
-- url     : https://prove2.me/submissions/dbc744f6-8ad9-4945-98e7-af4c7897b628

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A smooth cutoff of the two-coordinate product is smooth, compactly supported,
and agrees with the product on the plateau of the cutoff. -/
theorem solution
    (R : ℝ) (ψ : (Fin 2 → ℝ) → ℝ)
    (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (hs : HasCompactSupport ψ)
    (hp : ∀ z : Fin 2 → ℝ, ‖z‖ ≤ R → ψ z = 1) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : Fin 2 → ℝ => ψ z * (z 0 * z 1)) ∧
    HasCompactSupport (fun z : Fin 2 → ℝ => ψ z * (z 0 * z 1)) ∧
    (∀ z : Fin 2 → ℝ, ‖z‖ ≤ R → ψ z * (z 0 * z 1) = z 0 * z 1) := by
  have h₀ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : Fin 2 → ℝ => z 0) :=
    contDiff_apply ℝ ℝ (0 : Fin 2)
  have h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : Fin 2 → ℝ => z 1) :=
    contDiff_apply ℝ ℝ (1 : Fin 2)
  refine ⟨hψ.mul (h₀.mul h₁), hs.mul_right, ?_⟩
  intro z hz
  rw [hp z hz, one_mul]
