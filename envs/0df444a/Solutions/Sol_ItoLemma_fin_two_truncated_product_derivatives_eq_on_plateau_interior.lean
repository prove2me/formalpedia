-- Prove2me | solution 1 for ItoLemma.fin_two_truncated_product_derivatives_eq_on_plateau_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:43:50.996934+00:00
-- url     : https://prove2.me/submissions/b6579454-736a-4a80-ac1c-df3cbe1a3ce4

import Mathlib.Analysis.Calculus.FDeriv.Congr

open scoped Topology

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Inside the plateau, the cutoff product agrees with the original product
on a neighbourhood; therefore its first two Fréchet derivatives agree there. -/
theorem solution
    (R : ℝ) (ψ : (Fin 2 → ℝ) → ℝ)
    (hp : ∀ y : Fin 2 → ℝ, ‖y‖ ≤ R → ψ y = 1)
    (z : Fin 2 → ℝ) (hz : ‖z‖ < R) :
    fderiv ℝ (fun y : Fin 2 → ℝ => ψ y * (y 0 * y 1)) z =
      fderiv ℝ (fun y : Fin 2 → ℝ => y 0 * y 1) z ∧
    fderiv ℝ (fderiv ℝ (fun y : Fin 2 → ℝ => ψ y * (y 0 * y 1))) z =
      fderiv ℝ (fderiv ℝ (fun y : Fin 2 → ℝ => y 0 * y 1)) z := by
  have hneigh : {y : Fin 2 → ℝ | ‖y‖ < R} ∈ 𝓝 z :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hz
  have hEq :
      (fun y : Fin 2 → ℝ => ψ y * (y 0 * y 1)) =ᶠ[𝓝 z]
        (fun y : Fin 2 → ℝ => y 0 * y 1) := by
    filter_upwards [hneigh] with y hy
    rw [hp y (le_of_lt hy), one_mul]
  exact ⟨hEq.fderiv_eq, hEq.fderiv.fderiv_eq⟩
