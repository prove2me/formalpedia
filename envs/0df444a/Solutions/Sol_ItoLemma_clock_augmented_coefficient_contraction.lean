-- Prove2me | solution 1 for ItoLemma.clock_augmented_coefficient_contraction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:34:27.794246+00:00
-- url     : https://prove2.me/submissions/f1e37cae-1ed9-4135-a216-d1cc366fb2b9

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

/-- The clock has unit drift and zero Brownian diffusion; the spatial
coordinate has drift μ and diffusion σ. Contracting the vector Itô
coefficients therefore retains only the spatial Hessian term. -/

theorem solution
    (gradient : Fin 2 → ℝ) (hessian : Fin 2 → Fin 2 → ℝ) (μ σ : ℝ) :
    (∑ i : Fin 2, gradient i * (if i = 0 then (1 : ℝ) else μ)) =
      gradient 0 + gradient 1 * μ ∧
    (∑ i : Fin 2, gradient i * (if i = 0 then (0 : ℝ) else σ)) =
      gradient 1 * σ ∧
    (∑ i : Fin 2, ∑ j : Fin 2,
      hessian i j * (if i = 0 then (0 : ℝ) else σ) *
        (if j = 0 then (0 : ℝ) else σ)) =
      hessian 1 1 * σ ^ 2 := by
  simp [Fin.sum_univ_two, pow_two, mul_assoc]
