-- Prove2me | solution 1 for MonopolesInstantonsConfinement.static_first_integral
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T22:26:57.655484+00:00
-- url     : https://prove2.me/submissions/3d3df987-60e6-4a09-8eef-8f2bf8a660e2

import Mathlib
import Definitions.Def_MIC_kink_solitons_1d
import Theorems.Thm_MonopolesInstantonsConfinement_static_first_integral_deriv_zero
import Theorems.Thm_MonopolesInstantonsConfinement_exists_const_of_deriv_zero

open Filter Topology
open MonopolesInstantonsConfinement

theorem solution (V : ℝ → ℝ) (hV : Differentiable ℝ V)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hEL : ∀ x, deriv (deriv φ) x = deriv V (φ x)) :
    ∃ c : ℝ, ∀ x, 1 / 2 * deriv φ x ^ 2 - V (φ x) = c := by
  have hderiv : ∀ x, deriv (fun y => 1 / 2 * deriv φ y ^ 2 - V (φ y)) x = 0 := by
    intro x
    exact static_first_integral_deriv_zero V hV φ hφ hEL x
  exact exists_const_of_deriv_zero V hV φ hφ hderiv
