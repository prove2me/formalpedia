-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45SmoothPlateauJetV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:24:33.519809+00:00
-- url     : https://prove2.me/submissions/76ac33a0-fdde-4096-9ffa-dd4de522bb33

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
open Filter Set
open scoped ContDiff
set_option autoImplicit false

/-- A smooth scalar plateau has vanishing first and second derivatives on its interior. -/
theorem solution (R : ℝ) (hR : 0 ≤ R) :
    ∃ b : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) b ∧
      (∀ x, |x| ≤ R → b x = 1 ∧ deriv b x = 0 ∧ deriv (deriv b) x = 0) ∧
      (∀ x, R + 3 < |x| → b x = 0 ∧ deriv b x = 0 ∧ deriv (deriv b) x = 0) := by
  let φ : ContDiffBump (0 : ℝ) := ⟨R+1,R+3,by linarith,by linarith⟩
  refine ⟨φ,φ.contDiff,?_,?_⟩
  · intro x hx
    have hball : x ∈ Metric.ball (0 : ℝ) φ.rIn := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      change |x| < R+1
      linarith
    have he : (φ : ℝ → ℝ) =ᶠ[nhds x] (fun _ => 1) :=
      φ.eventuallyEq_one_of_mem_ball hball
    exact ⟨he.eq_of_nhds, by simpa using he.deriv_eq, by simpa using he.deriv.deriv_eq⟩
  · intro x hx
    have he : (φ : ℝ → ℝ) =ᶠ[nhds x] (fun _ => 0) := by
      have hs : IsOpen {y : ℝ | R+3 < |y|} := isOpen_lt continuous_const continuous_abs
      filter_upwards [hs.mem_nhds hx] with y hy
      apply φ.zero_of_le_dist
      rw [Real.dist_eq, sub_zero]
      exact le_of_lt hy
    exact ⟨he.eq_of_nhds, by simpa using he.deriv_eq, by simpa using he.deriv.deriv_eq⟩
