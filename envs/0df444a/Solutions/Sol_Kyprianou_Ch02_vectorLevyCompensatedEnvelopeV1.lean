-- Prove2me | solution 1 for Kyprianou.Ch02.vectorLevyCompensatedEnvelopeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:32:33.492514+00:00
-- url     : https://prove2.me/submissions/2acec12b-2418-4d33-8758-c36c0d74fa53

import Theorems.Thm_ProbabilityTheory_norm_levyCompensatedIntegrand_le
import Theorems.Thm_ProbabilityTheory_levyCompensatedIntegrand_def
import Mathlib
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (d : ℕ) (θ x : Fin d → ℝ) :
    ‖(1 - Complex.exp (Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ)) +
       Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ) * (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0))‖ ≤
      (2 + 3 * ((d : ℝ) * ‖θ‖)^2) * (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ 2)) := by
  classical
  let r (x : Fin d → ℝ) := Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ))
  let dot (θ x : Fin d → ℝ) := ∑ i : Fin d, θ i * x i
  let F (θ x : Fin d → ℝ) : ℂ :=
    1 - Complex.exp (Complex.I * (dot θ x : ℂ)) +
      Complex.I * (dot θ x : ℂ) * (if r x < 1 then 1 else 0)
  let w (x : Fin d → ℝ) := min 1 (r x ^ 2)
  have hr (x : Fin d → ℝ) : 0 ≤ r x := Real.sqrt_nonneg _
  have hw (x : Fin d → ℝ) : 0 ≤ w x := by dsimp [w]; positivity
  have hcoord (x : Fin d → ℝ) (i : Fin d) : |x i| ≤ r x := by
    apply abs_le_of_sq_le_sq _ (hr x)
    rw [show r x ^ 2 = ∑ j : Fin d, x j ^ (2 : ℕ) by
      unfold r; exact Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (x j))]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have hdot (θ x : Fin d → ℝ) : |dot θ x| ≤ (d : ℝ) * ‖θ‖ * r x := by
    calc
      |dot θ x| ≤ ∑ i : Fin d, |θ i * x i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, ‖θ‖ * r x := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        have hi : |θ i| ≤ ‖θ‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm θ i
        exact mul_le_mul hi (hcoord x i) (abs_nonneg _) (norm_nonneg _)
      _ = _ := by simp [mul_assoc]
  have hb (θ x : Fin d → ℝ) :
      ‖F θ x‖ ≤ (2 + 3 * ((d : ℝ) * ‖θ‖)^2) * w x := by
    by_cases hx : r x = 0
    · have hz : dot θ x = 0 := by
        have h := hdot θ x
        rw [hx, mul_zero] at h
        exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
      simp [F, hz, w, hx]
    have hp : 0 < r x := lt_of_le_of_ne (hr x) (Ne.symm hx)
    let ξ := dot θ x / r x
    have hξ : |ξ| ≤ (d : ℝ) * ‖θ‖ := by
      rw [show ξ = dot θ x / r x from rfl, abs_div, abs_of_pos hp]
      exact (div_le_iff₀ hp).2 (hdot θ x)
    have hξr : r x * ξ = dot θ x := by
      dsimp [ξ]
      field_simp
    have hz : (r x : ℂ) * (ξ : ℂ) * Complex.I =
        Complex.I * (dot θ x : ℂ) := by
      rw [← Complex.ofReal_mul, hξr, mul_comm]
    have hF : F θ x = -ProbabilityTheory.levyCompensatedIntegrand ξ (r x) := by
      rw [ProbabilityTheory.levyCompensatedIntegrand_def, abs_of_nonneg (hr x), hz]
      unfold F
      ring
    rw [hF, norm_neg]
    refine (ProbabilityTheory.norm_levyCompensatedIntegrand_le ξ (r x)).trans ?_
    apply mul_le_mul_of_nonneg_right _ (hw x)
    have hs : ξ ^ 2 ≤ ((d : ℝ) * ‖θ‖)^2 :=
      sq_le_sq.mpr (hξ.trans (le_abs_self _))
    linarith
  exact hb θ x
