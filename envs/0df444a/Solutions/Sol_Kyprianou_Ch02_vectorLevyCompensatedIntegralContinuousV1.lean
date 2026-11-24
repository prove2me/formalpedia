-- Prove2me | solution 1 for Kyprianou.Ch02.vectorLevyCompensatedIntegralContinuousV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:32:50.657912+00:00
-- url     : https://prove2.me/submissions/1f5b78a8-2865-4a12-a93f-302d4d77dee9

import Theorems.Thm_Kyprianou_Ch02_vectorLevyCompensatedEnvelopeV1
import Mathlib
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (d : ℕ) (ν : Measure (Fin d → ℝ))
    (hLevy : (∫⁻ x, ENNReal.ofReal (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ 2)) ∂ν) < ⊤) :
    ContinuousAt (fun θ : Fin d → ℝ => ∫ x, (1 - Complex.exp (Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ)) +
       Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ) * (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν) 0 := by
  classical
  let r (x : Fin d → ℝ) := Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ))
  let dot (θ x : Fin d → ℝ) := ∑ i : Fin d, θ i * x i
  let F (θ x : Fin d → ℝ) : ℂ :=
    1 - Complex.exp (Complex.I * (dot θ x : ℂ)) +
      Complex.I * (dot θ x : ℂ) * (if r x < 1 then 1 else 0)
  let w (x : Fin d → ℝ) := min 1 (r x ^ 2)
  have hr (x : Fin d → ℝ) : 0 ≤ r x := Real.sqrt_nonneg _
  have hw (x : Fin d → ℝ) : 0 ≤ w x := by dsimp [w]; positivity
  have hrc : Continuous r := by dsimp [r]; fun_prop
  have hwc : Continuous w := by unfold w; fun_prop
  have hwi : Integrable w ν := by
    refine ⟨hwc.measurable.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ hw)).2 hLevy
  have hb (θ x : Fin d → ℝ) :
      ‖F θ x‖ ≤ (2 + 3 * ((d : ℝ) * ‖θ‖)^2) * w x :=
    Kyprianou.Ch02.vectorLevyCompensatedEnvelopeV1 d θ x
  have hFm (θ : Fin d → ℝ) : Measurable (F θ) := by
    have hi : Measurable (fun x : Fin d → ℝ => if r x < 1 then (1 : ℂ) else 0) :=
      Measurable.ite (measurableSet_lt hrc.measurable measurable_const)
        measurable_const measurable_const
    have hd : Continuous (dot θ) := by dsimp [dot]; fun_prop
    unfold F
    fun_prop
  have hFc (x : Fin d → ℝ) : Continuous (fun θ => F θ x) := by
    unfold F dot
    fun_prop
  let B := fun x => (2 + 3 * (d : ℝ)^2) * w x
  have hBi : Integrable B ν := hwi.const_mul _
  have hm : ∀ᶠ θ in nhds (0 : Fin d → ℝ), AEStronglyMeasurable (F θ) ν :=
    Eventually.of_forall fun θ => (hFm θ).aestronglyMeasurable
  have hnorm : ∀ᶠ θ in nhds (0 : Fin d → ℝ), ‖θ‖ ≤ 1 := by
    have ht : Tendsto (fun θ : Fin d → ℝ => ‖θ‖) (nhds 0) (nhds 0) := by
      have h := (continuous_norm : Continuous (fun θ : Fin d → ℝ => ‖θ‖)).continuousAt (x := (0 : Fin d → ℝ))
      change Tendsto _ (nhds (0 : Fin d → ℝ)) (nhds ‖(0 : Fin d → ℝ)‖) at h
      simpa only [norm_zero] using h
    exact ((tendsto_order.1 ht).2 1 zero_lt_one).mono fun _ h => h.le
  have hB : ∀ᶠ θ in nhds (0 : Fin d → ℝ), ∀ᵐ x ∂ν, ‖F θ x‖ ≤ B x := by
    filter_upwards [hnorm] with θ hθ
    refine ae_of_all _ fun x => (hb θ x).trans ?_
    apply mul_le_mul_of_nonneg_right _ (hw x)
    have h : (d : ℝ) * ‖θ‖ ≤ d := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
    have hs := (sq_le_sq₀ (show 0 ≤ (d : ℝ) * ‖θ‖ by positivity)
      (Nat.cast_nonneg (α := ℝ) d)).2 h
    linarith
  exact tendsto_integral_filter_of_dominated_convergence B hm hB hBi
    (ae_of_all _ fun x => (hFc x).continuousAt.tendsto)
