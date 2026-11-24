-- Prove2me | solution 1 for Kyprianou.Ch02.vectorLevyCompensatedCutoffIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:31:03.430089+00:00
-- url     : https://prove2.me/submissions/84b08ee3-fc3f-4448-b2be-174bf9ff6eb6

import Theorems.Thm_Kyprianou_Ch02_vectorLevyCompensatedEnvelopeV1
import Mathlib
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (d : ℕ) (ν : Measure (Fin d → ℝ))
    (hLevy : (∫⁻ x, ENNReal.ofReal (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ 2)) ∂ν) < ⊤) (θ : Fin d → ℝ) :
    Tendsto (fun n : ℕ => ∫ x, (1 - Complex.exp (Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ)) +
       Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ) * (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂(ν.restrict {x | 1 / ((n : ℝ) + 1) ≤ Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ))}))
      atTop (nhds (∫ x, (1 - Complex.exp (Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ)) +
       Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ) * (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν)) := by
  classical
  let r (x : Fin d → ℝ) := Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ))
  let dot (θ x : Fin d → ℝ) := ∑ i : Fin d, θ i * x i
  let F (θ x : Fin d → ℝ) : ℂ :=
    1 - Complex.exp (Complex.I * (dot θ x : ℂ)) +
      Complex.I * (dot θ x : ℂ) * (if r x < 1 then 1 else 0)
  let w (x : Fin d → ℝ) := min 1 (r x ^ 2)
  let S (n : ℕ) : Set (Fin d → ℝ) := {x | 1 / ((n : ℝ) + 1) ≤ r x}
  have hr (x : Fin d → ℝ) : 0 ≤ r x := Real.sqrt_nonneg _
  have hw (x : Fin d → ℝ) : 0 ≤ w x := by dsimp [w]; positivity
  have hrc : Continuous r := by dsimp [r]; fun_prop
  have hwc : Continuous w := by unfold w; fun_prop
  have hwi : Integrable w ν := by
    refine ⟨hwc.measurable.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ hw)).2 hLevy
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
  have hSm (n : ℕ) : MeasurableSet (S n) :=
    measurableSet_le measurable_const hrc.measurable
  let B := fun x => (2 + 3 * ((d : ℝ) * ‖θ‖)^2) * w x
  have hBi : Integrable B ν := hwi.const_mul _
  have hm : ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable ((S n).indicator (F θ)) ν :=
    Eventually.of_forall fun n => ((hFm θ).indicator (hSm n)).aestronglyMeasurable
  have hB : ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂ν,
      ‖(S n).indicator (F θ) x‖ ≤ B x := by
    refine Eventually.of_forall fun n => ae_of_all _ fun x => ?_
    by_cases hx : x ∈ S n
    · rw [Set.indicator_of_mem hx]; exact hb θ x
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact le_trans (norm_nonneg _) (hb θ x)
  have hl : ∀ᵐ x ∂ν,
      Tendsto (fun n => (S n).indicator (F θ) x) atTop (nhds (F θ x)) := by
    refine ae_of_all _ fun x => ?_
    by_cases hx : r x = 0
    · have hz : dot θ x = 0 := by
        have h := hdot θ x
        rw [hx, mul_zero] at h
        exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
      have hf0 : F θ x = 0 := by simp [F, hz]
      simp [hf0, Set.indicator_apply]
    · have hp : 0 < r x := lt_of_le_of_ne (hr x) (Ne.symm hx)
      have hsmall := (tendsto_order.1
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).2 (r x) hp
      apply tendsto_const_nhds.congr'
      filter_upwards [hsmall] with n hn
      exact (Set.indicator_of_mem (show x ∈ S n from hn.le) (F θ)).symm
  have hlim := tendsto_integral_filter_of_dominated_convergence B hm hB hBi hl
  exact hlim.congr (fun n => integral_indicator (hSm n))
