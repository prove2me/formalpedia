-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_finite_negative_jump_transforms
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T17:55:05.134653+00:00
-- url     : https://prove2.me/submissions/dabe6a3e-7760-49f4-a6d3-51d0424e1ddd

import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.Ring
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_compound_poisson_marked_transforms

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem result81_centered_jump_integral
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν J : Measure ℝ) (r : ℝ≥0)
    (hscale : (r : ℝ≥0∞) • J = ν + Measure.dirac 0)
    (F : ℝ → E) (hF : Integrable F ν) (h0 : F 0 = 0) :
    (r : ℝ) • (∫ y, F y ∂J) = ∫ y, F y ∂ν := by
  have hD : Integrable F (Measure.dirac 0) := integrable_dirac (by simpa [h0])
  calc
    _ = ∫ y, F y ∂((r : ℝ≥0∞) • J) := by rw [integral_smul_measure, ENNReal.coe_toReal]
    _ = _ := by rw [hscale, integral_add_measure hF hD, integral_dirac, h0, add_zero]

private theorem result81_exp_negative_support
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ≤ 0)
    (β : ℝ) (hβ : 0 ≤ β) : Integrable (fun y => Real.exp (β * y)) ν := by
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [hν] with y hy
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact mul_nonpos_of_nonneg_of_nonpos hβ hy

private theorem result81_complex_character_integrable
    (ν : Measure ℝ) [IsFiniteMeasure ν] (ξ : ℝ) :
    Integrable (fun y : ℝ => Complex.exp ((ξ : ℂ) * y * Complex.I)) ν := by
  apply Integrable.of_bound (by fun_prop) 1
  exact Eventually.of_forall fun y => by
    simpa only [Complex.ofReal_mul] using (Complex.norm_exp_ofReal_mul_I (ξ * y)).le

theorem solution
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hneg : ν (Ici (0 : ℝ)) = 0)
    (t : ℝ≥0) :
    ∃ μ : ProbabilityMeasure ℝ,
      (∀ ξ : ℝ, Integrable (fun y : ℝ => Complex.exp ((ξ : ℂ) * y * Complex.I) - 1) ν ∧
        charFun (μ : Measure ℝ) ξ = Complex.exp (((t : ℝ) : ℂ) *
          ∫ y : ℝ, (Complex.exp ((ξ : ℂ) * y * Complex.I) - 1) ∂ν)) ∧
      (∀ β : ℝ, 0 ≤ β → Integrable (fun y => Real.exp (β * y) - 1) ν ∧
        Integrable (fun x => Real.exp (β * x)) (μ : Measure ℝ) ∧
        (∫ x, Real.exp (β * x) ∂(μ : Measure ℝ)) =
          Real.exp ((t : ℝ) * ∫ y, (Real.exp (β * y) - 1) ∂ν)) := by
  let r : ℝ≥0 := (ν univ).toNNReal + 1
  let J : Measure ℝ := (r : ℝ≥0∞)⁻¹ • (ν + Measure.dirac 0)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr0 : (r : ℝ≥0∞) ≠ 0 := by simpa using hr.ne'
  have hm : ν univ + 1 = (r : ℝ≥0∞) := by
    simp [r, ENNReal.coe_toNNReal, measure_ne_top]
  letI : IsProbabilityMeasure J := ⟨by
    change ((r : ℝ≥0∞)⁻¹ • (ν + Measure.dirac (0 : ℝ))) univ = 1
    rw [Measure.smul_apply, smul_eq_mul, Measure.add_apply,
      (measure_univ : (Measure.dirac (0 : ℝ)) univ = 1), hm]
    exact ENNReal.inv_mul_cancel hr0 ENNReal.coe_ne_top⟩
  have hscale : (r : ℝ≥0∞) • J = ν + Measure.dirac 0 := by
    change (r : ℝ≥0∞) • ((r : ℝ≥0∞)⁻¹ • (ν + Measure.dirac 0)) = _
    rw [smul_smul, ENNReal.mul_inv_cancel hr0 ENNReal.coe_ne_top, one_smul]
  have hpos : ν (Ioi (0 : ℝ)) = 0 := measure_mono_null Ioi_subset_Ici_self hneg
  have hνae : ∀ᵐ y ∂ν, y ≤ 0 := ae_iff.2 (by simpa only [not_le, Ioi] using hpos)
  have hJae : ∀ᵐ y ∂J, y ≤ 0 := by
    simp only [ae_iff, not_le]
    change J (Ioi (0 : ℝ)) = 0
    simp [J, Measure.smul_apply, Measure.add_apply, hpos]
  obtain ⟨μ, hchar, hreal⟩ :=
    Kyprianou.Ch08.StageB.source_result81_compound_poisson_marked_transforms J hJae r hr t
  refine ⟨μ, ?_, ?_⟩
  · intro ξ
    let F (y : ℝ) := Complex.exp ((ξ : ℂ) * y * Complex.I)
    have hFint := (result81_complex_character_integrable ν ξ).sub (integrable_const (1 : ℂ))
    refine ⟨hFint, ?_⟩
    have hcent : (∫ y, F y - 1 ∂J) = charFun J ξ - 1 := by
      rw [integral_sub (result81_complex_character_integrable J ξ) (integrable_const _), charFun_apply_real]
      simp [F]
    have he : ((r : ℝ) : ℂ) * (charFun J ξ - 1) = ∫ y, (F y - 1) ∂ν := by
      rw [← hcent, ← Complex.real_smul]
      exact result81_centered_jump_integral ν J r hscale (fun y => F y - 1) hFint (by simp [F])
    change charFun (μ : Measure ℝ) ξ = Complex.exp (((t : ℝ) : ℂ) * ∫ y, (F y - 1) ∂ν)
    rw [hchar ξ, ← he]
    congr 1
    push_cast
    ring
  · intro β hβ
    let F (y : ℝ) := Real.exp (β * y)
    have hFint := (result81_exp_negative_support ν hνae β hβ).sub (integrable_const (1 : ℝ))
    have hcent : (∫ y, F y - 1 ∂J) = (∫ y, F y ∂J) - 1 := by
      rw [integral_sub (result81_exp_negative_support J hJae β hβ) (integrable_const _)]
      simp [F]
    have he : (r : ℝ) * ((∫ y, F y ∂J) - 1) = ∫ y, (F y - 1) ∂ν := by
      simpa only [hcent, smul_eq_mul] using
        result81_centered_jump_integral ν J r hscale (fun y => F y - 1) hFint (by simp [F])
    refine ⟨hFint, (hreal β hβ).1, ?_⟩
    change (∫ x, F x ∂(μ : Measure ℝ)) = Real.exp ((t : ℝ) * ∫ y, (F y - 1) ∂ν)
    rw [(hreal β hβ).2, ← he]
    congr 1
    ring
