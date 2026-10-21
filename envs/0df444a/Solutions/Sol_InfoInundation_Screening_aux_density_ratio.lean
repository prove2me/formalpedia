-- Prove2me | solution 1 for InfoInundation.Screening.aux_density_ratio
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:35:54.199001+00:00
-- url     : https://prove2.me/submissions/030f31ca-1571-4df3-b2f5-904e53320d24

import Mathlib
import Definitions.Def_InfoInundation_Screening_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InfoInundation.Screening

lemma ii_aux_int (G : Measure ℝ) [IsFiniteMeasure G] (s r p : ℝ) (hs : 0 < s) (hp : 0 ≤ p) :
    Integrable (fun σ : ℝ => (σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) G := by
  have hw : ∀ σ : ℝ, 0 < σ ^ 2 + s ^ 2 := fun σ => by positivity
  have hc : Continuous (fun σ : ℝ => (σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) := by
    apply Continuous.mul
    · exact Continuous.rpow_const (by fun_prop) (fun x => Or.inl (hw x).ne')
    · apply Real.continuous_exp.comp
      apply Continuous.neg
      exact continuous_const.div (by fun_prop) (fun x => by have := hw x; positivity)
  refine Integrable.of_bound hc.aestronglyMeasurable ((s ^ 2) ^ (-p) * Real.exp (|r| / (2 * s ^ 2))) ?_
  refine Filter.Eventually.of_forall (fun σ => ?_)
  have h1 : (σ ^ 2 + s ^ 2) ^ (-p) ≤ (s ^ 2) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg σ]) (by linarith)
  have h2 : Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2)))) ≤ Real.exp (|r| / (2 * s ^ 2)) := by
    apply Real.exp_le_exp.2
    have a1 : -(r / (2 * (σ ^ 2 + s ^ 2))) ≤ |r| / (2 * (σ ^ 2 + s ^ 2)) := by
      rw [← neg_div]
      apply div_le_div_of_nonneg_right _ (by have := hw σ; positivity)
      linarith [neg_abs_le r]
    have a2 : |r| / (2 * (σ ^ 2 + s ^ 2)) ≤ |r| / (2 * s ^ 2) := by
      apply div_le_div_of_nonneg_left (abs_nonneg r) (by positivity)
      nlinarith [sq_nonneg σ]
    linarith
  rw [Real.norm_of_nonneg (by have := hw σ; positivity)]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

lemma ii_aux_pos (G : Measure ℝ) [IsProbabilityMeasure G] (s r p : ℝ) (hs : 0 < s) (hp : 0 ≤ p) :
    0 < auxMoment G s r p := by
  unfold auxMoment
  rw [integral_pos_iff_support_of_nonneg (fun σ => by have : 0 < σ ^ 2 + s ^ 2 := by positivity
                                                      positivity) (ii_aux_int G s r p hs hp)]
  have : Function.support (fun σ : ℝ => (σ ^ 2 + s ^ 2) ^ (-p) * Real.exp (-(r / (2 * (σ ^ 2 + s ^ 2))))) = Set.univ := by
    ext σ
    have : 0 < σ ^ 2 + s ^ 2 := by positivity
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    positivity
  rw [this]; simp

lemma ii_lik (μ s σ z : ℝ) (hs : 0 < s) :
    likelihood μ s σ z = (Real.sqrt (2 * Real.pi))⁻¹ *
      ((σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (-((z - μ) ^ 2 / (2 * (σ ^ 2 + s ^ 2))))) := by
  have hw : 0 < σ ^ 2 + s ^ 2 := by positivity
  unfold likelihood psi
  rw [Real.sq_sqrt (by positivity)]
  have e1 : (σ ^ 2 + s ^ 2) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (σ ^ 2 + s ^ 2))⁻¹ := by
    rw [Real.rpow_neg hw.le, Real.sqrt_eq_rpow]
  rw [e1, Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num)]
  have : 0 < Real.sqrt (σ ^ 2 + s ^ 2) := Real.sqrt_pos.2 hw
  have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  field_simp

lemma ii_lik_int (G : Measure ℝ) [IsFiniteMeasure G] (μ s z : ℝ) (hs : 0 < s) :
    Integrable (fun σ => likelihood μ s σ z) G := by
  have := (ii_aux_int G s ((z - μ) ^ 2) (1 / 2) hs (by norm_num)).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  refine this.congr (Filter.Eventually.of_forall (fun σ => ?_))
  simp only
  rw [ii_lik μ s σ z hs]

/-- `∫ (σ²+s²)^(-q) · likelihood = c · auxMoment (q + 1/2)`. -/
lemma ii_num (G : Measure ℝ) (μ s z q : ℝ) (hs : 0 < s) :
    ∫ σ, (σ ^ 2 + s ^ 2) ^ (-q) * likelihood μ s σ z ∂G =
      (Real.sqrt (2 * Real.pi))⁻¹ * auxMoment G s ((z - μ) ^ 2) (q + 1 / 2) := by
  unfold auxMoment
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun σ => ?_))
  simp only
  have hw : 0 < σ ^ 2 + s ^ 2 := by positivity
  rw [ii_lik μ s σ z hs, neg_add, Real.rpow_add hw]
  ring

lemma ii_den (G : Measure ℝ) (μ s z : ℝ) (hs : 0 < s) :
    ∫ σ, likelihood μ s σ z ∂G =
      (Real.sqrt (2 * Real.pi))⁻¹ * auxMoment G s ((z - μ) ^ 2) (0 + 1 / 2) := by
  have := ii_num G μ s z 0 hs
  simpa using this

theorem solution (G : Measure ℝ) (hG : AccuracyLaw G) (μ s : ℝ) (hs : 0 < s) (z : ℝ) :
    postExp G μ s z (fun σ => (σ ^ 2 + s ^ 2)⁻¹) =
      auxExp G s ((z - μ) ^ 2) (3 / 2) / auxExp G s ((z - μ) ^ 2) (1 / 2) := by
  haveI := hG.isProb
  have hc : (Real.sqrt (2 * Real.pi))⁻¹ ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    positivity
  have h0 : auxMoment G s ((z - μ) ^ 2) 0 ≠ 0 := (ii_aux_pos G s _ 0 hs le_rfl).ne'
  have hnum : ∫ σ, (σ ^ 2 + s ^ 2)⁻¹ * likelihood μ s σ z ∂G =
      (Real.sqrt (2 * Real.pi))⁻¹ * auxMoment G s ((z - μ) ^ 2) (3 / 2) := by
    have := ii_num G μ s z 1 hs
    have e : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
    rw [e] at this
    simpa [Real.rpow_neg_one] using this
  have hden := ii_den G μ s z hs
  rw [zero_add] at hden
  unfold postExp auxExp
  rw [hnum, hden, mul_div_mul_left _ _ hc, div_div_div_cancel_right₀ h0]
