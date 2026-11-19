-- Prove2me | solution 2 for Kyprianou.Ch01.inverseGaussianZeroDiscountPositiveDrift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T11:31:00.741397+00:00
-- url     : https://prove2.me/submissions/d7e2596e-35e6-41b3-86a0-37f66fd6fbd0

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_brownianDiscountedUpperPassage

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false


private theorem laplacePointwiseZero
    {Ω : Type*} (τ : Ω → WithTop ℝ≥0)
    (q : ℕ → ℝ) (hq : Tendsto q atTop (𝓝 0)) (ω : Ω) :
    Tendsto (fun n => passageLaplace τ (q n) ω)
      atTop (𝓝 (passageLaplace τ 0 ω)) := by
  unfold passageLaplace
  cases hτ : τ ω with
  | top => simp [hτ]
  | coe t =>
    simp only [hτ]
    have h : Tendsto (fun n => -q n * (t : ℝ)) atTop (𝓝 0) := by
      convert (hq.neg.mul_const (t : ℝ)) using 1 <;> simp
    simpa [Function.comp_def, neg_mul] using
      (Real.continuous_exp.tendsto 0).comp h

private theorem laplaceNormBound
    {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (q : ℝ)
    (hq : 0 ≤ q) (ω : Ω) : ‖passageLaplace τ q ω‖ ≤ (1 : ℝ) := by
  unfold passageLaplace
  cases hτ : τ ω with
  | top => simp [hτ]
  | coe t =>
    have h : -q * (t : ℝ) ≤ 0 := by
      have ht : (0 : ℝ) ≤ (t : ℝ) := by positivity
      nlinarith
    simpa [hτ, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      (Real.exp_le_one_iff.mpr h)


private theorem brownianPositiveQ
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (b : ℝ)
    (hB : IsLinearBrownian P B 1 b)
    (hmeas : ∀ t : ℝ≥0, Measurable (B t))
    (s q : ℝ) (hs : 0 < s) (hq : 0 < q) :
    Integrable (passageLaplace (firstUpperPassage B s) q) P ∧
      (∫ ω, passageLaplace (firstUpperPassage B s) q ω ∂P) =
        Real.exp (-s * (Real.sqrt (b ^ 2 + 2 * q) - b)) := by
  simpa [mul_assoc] using
    (Kyprianou.Ch01.brownianDiscountedUpperPassage
      P B 1 b q s (by norm_num) hq hs hB hmeas)


private theorem boundedIntegralLimit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (f : Ω → ℝ)
    (hInt : ∀ n, Integrable (F n) P)
    (hlim : ∀ ω, Tendsto (fun n => F n ω) atTop (𝓝 (f ω)))
    (hBound : ∀ n ω, ‖F n ω‖ ≤ (1 : ℝ))
    (hBound0 : ∀ ω, ‖f ω‖ ≤ (1 : ℝ)) :
    Integrable f P ∧
      Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 (∫ ω, f ω ∂P)) := by
  have hfm (n : ℕ) : AEStronglyMeasurable (F n) P := (hInt n).aestronglyMeasurable
  have hf0 : AEStronglyMeasurable f P :=
    aestronglyMeasurable_of_tendsto_ae atTop hfm (Filter.Eventually.of_forall hlim)
  constructor
  · exact (integrable_const (1 : ℝ)).mono' hf0 (Filter.Eventually.of_forall hBound0)
  · exact tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      hfm (integrable_const _) (fun n => Filter.Eventually.of_forall (hBound n))
      (Filter.Eventually.of_forall hlim)

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (b s : ℝ)
    (hb : 0 < b) (hs : 0 < s)
    (hB : Kyprianou.Ch01.IsLinearBrownian P B 1 b)
    (hmeas : ∀ t : ℝ≥0, Measurable (B t)) :
    Integrable (Kyprianou.Ch01.passageLaplace
      (Kyprianou.Ch01.firstUpperPassage B s) 0) P ∧
    (∫ ω, Kyprianou.Ch01.passageLaplace
      (Kyprianou.Ch01.firstUpperPassage B s) 0 ω ∂P) = 1 := by
  let τ := firstUpperPassage B s
  let qn : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  let F : ℕ → Ω → ℝ := fun n ω => passageLaplace τ (qn n) ω
  let f : Ω → ℝ := passageLaplace τ 0
  have hqpos (n : ℕ) : 0 < qn n := by
    dsimp [qn]; positivity
  have hq : Tendsto qn atTop (𝓝 0) := by
    simpa only [qn, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim (ω : Ω) : Tendsto (fun n => F n ω) atTop (𝓝 (f ω)) :=
    laplacePointwiseZero τ qn hq ω
  have hpos (n : ℕ) : Integrable (F n) P ∧
      (∫ ω, F n ω ∂P) =
        Real.exp (-s * (Real.sqrt (b ^ 2 + 2 * qn n) - b)) :=
    brownianPositiveQ P B b hB hmeas s (qn n) hs (hqpos n)
  have hbound (n : ℕ) (ω : Ω) : ‖F n ω‖ ≤ (1 : ℝ) := laplaceNormBound τ (qn n) (hqpos n).le ω
  have hbound0 (ω : Ω) : ‖f ω‖ ≤ (1 : ℝ) := laplaceNormBound τ 0 le_rfl ω
  obtain ⟨hint0, hintlim⟩ :=
    boundedIntegralLimit P F f (fun n => (hpos n).1) hlim hbound hbound0
  have hcontinuous : Continuous
      (fun q : ℝ => Real.exp (-s * (Real.sqrt (b ^ 2 + 2 * q) - b))) := by fun_prop
  have hroot : Real.sqrt (b ^ 2) = b := by
    simpa only [abs_of_pos hb] using Real.sqrt_sq_eq_abs b
  have hrhs : Tendsto
      (fun n => Real.exp (-s * (Real.sqrt (b ^ 2 + 2 * qn n) - b)))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, mul_zero, add_zero, hroot,
      sub_self, mul_zero, neg_zero, Real.exp_zero] using
      (hcontinuous.tendsto 0).comp hq
  have hintlim1 : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 1) := by
    convert hrhs using 1
    funext n; exact (hpos n).2
  exact ⟨hint0, tendsto_nhds_unique hintlim hintlim1⟩
