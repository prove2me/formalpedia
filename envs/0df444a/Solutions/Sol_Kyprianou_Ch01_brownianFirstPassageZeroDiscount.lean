-- Prove2me | solution 1 for Kyprianou.Ch01.brownianFirstPassageZeroDiscount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:46:43.661208+00:00
-- url     : https://prove2.me/submissions/8b5714ad-9c04-4700-80e5-6c3f90815ad9

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

/-- Discount parameters decreasing strictly to zero. -/
private noncomputable def zeroDiscountSeq (n : ℕ) : ℝ :=
  ((n : ℝ) + 1)⁻¹

private theorem zeroDiscountSeq_pos (n : ℕ) : 0 < zeroDiscountSeq n :=
  inv_pos.mpr (by positivity)

private theorem zeroDiscountSeq_tendsto :
    Tendsto zeroDiscountSeq atTop (𝓝 (0 : ℝ)) := by
  unfold zeroDiscountSeq
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

/-- Every finite nonnegative passage time has payoff tending to one
    under vanishing strictly positive discounts; infinite passage stays zero. -/
private theorem passageLaplace_tendsto_zeroDiscount
    {Ω : Type*} [MeasurableSpace Ω] (T : Ω → WithTop ℝ≥0) (ω : Ω) :
    Tendsto (fun n => passageLaplace T (zeroDiscountSeq n) ω)
      atTop (𝓝 (passageLaplace T 0 ω)) := by
  cases hT : T ω with
  | top =>
    simp [passageLaplace, hT]
  | coe t =>
    have hzero : Tendsto
        (fun n => -(zeroDiscountSeq n) * (t : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      convert zeroDiscountSeq_tendsto.neg.mul_const (t : ℝ) using 1 <;> simp
    have hexp := Real.continuous_exp.continuousAt.tendsto.comp hzero
    simpa only [Function.comp_def, passageLaplace, hT,
      neg_zero, zero_mul, Real.exp_zero] using hexp

private theorem passageLaplace_norm_le_one
    {Ω : Type*} [MeasurableSpace Ω] (T : Ω → WithTop ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) :
    ‖passageLaplace T q ω‖ ≤ (1 : ℝ) := by
  cases hT : T ω with
  | top =>
    simp [passageLaplace, hT]
  | coe t =>
    have hnonpos : -q * (t : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) (NNReal.coe_nonneg t)
    simpa [passageLaplace, hT, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      using (Real.exp_le_one_iff.mpr hnonpos)

/-- The q=0 Brownian passage transform is the dominated q↓0 limit. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : Kyprianou.Ch01.IsLinearBrownian P B 1 0)
    (hmeas : ∀ t : ℝ≥0, Measurable (B t))
    (s : ℝ) (hs : 0 < s) :
    Integrable (Kyprianou.Ch01.passageLaplace
      (Kyprianou.Ch01.firstUpperPassage B s) 0) P ∧
    (∫ ω, Kyprianou.Ch01.passageLaplace
      (Kyprianou.Ch01.firstUpperPassage B s) 0 ω ∂P) = 1 := by
  let T := firstUpperPassage B s
  let F : ℕ → Ω → ℝ :=
    fun n ω => passageLaplace T (zeroDiscountSeq n) ω
  let f : Ω → ℝ := passageLaplace T 0
  have hpositive (n : ℕ) :=
    Kyprianou.Ch01.brownianDiscountedUpperPassage
      P B 1 0 (zeroDiscountSeq n) s
      (by norm_num) (zeroDiscountSeq_pos n) hs hB hmeas
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) P :=
    fun n => (hpositive n).1.aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ (fun _ : Ω => (1 : ℝ)) ω :=
    fun n => Filter.Eventually.of_forall fun ω =>
      passageLaplace_norm_le_one T (zeroDiscountSeq n)
        (zeroDiscountSeq_pos n).le ω
  have hlimit : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (f ω)) :=
    Filter.Eventually.of_forall fun ω => passageLaplace_tendsto_zeroDiscount T ω
  have hdct := tendsto_integral_of_dominated_convergence
    (fun _ : Ω => (1 : ℝ)) hFmeas (integrable_const 1) hbound hlimit
  have hFformula (n : ℕ) :
      (∫ ω, F n ω ∂P) =
        Real.exp (-s * Real.sqrt (2 * zeroDiscountSeq n)) := by
    simpa [F] using (hpositive n).2
  have hFormulaLimit :
      Tendsto (fun n => Real.exp (-s * Real.sqrt (2 * zeroDiscountSeq n)))
        atTop (𝓝 (1 : ℝ)) := by
    have hc : Continuous (fun q : ℝ => Real.exp (-s * Real.sqrt (2 * q))) := by
      fun_prop
    have h := ((hc.tendsto 0).comp zeroDiscountSeq_tendsto)
    simpa only [Function.comp_def, mul_zero, Real.sqrt_zero,
      Real.exp_zero, neg_zero] using h
  have hIntegralLimit :
      Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hFformula] using hFormulaLimit
  have hfmeas : AEStronglyMeasurable f P :=
    aestronglyMeasurable_of_tendsto_ae atTop hFmeas hlimit
  have hfint : Integrable f P :=
    Integrable.of_bound hfmeas 1
      (Filter.Eventually.of_forall fun ω => passageLaplace_norm_le_one T 0 le_rfl ω)
  refine ⟨hfint, ?_⟩
  exact tendsto_nhds_unique hdct hIntegralLimit
