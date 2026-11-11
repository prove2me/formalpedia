-- Prove2me | solution 1 for OAI.Invariant233.exists_circle_parameters
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:34:13.939458+00:00
-- url     : https://prove2.me/submissions/f30740f6-cd30-4259-b432-a9cd691af02e

import Mathlib
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.MetricSpace.Equicontinuity
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003
import Theorems.Thm_OAI_Invariant233_TrialSampling_expectation_squaredError_le_actual_bound

section
-- module Solutions.Q234_IR.Compat
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FiniteTestSelection
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233

open Set MeasureTheory
open scoped ENNReal

theorem exists_outside_bad_with_finite_tests
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (F : ι → Ω → ℝ≥0∞) (ε : ι → ℝ≥0∞) (bad : Set Ω)
    (hF : ∀ i ∈ s, AEMeasurable (F i) μ)
    (hε0 : ∀ i ∈ s, ε i ≠ 0) (hεtop : ∀ i ∈ s, ε i ≠ ∞)
    (hbudget : μ bad + ∑ i ∈ s, (∫⁻ ω, F i ω ∂μ) / ε i < 1) :
    ∃ ω, ω ∉ bad ∧ ∀ i ∈ s, F i ω < ε i := by
  classical
  let E := bad ∪ ⋃ i ∈ s, {ω | ε i ≤ F i ω}
  have hmeasure : μ E < 1 := by
    calc
      μ E ≤ μ bad + μ (⋃ i ∈ s, {ω | ε i ≤ F i ω}) := measure_union_le _ _
      _ ≤ μ bad + ∑ i ∈ s, μ {ω | ε i ≤ F i ω} :=
        add_le_add_right (measure_biUnion_finset_le s _) _
      _ ≤ μ bad + ∑ i ∈ s, (∫⁻ ω, F i ω ∂μ) / ε i := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro i hi
        exact meas_ge_le_lintegral_div (hF i hi) (hε0 i hi) (hεtop i hi)
      _ < 1 := hbudget
  have hE : E ≠ univ := by
    intro heq
    rw [heq, measure_univ] at hmeasure
    exact lt_irrefl _ hmeasure
  obtain ⟨ω, hω⟩ := Set.nonempty_compl.mpr hE
  refine ⟨ω, ?_, ?_⟩
  · intro hbad
    exact hω (Or.inl hbad)
  · intro i hi
    apply lt_of_not_ge
    intro htest
    exact hω (Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, htest⟩⟩))

theorem exists_outside_bad_with_finite_tests_and_ae
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (F : ι → Ω → ℝ≥0∞) (ε : ι → ℝ≥0∞) (bad : Set Ω)
    (hF : ∀ i ∈ s, AEMeasurable (F i) μ)
    (hε0 : ∀ i ∈ s, ε i ≠ 0) (hεtop : ∀ i ∈ s, ε i ≠ ∞)
    (hbudget : μ bad + ∑ i ∈ s, (∫⁻ ω, F i ω ∂μ) / ε i < 1)
    (P : Ω → Prop) (hP : ∀ᵐ ω ∂μ, P ω) :
    ∃ ω, P ω ∧ ω ∉ bad ∧ ∀ i ∈ s, F i ω < ε i := by
  have hnull : μ {ω | ¬ P ω} = 0 := ae_iff.mp hP
  have hbudget' : μ (bad ∪ {ω | ¬ P ω}) +
      ∑ i ∈ s, (∫⁻ ω, F i ω ∂μ) / ε i < 1 := by
    calc
      _ ≤ (μ bad + μ {ω | ¬ P ω}) +
          ∑ i ∈ s, (∫⁻ ω, F i ω ∂μ) / ε i :=
        add_le_add_left (measure_union_le _ _) _
      _ = μ bad + ∑ i ∈ s, (∫⁻ ω, F i ω ∂μ) / ε i := by rw [hnull, add_zero]
      _ < 1 := hbudget
  obtain ⟨ω, hω, htests⟩ := exists_outside_bad_with_finite_tests μ s F ε
    (bad ∪ {ω | ¬ P ω}) hF hε0 hεtop hbudget'
  refine ⟨ω, ?_, ?_, htests⟩
  · by_contra hnot
    exact hω (Or.inr hnot)
  · intro hb
    exact hω (Or.inl hb)

theorem exists_finite_tests_of_uniform_expectation_bound
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset ι) (F : ι → Ω → ℝ≥0∞) (bad : Set Ω)
    {ε δ β : ℝ≥0∞} (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞)
    (hF : ∀ i ∈ s, AEMeasurable (F i) μ)
    (hδ : ∀ i ∈ s, (∫⁻ ω, F i ω ∂μ) ≤ δ)
    (hbad : μ bad ≤ β) (hbudget : β + (s.card : ℝ≥0∞) * (δ / ε) < 1)
    (P : Ω → Prop) (hP : ∀ᵐ ω ∂μ, P ω) :
    ∃ ω, P ω ∧ ω ∉ bad ∧ ∀ i ∈ s, F i ω < ε := by
  apply exists_outside_bad_with_finite_tests_and_ae μ s F (fun _ => ε) bad hF
    (fun _ _ => hε0) (fun _ _ => hεtop) _ P hP
  calc
    μ bad + ∑ i ∈ s, (∫⁻ ω, F i ω ∂μ) / ε ≤ β + ∑ _i ∈ s, δ / ε := by
      apply add_le_add hbad
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      exact hδ i hi
    _ = β + (s.card : ℝ≥0∞) * (δ / ε) := by simp [nsmul_eq_mul]
    _ < 1 := hbudget

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ModuloIntervalMeasure
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.ModuloIntervalMeasure

open Set MeasureTheory
open scoped ENNReal

theorem integral_periodic_le_length_add_one {f : ℝ → ℝ}
    (hperiod : Function.Periodic f 1) (hf : ∀ x, 0 ≤ f x)
    (hint : IntervalIntegrable f volume 0 1) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, f x) ≤ (b - a + 1) * ∫ x in (0 : ℝ)..1, f x := by
  let n : ℕ := ⌈b - a⌉₊
  have hn : b ≤ a + n := by
    have := Nat.le_ceil (b - a)
    dsimp [n]
    linarith
  have hn' : (n : ℝ) ≤ b - a + 1 := by
    exact (Nat.ceil_lt_add_one (sub_nonneg.mpr hab)).le
  have hint' := hperiod.intervalIntegrable₀ (by norm_num : (1 : ℝ) ≠ 0) hint
  have hmass : 0 ≤ ∫ x in (0 : ℝ)..1, f x :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) hf
  calc
    (∫ x in a..b, f x) ≤ ∫ x in a..a + n, f x :=
      intervalIntegral.integral_mono_interval le_rfl hab hn
        (Filter.Eventually.of_forall hf) (hint' _ _)
    _ = (n : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
      have h := hperiod.intervalIntegral_add_zsmul_eq (n : ℤ) a hint'
      simpa only [zsmul_eq_mul, Int.cast_natCast, mul_one,
        hperiod.intervalIntegral_add_eq a 0, zero_add] using h
    _ ≤ (b - a + 1) * ∫ x in (0 : ℝ)..1, f x :=
      mul_le_mul_of_nonneg_right hn' hmass

theorem periodic_fract_indicator (s : Set ℝ) :
    Function.Periodic ((Int.fract ⁻¹' s).indicator (fun _ => (1 : ℝ))) 1 := by
  classical
  intro x
  change (if Int.fract (x + 1) ∈ s then (1 : ℝ) else 0) =
    (if Int.fract x ∈ s then 1 else 0)
  rw [Int.fract_add_one]

theorem intervalIntegrable_indicator_one {s : Set ℝ} (hs : MeasurableSet s)
    (a b : ℝ) : IntervalIntegrable (s.indicator (fun _ => (1 : ℝ))) volume a b := by
  exact ⟨(integrable_const (1 : ℝ)).indicator hs,
    (integrable_const (1 : ℝ)).indicator hs⟩

theorem integral_fract_indicator_one_period {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ x in (0 : ℝ)..1, (Int.fract ⁻¹' s).indicator (fun _ => (1 : ℝ)) x) =
      volume.real (s ∩ Ico 0 1) := by
  calc
    (∫ x in (0 : ℝ)..1, (Int.fract ⁻¹' s).indicator (fun _ => (1 : ℝ)) x) =
        ∫ x in (0 : ℝ)..1, s.indicator (fun _ => (1 : ℝ)) x := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      classical
      intro x hx
      have hfract := Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩
      change (if Int.fract x ∈ s then (1 : ℝ) else 0) =
        (if x ∈ s then 1 else 0)
      rw [hfract]
    _ = volume.real (s ∩ Ico 0 1) := by
      rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Ico_eq_integral_Ioc,
        integral_indicator_const 1 hs, measureReal_restrict_apply hs]
      simp

theorem volume_fract_preimage_inter_Ioc_le {s : Set ℝ} (hs : MeasurableSet s)
    {a b : ℝ} (hab : a ≤ b) :
    volume.real (Int.fract ⁻¹' s ∩ Ioc a b) ≤
      (b - a + 1) * volume.real (s ∩ Ico 0 1) := by
  have hs' : MeasurableSet (Int.fract ⁻¹' s) := hs.preimage measurable_fract
  have hnonneg : ∀ x, 0 ≤ (Int.fract ⁻¹' s).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have h := integral_periodic_le_length_add_one (periodic_fract_indicator s) hnonneg
    (intervalIntegrable_indicator_one hs' 0 1) hab
  rw [integral_fract_indicator_one_period hs, intervalIntegral.integral_of_le hab,
    integral_indicator_const 1 hs', measureReal_restrict_apply hs'] at h
  simpa only [smul_eq_mul, mul_one] using h

theorem cond_fract_preimage_le {s : Set ℝ} (hs : MeasurableSet s)
    {a b : ℝ} (hab : a < b) :
    (ProbabilityTheory.cond volume (Ioc a b)).real (Int.fract ⁻¹' s) ≤
      (1 + 1 / (b - a)) * volume.real (s ∩ Ico 0 1) := by
  have hr : 0 < b - a := sub_pos.mpr hab
  have h := mul_le_mul_of_nonneg_left
    (volume_fract_preimage_inter_Ioc_le hs hab.le) (inv_nonneg.mpr hr.le)
  rw [ProbabilityTheory.cond, measureReal_ennreal_smul_apply,
    measureReal_restrict_apply (hs.preimage measurable_fract),
    ENNReal.toReal_inv, Real.volume_Ioc, ENNReal.toReal_ofReal hr.le]
  calc
    _ ≤ (b - a)⁻¹ * ((b - a + 1) * volume.real (s ∩ Ico 0 1)) := h
    _ = (1 + 1 / (b - a)) * volume.real (s ∩ Ico 0 1) := by
      rw [← mul_assoc, mul_add, inv_mul_cancel₀ hr.ne', mul_one, one_div]

theorem threshold_miss_unit_volume_le {w : ℝ} (hw : 0 ≤ w) :
    volume.real ({u : ℝ | 1 - u ∉ Icc w (1 - w)} ∩ Ico 0 1) ≤ 2 * w := by
  have hsub : {u : ℝ | 1 - u ∉ Icc w (1 - w)} ∩ Ico 0 1 ⊆
      Ico 0 w ∪ Ioo (1 - w) 1 := by
    intro u hu
    rcases hu with ⟨hbad, hu0, hu1⟩
    by_cases huw : u < w
    · exact Or.inl ⟨hu0, huw⟩
    · right
      refine ⟨?_, hu1⟩
      by_contra h
      apply hbad
      constructor <;> linarith
  calc
    volume.real ({u : ℝ | 1 - u ∉ Icc w (1 - w)} ∩ Ico 0 1) ≤
        volume.real (Ico 0 w ∪ Ioo (1 - w) 1) := measureReal_mono hsub (measure_union_lt_top
          (by rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top)
          (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)).ne
    _ ≤ volume.real (Ico 0 w) + volume.real (Ioo (1 - w) 1) :=
      measureReal_union_le _ _
    _ = 2 * w := by
      rw [Real.volume_real_Ico_of_le hw, Real.volume_real_Ioo_of_le (by linarith)]
      ring

theorem cond_threshold_miss_le {a b w : ℝ} (hlen : (1 : ℝ) / 4 ≤ b - a)
    (hw : 0 ≤ w) :
    (ProbabilityTheory.cond volume (Ioc a b)).real
      {t : ℝ | 1 - Int.fract t ∉ Icc w (1 - w)} ≤ 10 * w := by
  have hab : a < b := by linarith
  have hs : MeasurableSet {u : ℝ | 1 - u ∉ Icc w (1 - w)} :=
    (measurableSet_Icc.preimage (measurable_const.sub measurable_id)).compl
  have h := cond_fract_preimage_le hs hab
  have hr : 0 < b - a := sub_pos.mpr hab
  have hfactor : 1 + 1 / (b - a) ≤ 5 := by
    have : 1 / (b - a) ≤ 4 := (div_le_iff₀ hr).mpr (by linarith)
    linarith
  change (ProbabilityTheory.cond volume (Ioc a b)).real (Int.fract ⁻¹'
    {u : ℝ | 1 - u ∉ Icc w (1 - w)}) ≤ 10 * w
  calc
    _ ≤ (1 + 1 / (b - a)) * volume.real
        ({u : ℝ | 1 - u ∉ Icc w (1 - w)} ∩ Ico 0 1) := h
    _ ≤ 5 * (2 * w) := mul_le_mul hfactor (threshold_miss_unit_volume_le hw)
      measureReal_nonneg (by norm_num)
    _ = 10 * w := by ring

theorem cond_Icc_eq_cond_Ioc (a b : ℝ) :
    ProbabilityTheory.cond volume (Icc a b) = ProbabilityTheory.cond volume (Ioc a b) := by
  simp only [ProbabilityTheory.cond, Real.volume_Icc, Real.volume_Ioc]
  rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume)).symm]

theorem cond_uIcc_mul_preimage (a b k : ℝ) (hk : k ≠ 0) (s : Set ℝ) :
    (ProbabilityTheory.cond volume (uIcc a b)).real ((k * ·) ⁻¹' s) =
      (ProbabilityTheory.cond volume (uIcc (k * a) (k * b))).real s := by
  have hpre : (k * ·) ⁻¹' uIcc (k * a) (k * b) = uIcc a b := by
    rw [preimage_const_mul_uIcc hk]
    field_simp
  have hbase : volume (uIcc a b) =
      ENNReal.ofReal |k⁻¹| * volume (uIcc (k * a) (k * b)) := by
    rw [← hpre, Real.volume_preimage_mul_left hk]
  have hinter : volume (uIcc a b ∩ (k * ·) ⁻¹' s) =
      ENNReal.ofReal |k⁻¹| * volume (uIcc (k * a) (k * b) ∩ s) := by
    rw [← hpre, ← preimage_inter, Real.volume_preimage_mul_left hk]
  simp only [measureReal_def, ProbabilityTheory.cond_apply measurableSet_uIcc,
    hbase, hinter, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (abs_nonneg k⁻¹), mul_inv_rev]
  have hscale : |k⁻¹| ≠ 0 := abs_ne_zero.mpr (inv_ne_zero hk)
  rw [mul_assoc, ← mul_assoc |k⁻¹|⁻¹, inv_mul_cancel₀ hscale, one_mul]

theorem cond_uIcc_threshold_miss_le {a b w : ℝ}
    (hlen : (1 : ℝ) / 4 ≤ |b - a|) (hw : 0 ≤ w) :
    (ProbabilityTheory.cond volume (uIcc a b)).real
      {t : ℝ | 1 - Int.fract t ∉ Icc w (1 - w)} ≤ 10 * w := by
  rw [uIcc, cond_Icc_eq_cond_Ioc]
  apply cond_threshold_miss_le _ hw
  simpa only [max_sub_min_eq_abs] using hlen

theorem uniform_angle_threshold_miss_le {N k w : ℝ} (hN : 0 < N)
    (hk : N / 4 ≤ |k|) (hw : 0 ≤ w) :
    (ProbabilityTheory.cond volume (Icc (1 / N) (2 / N))).real
      {θ : ℝ | 1 - Int.fract (k * θ) ∉ Icc w (1 - w)} ≤ 10 * w := by
  have hk0 : k ≠ 0 := by
    intro h
    simp only [h, abs_zero] at hk
    linarith
  have hab : (1 : ℝ) / N ≤ 2 / N := by
    apply div_le_div_of_nonneg_right (by norm_num) hN.le
  rw [← uIcc_of_le hab]
  change (ProbabilityTheory.cond volume (uIcc (1 / N) (2 / N))).real
    ((k * ·) ⁻¹' {t : ℝ | 1 - Int.fract t ∉ Icc w (1 - w)}) ≤ 10 * w
  rw [cond_uIcc_mul_preimage _ _ _ hk0]
  apply cond_uIcc_threshold_miss_le _ hw
  have hlength : |k * (2 / N) - k * (1 / N)| = |k| / N := by
    rw [← mul_sub, ← sub_div, show (2 : ℝ) - 1 = 1 by norm_num,
      mul_one_div, abs_div, abs_of_pos hN]
  rw [hlength]
  exact (le_div_iff₀ hN).mpr (by linarith)

end Invariant233.ModuloIntervalMeasure

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_PrescribedPhaseRealization
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
namespace PrescribedPhaseRealization

open Set

local notation "Circle" => AddCircle (1 : ℝ)

theorem dense_positive_orbit_tail {θ : ℝ} (hθ : Irrational θ) (N : ℕ) :
    DenseRange (fun n : ℕ => (n + N) • (θ : Circle)) := by
  have hz : DenseRange (fun n : ℤ => n • (θ : Circle)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hθ)
  have hn : DenseRange (fun n : ℕ => n • (θ : Circle)) :=
    denseRange_zsmul_iff_nsmul.mp hz
  have ht := (Homeomorph.addRight (N • (θ : Circle))).surjective.denseRange.comp
    hn (Homeomorph.addRight (N • (θ : Circle))).continuous
  change DenseRange (fun n : ℕ => n • (θ : Circle) + N • (θ : Circle)) at ht
  simpa only [add_nsmul] using ht

theorem exists_large_phase_in_interval {θ a b : ℝ} (hθ : Irrational θ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ a < Int.fract ((n : ℝ) * θ) ∧
      Int.fract ((n : ℝ) * θ) < b := by
  let s : Set Circle := (fun x : ℝ => (x : Circle)) '' Ioo a b
  have hsopen : IsOpen s := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hsnonempty : s.Nonempty := (nonempty_Ioo.mpr hab).image _
  obtain ⟨n, hn⟩ := (dense_positive_orbit_tail hθ N).exists_mem_open hsopen hsnonempty
  obtain ⟨z, hz, he⟩ := hn
  have hz01 : 0 ≤ z ∧ z < 1 := ⟨ha.trans hz.1.le, hz.2.trans_le hb⟩
  have he' : Int.fract z = Int.fract (((n + N : ℕ) : ℝ) * θ) := by
    have heq := congrArg (fun x : Circle => (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)) he
    simpa only [← AddCircle.coe_nsmul, nsmul_eq_mul,
      AddCircle.coe_equivIco_mk_apply, div_one, mul_one] using heq
  rw [Int.fract_eq_self.mpr hz01] at he'
  refine ⟨n + N, Nat.le_add_left N n, ?_⟩
  rw [← he']
  exact hz

theorem exists_large_divisible_phase {θ a b : ℝ} (hθ : Irrational θ)
    {q : ℕ} (hq : 0 < q) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ a < Int.fract (((q * n : ℕ) : ℝ) * θ) ∧
      Int.fract (((q * n : ℕ) : ℝ) * θ) < b := by
  obtain ⟨n, hn, hlo, hhi⟩ :=
    exists_large_phase_in_interval (hθ.natCast_mul hq.ne') ha hab hb N
  refine ⟨n, hn, ?_, ?_⟩
  · have he : ((q * n : ℕ) : ℝ) * θ = (n : ℝ) * ((q : ℝ) * θ) := by
      push_cast
      ring
    rw [he]
    exact hlo
  · have he : ((q * n : ℕ) : ℝ) * θ = (n : ℝ) * ((q : ℝ) * θ) := by
      push_cast
      ring
    rw [he]
    exact hhi

theorem exists_divisible_frequencies {θ : ℝ} (hθ : Irrational θ)
    (a b : ℕ → ℝ) (B : ℕ → ℕ)
    (ha : ∀ n, 0 ≤ a n) (hab : ∀ n, a n < b n) (hb : ∀ n, b n ≤ 1)
    {q₀ : ℕ} (hq₀ : 0 < q₀) :
    ∃ q : ℕ → ℕ, q 0 = q₀ ∧ (∀ n, 0 < q n) ∧
      ∀ n, q n ∣ q (n + 1) ∧ q n < q (n + 1) ∧
        B n * q n ≤ q (n + 1) ∧
        a n < Int.fract ((q (n + 1) : ℝ) * θ) ∧
        Int.fract ((q (n + 1) : ℝ) * θ) < b n := by
  classical
  let P := {q : ℕ // 0 < q}
  have hstep : ∀ n (q : P), ∃ q' : P,
      q.val ∣ q'.val ∧ q.val < q'.val ∧ B n * q.val ≤ q'.val ∧
        a n < Int.fract ((q'.val : ℝ) * θ) ∧
        Int.fract ((q'.val : ℝ) * θ) < b n := by
    intro n q
    obtain ⟨m, hm, hlo, hhi⟩ := exists_large_divisible_phase hθ q.property
      (ha n) (hab n) (hb n) (max (B n) 2)
    have hm₂ : 2 ≤ m := (le_max_right (B n) 2).trans hm
    have hmB : B n ≤ m := (le_max_left (B n) 2).trans hm
    refine ⟨⟨q.val * m, Nat.mul_pos q.property (by omega)⟩, ⟨m, rfl⟩, ?_, ?_, hlo, hhi⟩
    · change q.val < q.val * m
      nlinarith [q.property]
    · change B n * q.val ≤ q.val * m
      nlinarith
  let Q : ℕ → P := Nat.rec ⟨q₀, hq₀⟩ (fun n q => Classical.choose (hstep n q))
  refine ⟨fun n => (Q n).val, rfl, fun n => (Q n).property, ?_⟩
  intro n
  exact Classical.choose_spec (hstep n (Q n))

theorem exists_divisible_phase_approximation {θ : ℝ} (hθ : Irrational θ)
    (target ε : ℕ → ℝ) (B : ℕ → ℕ)
    (htarget₀ : ∀ n, 0 < target n) (htarget₁ : ∀ n, target n < 1) (hε : ∀ n, 0 < ε n)
    {q₀ : ℕ} (hq₀ : 0 < q₀) :
    ∃ q : ℕ → ℕ, q 0 = q₀ ∧ (∀ n, 0 < q n) ∧
      ∀ n, q n ∣ q (n + 1) ∧ q n < q (n + 1) ∧
        B n * q n ≤ q (n + 1) ∧
        |Int.fract ((q (n + 1) : ℝ) * θ) - target n| < ε n := by
  have ha : ∀ n, 0 ≤ max 0 (target n - ε n) := fun n => le_max_left _ _
  have hab : ∀ n, max 0 (target n - ε n) < min 1 (target n + ε n) := by
    intro n
    apply max_lt
    · apply lt_min
      · norm_num
      · linarith [htarget₀ n, hε n]
    · apply lt_min
      · linarith [htarget₁ n, hε n]
      · linarith [hε n]
  obtain ⟨q, hqzero, hqpos, hq⟩ := exists_divisible_frequencies hθ
    (fun n => max 0 (target n - ε n)) (fun n => min 1 (target n + ε n)) B
    ha hab (fun n => min_le_left _ _) hq₀
  refine ⟨q, hqzero, hqpos, ?_⟩
  intro n
  obtain ⟨hdiv, hlt, hbound, hlo, hhi⟩ := hq n
  refine ⟨hdiv, hlt, hbound, abs_lt.mpr ?_⟩
  constructor
  · have := lt_of_le_of_lt (le_max_right 0 (target n - ε n)) hlo
    linarith
  · have := lt_of_lt_of_le hhi (min_le_right 1 (target n + ε n))
    linarith

end PrescribedPhaseRealization
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_OrbitPartition
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233

open Set Function

theorem exists_finite_partition_of_nat_open_cover
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (U : ℕ → Set X) (hUopen : ∀ n, IsOpen (U n))
    (hcover : ∀ x, ∃ n, x ∈ U n) :
    ∃ H : ℕ, ∃ φ : ℕ → C(X, ℝ),
      (∀ n x, 0 ≤ φ n x) ∧
      (∀ x, ∑ n ∈ Finset.range (H + 1), φ n x = 1) ∧
      (∀ n, tsupport (φ n) ⊆ U n) ∧
      (∀ n, H < n → φ n = 0) := by
  classical
  obtain ⟨φ, hφsub⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U hUopen
    (by intro x _; simpa only [mem_iUnion] using hcover x)
  have hfinite : {n | (support (φ n)).Nonempty}.Finite :=
    φ.locallyFinite.finite_nonempty_of_compact
  let S := hfinite.toFinset
  let H := S.sup id
  have hindex : ∀ n x, φ n x ≠ 0 → n ≤ H := by
    intro n x hx
    apply Finset.le_sup (f := id)
    exact hfinite.mem_toFinset.mpr ⟨x, hx⟩
  refine ⟨H, fun n => φ n, φ.nonneg, ?_, hφsub, ?_⟩
  · intro x
    rw [← finsum_eq_sum_of_support_subset (fun n => φ n x)]
    · exact φ.sum_eq_one (mem_univ x)
    · intro n hn
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hindex n x hn))
  · intro n hn
    ext x
    by_contra hx
    exact (not_le_of_gt hn) (hindex n x hx)

theorem exists_finite_orbit_partition
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (σ : X → X) (hσ : Continuous σ)
    (hdense : ∀ x, DenseRange (fun n : ℕ => σ^[n] x))
    (O : Set X) (hO : IsOpen O) (hOne : O.Nonempty) :
    ∃ H : ℕ, ∃ φ : ℕ → C(X, ℝ),
      (∀ n x, 0 ≤ φ n x) ∧
      (∀ x, ∑ n ∈ Finset.range (H + 1), φ n x = 1) ∧
      (∀ n, σ^[n] '' tsupport (φ n) ⊆ O) ∧
      (∀ n, H < n → φ n = 0) := by
  obtain ⟨H, φ, hφpos, hφsum, hφsupport, hφzero⟩ :=
    exists_finite_partition_of_nat_open_cover (fun n => σ^[n] ⁻¹' O)
      (fun n => hO.preimage (hσ.iterate n))
      (fun x => (hdense x).exists_mem_open hO hOne)
  refine ⟨H, φ, hφpos, hφsum, ?_, hφzero⟩
  intro n y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hφsupport n hx

theorem exists_irrational_rotation_partition {θ : ℝ} (hθ : Irrational θ)
    (O : Set (AddCircle (1 : ℝ))) (hO : IsOpen O) (hOne : O.Nonempty) :
    ∃ H : ℕ, ∃ φ : ℕ → C(AddCircle (1 : ℝ), ℝ),
      (∀ n x, 0 ≤ φ n x) ∧
      (∀ x, ∑ n ∈ Finset.range (H + 1), φ n x = 1) ∧
      (∀ n, (fun x => x + n • (θ : AddCircle (1 : ℝ))) '' tsupport (φ n) ⊆ O) ∧
      (∀ n, H < n → φ n = 0) := by
  have hn : DenseRange (fun n : ℕ => n • (θ : AddCircle (1 : ℝ))) := by
    simpa only [Nat.add_zero] using
      PrescribedPhaseRealization.dense_positive_orbit_tail hθ 0
  have horbit : ∀ x : AddCircle (1 : ℝ),
      DenseRange (fun n : ℕ => (fun y => y + (θ : AddCircle (1 : ℝ)))^[n] x) := by
    intro x
    have hd := (Homeomorph.addLeft x).surjective.denseRange.comp hn
      (Homeomorph.addLeft x).continuous
    change DenseRange (fun n : ℕ => x + n • (θ : AddCircle (1 : ℝ))) at hd
    simpa only [add_right_iterate] using hd
  obtain ⟨H, φ, hφpos, hφsum, hφsupport, hφzero⟩ :=
    exists_finite_orbit_partition (fun x : AddCircle (1 : ℝ) => x + θ)
      (continuous_id.add continuous_const) horbit O hO hOne
  refine ⟨H, φ, hφpos, hφsum, ?_, hφzero⟩
  simpa only [add_right_iterate] using hφsupport

theorem exists_preparatory_partitions {θ : ℝ} (hθ : Irrational θ) :
    ∃ height : ℕ → ℕ, ∃ φ : ℕ → ℕ → C(AddCircle (1 : ℝ), ℝ),
      (∀ j n x, 0 ≤ φ j n x) ∧
      (∀ j x, ∑ n ∈ Finset.range (height j + 1), φ j n x = 1) ∧
      (∀ j, 1 ≤ j → ∀ n, ∀ x ∈ tsupport (φ j n),
        dist (x + (((n : ℝ) * θ : ℝ) : AddCircle (1 : ℝ))) 0 <
          1 / (10 * (j : ℝ))) ∧
      (∀ j n, height j < n → φ j n = 0) := by
  have hr : ∀ j : ℕ, 0 < (1 : ℝ) / (10 * ((j + 1 : ℕ) : ℝ)) := by
    intro j
    positivity
  choose H φ hnon hsum hsupport hzero using fun j : ℕ =>
    exists_irrational_rotation_partition hθ
      (Metric.ball 0 (1 / (10 * ((j + 1 : ℕ) : ℝ))))
      Metric.isOpen_ball ⟨0, Metric.mem_ball_self (hr j)⟩
  refine ⟨fun j => H (j - 1), fun j => φ (j - 1),
    (fun j => hnon (j - 1)), (fun j => hsum (j - 1)), ?_,
    (fun j => hzero (j - 1))⟩
  intro j hj n x hx
  have h := hsupport (j - 1) n ⟨x, hx, rfl⟩
  change dist (x + n • (θ : AddCircle (1 : ℝ))) 0 <
    1 / (10 * ((j - 1 + 1 : ℕ) : ℝ)) at h
  simpa only [Nat.sub_add_cancel hj, ← AddCircle.coe_nsmul, nsmul_eq_mul] using h

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_SeparatedPowers
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.SeparatedPowers

open Filter
open scoped Topology

theorem exists_separated_subset {α : Type*} (s : Finset α) (R : α → α → Prop) [DecidableRel R]
    (hSymm : ∀ ⦃x y⦄, R x y → R y x) (D : ℕ)
    (hdegree : ∀ x ∈ s, (s.filter (R x)).card ≤ D) :
    ∃ t : Finset α, t ⊆ s ∧ (t : Set α).Pairwise (fun x y => ¬ R x y) ∧
      s.card ≤ t.card * (D + 1) := by
  classical
  let T := s.powerset.filter (fun t : Finset α =>
    (t : Set α).Pairwise (fun x y => ¬ R x y))
  have hTempty : (∅ : Finset α) ∈ T := by simp [T]
  obtain ⟨t, ht, hmax⟩ := T.exists_max_image Finset.card ⟨∅, hTempty⟩
  have hsub : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
  have hpair : (t : Set α).Pairwise (fun x y => ¬ R x y) :=
    (Finset.mem_filter.mp ht).2
  have hcover : s ⊆ t.biUnion (fun y => insert y (s.filter (R y))) := by
    intro x hxs
    by_contra hxout
    have hxnot : x ∉ t := by
      intro hxt
      apply hxout
      exact Finset.mem_biUnion.mpr ⟨x, hxt, Finset.mem_insert_self _ _⟩
    have hbad : ∀ y ∈ t, ¬ R y x := by
      intro y hy hyx
      apply hxout
      exact Finset.mem_biUnion.mpr
        ⟨y, hy, Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hxs, hyx⟩)⟩
    have hnewpair : ((insert x t : Finset α) : Set α).Pairwise (fun a b => ¬ R a b) := by
      rw [Finset.coe_insert]
      apply hpair.insert
      intro y hy hxy
      exact ⟨fun h => hbad y hy (hSymm h), hbad y hy⟩
    have hnew : insert x t ∈ T := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr (Finset.insert_subset hxs hsub), hnewpair⟩
    have hc := hmax (insert x t) hnew
    rw [Finset.card_insert_of_notMem hxnot] at hc
    omega
  refine ⟨t, hsub, hpair, ?_⟩
  calc
    s.card ≤ (t.biUnion (fun y => insert y (s.filter (R y)))).card :=
      Finset.card_le_card hcover
    _ ≤ t.card * (D + 1) := by
      apply Finset.card_biUnion_le_card_mul
      intro y hy
      exact (Finset.card_insert_le y (s.filter (R y))).trans
        (Nat.add_le_add_right (hdegree y (hsub hy)) 1)

theorem power_gap_absorbs_polynomial {m C a b d : ℝ}
    (hm : 1 ≤ m) (hC : C ≤ m) (hgap : 1 + d ≤ (b - a) * m) :
    C * m ^ d * m ^ (a * m) ≤ m ^ (b * m) := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  calc
    C * m ^ d * m ^ (a * m) ≤ m * m ^ d * m ^ (a * m) := by
      gcongr
    _ = m ^ (1 + d + a * m) := by
      rw [Real.rpow_add hmpos, Real.rpow_add hmpos, Real.rpow_one]
    _ ≤ m ^ (b * m) :=
      Real.rpow_le_rpow_of_exponent_le hm (by linarith)

theorem eventually_power_gap {m : ℕ → ℝ} (hm : Tendsto m atTop atTop)
    (C a b d : ℝ) (hab : a < b) :
    ∀ᶠ n in atTop, C * m n ^ d * m n ^ (a * m n) ≤ m n ^ (b * m n) := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  filter_upwards [hm.eventually_ge_atTop 1, hm.eventually_ge_atTop C,
    hm.eventually_ge_atTop ((1 + d) / (b - a))] with n hn hC hd
  apply power_gap_absorbs_polynomial hn hC
  have := (div_le_iff₀ hgap).mp hd
  nlinarith

theorem card_small_affine_le (s : Finset ℤ) (a b : ℤ) (hb : b ≠ 0) (R : ℕ) :
    (s.filter (fun x => |a + b * x| ≤ (R : ℤ))).card ≤ 2 * R + 1 := by
  have hcard : (s.filter (fun x => |a + b * x| ≤ (R : ℤ))).card ≤
      (Finset.Icc (-(R : ℤ)) R).card := by
    apply Finset.card_le_card_of_injOn (fun x => a + b * x)
    · intro x hx
      exact Finset.mem_Icc.mpr (abs_le.mp (Finset.mem_filter.mp hx).2)
    · intro x hx y hy hxy
      exact mul_left_cancel₀ hb (add_left_cancel hxy)
  have hc : (Finset.Icc (-(R : ℤ)) R).card = 2 * R + 1 := by
    rw [Int.card_Icc]
    omega
  exact hc ▸ hcard

theorem exists_frequency_separated_subset (s : Finset ℤ) (H R : ℕ)
    (hs : ∀ n ∈ s, (R : ℤ) < n) :
    ∃ t : Finset ℤ, t ⊆ s ∧
      s.card ≤ t.card * ((2 * H + 1) ^ 2 * (2 * R + 1) + 1) ∧
      ∀ n ∈ t, ∀ n' ∈ t, n ≠ n' → ∀ v v' : ℤ,
        |v| ≤ (H : ℤ) → |v'| ≤ (H : ℤ) → (v ≠ 0 ∨ v' ≠ 0) →
        (R : ℤ) < |v * n + v' * n'| := by
  classical
  let I : Finset ℤ := Finset.Icc (-(H : ℤ)) H
  let F : Finset (ℤ × ℤ) := (I.product I).filter (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0)
  let Bad : ℤ → ℤ → Prop := fun n n' =>
    ∃ p ∈ F, |p.1 * n + p.2 * n'| ≤ (R : ℤ)
  have hsymm : ∀ ⦃n n'⦄, Bad n n' → Bad n' n := by
    intro n n' h
    obtain ⟨⟨v, v'⟩, hf, hsmall⟩ := h
    have hp := Finset.mem_filter.mp hf
    have hi := Finset.mem_product.mp hp.1
    refine ⟨(v', v), Finset.mem_filter.mpr ?_, ?_⟩
    · exact ⟨Finset.mem_product.mpr ⟨hi.2, hi.1⟩, hp.2.2, hp.2.1⟩
    · simpa only [add_comm] using hsmall
  have hFcard : F.card ≤ (2 * H + 1) ^ 2 := by
    have hI : I.card = 2 * H + 1 := by
      dsimp [I]
      rw [Int.card_Icc]
      omega
    calc
      F.card ≤ (I.product I).card := Finset.card_filter_le _ _
      _ = (2 * H + 1) ^ 2 := by
        change (I ×ˢ I).card = _
        rw [Finset.card_product, hI, pow_two]
  have hdegree : ∀ n ∈ s, (s.filter (Bad n)).card ≤
      (2 * H + 1) ^ 2 * (2 * R + 1) := by
    intro n hn
    have hcover : s.filter (Bad n) ⊆
        F.biUnion (fun p => s.filter (fun n' => |p.1 * n + p.2 * n'| ≤ (R : ℤ))) := by
      intro n' hn'
      obtain ⟨hns, p, hp, hsmall⟩ := Finset.mem_filter.mp hn'
      exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hns, hsmall⟩⟩
    calc
      (s.filter (Bad n)).card ≤
          (F.biUnion (fun p => s.filter (fun n' => |p.1 * n + p.2 * n'| ≤ (R : ℤ)))).card :=
        Finset.card_le_card hcover
      _ ≤ F.card * (2 * R + 1) := by
        apply Finset.card_biUnion_le_card_mul
        intro p hp
        exact card_small_affine_le s (p.1 * n) p.2 (Finset.mem_filter.mp hp).2.2 R
      _ ≤ (2 * H + 1) ^ 2 * (2 * R + 1) := Nat.mul_le_mul_right _ hFcard
  obtain ⟨t, hts, hpair, hcard⟩ :=
    exists_separated_subset s Bad hsymm ((2 * H + 1) ^ 2 * (2 * R + 1)) hdegree
  refine ⟨t, hts, hcard, ?_⟩
  intro n hn n' hn' hne v v' hv hv' hnonzero
  have hnR := hs n (hts hn)
  have hnR' := hs n' (hts hn')
  have hn0 : 0 ≤ n := by omega
  have hn0' : 0 ≤ n' := by omega
  by_cases hv0 : v = 0
  · have hvn : v' ≠ 0 := hnonzero.resolve_left (not_not.mpr hv0)
    have hmul := mul_le_mul_of_nonneg_right (Int.one_le_abs hvn) hn0'
    rw [one_mul] at hmul
    simpa only [hv0, zero_mul, zero_add, abs_mul, abs_of_nonneg hn0'] using hnR'.trans_le hmul
  by_cases hv0' : v' = 0
  · have hmul := mul_le_mul_of_nonneg_right (Int.one_le_abs hv0) hn0
    rw [one_mul] at hmul
    simpa only [hv0', zero_mul, add_zero, abs_mul, abs_of_nonneg hn0] using hnR.trans_le hmul
  apply lt_of_not_ge
  intro hsmall
  apply hpair hn hn' hne
  refine ⟨(v, v'), Finset.mem_filter.mpr ?_, hsmall⟩
  exact ⟨Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr (abs_le.mp hv), Finset.mem_Icc.mpr (abs_le.mp hv')⟩,
    hv0, hv0'⟩

theorem deletion_budget_le {m N : ℕ} (hm : 1 ≤ m) (hN : N ≤ m ^ 2) :
    (2 * m ^ 300 + 1) ^ 2 * (2 * (N * m ^ 1000) + 1) + 1 ≤
      28 * m ^ 1602 := by
  have h300 : 1 ≤ m ^ 300 := one_le_pow₀ hm
  have h1002 : 1 ≤ m ^ 1002 := one_le_pow₀ hm
  have h1602 : 1 ≤ m ^ 1602 := one_le_pow₀ hm
  have hR : N * m ^ 1000 ≤ m ^ 1002 := by
    calc
      N * m ^ 1000 ≤ m ^ 2 * m ^ 1000 := Nat.mul_le_mul_right _ hN
      _ = m ^ 1002 := by rw [← pow_add]
  have hH : 2 * m ^ 300 + 1 ≤ 3 * m ^ 300 := by omega
  have hR' : 2 * (N * m ^ 1000) + 1 ≤ 3 * m ^ 1002 := by omega
  calc
    (2 * m ^ 300 + 1) ^ 2 * (2 * (N * m ^ 1000) + 1) + 1 ≤
        (3 * m ^ 300) ^ 2 * (3 * m ^ 1002) + 1 := by gcongr
    _ = 27 * m ^ 1602 + 1 := by
      simp only [mul_pow, ← pow_mul]
      ring_nf
    _ ≤ 28 * m ^ 1602 := by omega

theorem exists_frequency_separated_nat_subset (s : Finset ℕ) (H R : ℕ)
    (hs : ∀ n ∈ s, R < n) :
    ∃ t : Finset ℕ, t ⊆ s ∧
      s.card ≤ t.card * ((2 * H + 1) ^ 2 * (2 * R + 1) + 1) ∧
      ∀ n ∈ t, ∀ n' ∈ t, n ≠ n' → ∀ v v' : ℤ,
        |v| ≤ (H : ℤ) → |v'| ≤ (H : ℤ) → (v ≠ 0 ∨ v' ≠ 0) →
        (R : ℤ) < |v * (n : ℤ) + v' * (n' : ℤ)| := by
  classical
  obtain ⟨u, hus, hcard, hsep⟩ :=
    exists_frequency_separated_subset (s.image (fun n : ℕ => (n : ℤ))) H R (by
      intro n hn
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
      exact_mod_cast hs k hk)
  have hnonneg : ∀ n ∈ u, 0 ≤ n := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (hus hn)
    exact Int.natCast_nonneg k
  have hcast : ∀ n ∈ u, (n.toNat : ℤ) = n :=
    fun n hn => Int.toNat_of_nonneg (hnonneg n hn)
  have hcardu : (u.image Int.toNat).card = u.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have h := congrArg (fun n : ℕ => (n : ℤ)) hab
    simpa only [hcast a ha, hcast b hb] using h
  have hcards : (s.image (fun n : ℕ => (n : ℤ))).card = s.card :=
    Finset.card_image_of_injective _ (by intro a b h; change (a : ℤ) = (b : ℤ) at h; omega)
  refine ⟨u.image Int.toNat, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (hus hz)
    simpa using hk
  · simpa only [hcardu, hcards] using hcard
  · intro n hn n' hn' hne v v' hv hv' hvv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hn'
    have hzz : z ≠ z' := by intro h; exact hne (congrArg Int.toNat h)
    simpa only [hcast z hz, hcast z' hz'] using hsep z hz z' hz' hzz v v' hv hv' hvv

theorem eventually_select_from_supply (c : ℝ) (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, N ≤ m ^ 2 → ∀ s : Finset ℕ,
      (∀ n ∈ s, N * m ^ 1000 < n) →
      c * (m : ℝ) ^ ((7 / 10 : ℝ) * m) ≤ (s.card : ℝ) →
      ∃ t : Finset ℕ, t ⊆ s ∧
        (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (t.card : ℝ) ∧
        ∀ n ∈ t, ∀ n' ∈ t, n ≠ n' → ∀ v v' : ℤ,
          |v| ≤ (m ^ 300 : ℕ) → |v'| ≤ (m ^ 300 : ℕ) →
          (v ≠ 0 ∨ v' ≠ 0) →
          (N * m ^ 1000 : ℕ) < |v * (n : ℤ) + v' * (n' : ℤ)| := by
  have hm : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hgap := eventually_power_gap hm (28 / c) (69 / 100) (7 / 10) 1602 (by norm_num)
  filter_upwards [hgap, eventually_ge_atTop 1] with m hgap hmone
  intro N hN s hs hsize
  obtain ⟨t, hts, hcard, hsep⟩ :=
    exists_frequency_separated_nat_subset s (m ^ 300) (N * m ^ 1000) hs
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hbudget : (((2 * m ^ 300 + 1) ^ 2 * (2 * (N * m ^ 1000) + 1) + 1 : ℕ) : ℝ) ≤
      28 * (m : ℝ) ^ (1602 : ℝ) := by
    rw [show (1602 : ℝ) = ((1602 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact_mod_cast deletion_budget_le hmone hN
  have hcardreal : (s.card : ℝ) ≤ (t.card : ℝ) *
      (((2 * m ^ 300 + 1) ^ 2 * (2 * (N * m ^ 1000) + 1) + 1 : ℕ) : ℝ) :=
    by exact_mod_cast hcard
  have hlower : 28 * (m : ℝ) ^ (1602 : ℝ) *
      (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (s.card : ℝ) := by
    calc
      _ = c * ((28 / c) * (m : ℝ) ^ (1602 : ℝ) *
          (m : ℝ) ^ ((69 / 100 : ℝ) * m)) := by field_simp
      _ ≤ c * (m : ℝ) ^ ((7 / 10 : ℝ) * m) := mul_le_mul_of_nonneg_left hgap hc.le
      _ ≤ (s.card : ℝ) := hsize
  refine ⟨t, hts, ?_, hsep⟩
  have hp : 0 < 28 * (m : ℝ) ^ (1602 : ℝ) := by positivity
  apply le_of_mul_le_mul_left _ hp
  calc
    _ ≤ (s.card : ℝ) := hlower
    _ ≤ (t.card : ℝ) * (28 * (m : ℝ) ^ (1602 : ℝ)) :=
      hcardreal.trans (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg t.card))
    _ = _ := by ring

end Invariant233.SeparatedPowers

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_WeakConvergenceAEContinuous
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.WeakConvergenceAEContinuous

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

theorem tendsto_map_of_ae_continuous
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {μs : ℕ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) {f : X → Y} (hf : Measurable f)
    (hc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt f x) :
    Tendsto (fun j => (μs j).map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) atTop
      (𝓝 (μ.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))) := by
  apply tendsto_of_forall_isClosed_limsup_le'
  intro F hF
  have heq : (μ : Measure X) (closure (f ⁻¹' F)) = (μ : Measure X) (f ⁻¹' F) := by
    apply measure_congr
    filter_upwards [hc] with x hx
    apply propext
    constructor
    · intro h
      have hfreq : ∃ᶠ y in 𝓝 x, f y ∈ F := mem_closure_iff_frequently.mp h
      exact hF.mem_of_frequently_of_tendsto hfreq hx
    · intro h
      exact subset_closure h
  simp only [ProbabilityMeasure.map, ProbabilityMeasure.coe_mk,
    Measure.map_apply hf hF.measurableSet]
  calc
    limsup (fun j => (μs j : Measure X) (f ⁻¹' F)) atTop ≤
        limsup (fun j => (μs j : Measure X) (closure (f ⁻¹' F))) atTop :=
      limsup_le_limsup (Eventually.of_forall (fun _ => measure_mono subset_closure))
    _ ≤ (μ : Measure X) (closure (f ⁻¹' F)) :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_closure
    _ = (μ : Measure X) (f ⁻¹' F) := heq

theorem tendsto_integral_of_ae_continuous
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {μs : ℕ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) {f : X → ℝ} (hf : Measurable f)
    (hc : ∀ᵐ x ∂(μ : Measure X), ContinuousAt f x)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) :
    Tendsto (fun j => ∫ x, f x ∂(μs j : Measure X)) atTop
      (𝓝 (∫ x, f x ∂(μ : Measure X))) := by
  let g : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => max (-B) (min B x)) (by fun_prop) B (fun x => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩)
  have hgf : ∀ x, g (f x) = f x := by
    intro x
    change max (-B) (min B (f x)) = f x
    rw [min_eq_right (abs_le.mp (hb x)).2, max_eq_right (abs_le.mp (hb x)).1]
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_map_of_ae_continuous hμ hf hc)) g
  have hmap (ν : ProbabilityMeasure X) :
      (∫ y, g y ∂(ν.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure ℝ)) = ∫ x, f x ∂(ν : Measure X) := by
    change (∫ y, g y ∂Measure.map f (ν : Measure X)) = _
    rw [integral_map hf.aemeasurable g.continuous.aestronglyMeasurable]
    simp only [hgf]
  simpa only [hmap] using h

end Invariant233.WeakConvergenceAEContinuous

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_IndependentAngles
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace InvariantProjection.IndependentAngles

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem intervalLaw_isProbabilityMeasure {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Icc a b)) := by
  apply cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

theorem intervalLaw_nullSingletonClass (a b : ℝ) :
    NullSingletonClass (ProbabilityTheory.cond volume (Set.Icc a b)) := by
  constructor
  intro x
  exact ProbabilityTheory.cond_absolutelyContinuous (measure_singleton x)

end InvariantProjection.IndependentAngles

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_IndependentMissBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem measure_many_independent_events_le
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : ι → Set Ω) (hE : iIndepSet E μ) (s : Finset ι)
    {p : ℝ≥0∞} (hp : p ≤ 1) (hprob : ∀ i ∈ s, μ (E i) ≤ p) (q : ℝ) :
    μ {ω | ∃ t : Finset ι, t ⊆ s ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, ω ∈ E i} ≤
      (2 : ℝ≥0∞) ^ s.card * p ^ q := by
  classical
  let F := s.powerset.filter (fun t => q ≤ (t.card : ℝ))
  have hset : {ω | ∃ t : Finset ι, t ⊆ s ∧ q ≤ (t.card : ℝ) ∧
      ∀ i ∈ t, ω ∈ E i} = ⋃ t ∈ F, ⋂ i ∈ t, E i := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, F,
      Finset.mem_filter, Finset.mem_powerset]
    aesop
  have hFcard : F.card ≤ 2 ^ s.card := by
    calc
      F.card ≤ s.powerset.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 ^ s.card := Finset.card_powerset s
  rw [hset]
  calc
    μ (⋃ t ∈ F, ⋂ i ∈ t, E i) ≤ ∑ t ∈ F, μ (⋂ i ∈ t, E i) :=
      measure_biUnion_finset_le F _
    _ ≤ ∑ t ∈ F, p ^ q := by
      apply Finset.sum_le_sum
      intro t ht
      have ht' : t ⊆ s ∧ q ≤ (t.card : ℝ) := by
        simpa only [F, Finset.mem_filter, Finset.mem_powerset] using ht
      rw [hE.meas_biInter t]
      calc
        ∏ i ∈ t, μ (E i) ≤ ∏ _i ∈ t, p :=
          Finset.prod_le_prod' (fun i hi => hprob i (ht'.1 hi))
        _ = p ^ t.card := by simp
        _ = p ^ (t.card : ℝ) := (ENNReal.rpow_natCast p t.card).symm
        _ ≤ p ^ q := ENNReal.rpow_le_rpow_of_exponent_ge hp ht'.2
    _ = (F.card : ℝ≥0∞) * p ^ q := by simp [nsmul_eq_mul]
    _ ≤ (2 : ℝ≥0∞) ^ s.card * p ^ q := by
      apply mul_le_mul_left
      exact_mod_cast hFcard

theorem measure_exists_many_independent_events_le
    {Ω ι κ : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : κ → ι → Set Ω) (s : Finset ι) (powers : Finset κ)
    (hE : ∀ k ∈ powers, iIndepSet (E k) μ)
    {p : ℝ≥0∞} (hp : p ≤ 1)
    (hprob : ∀ k ∈ powers, ∀ i ∈ s, μ (E k i) ≤ p) (q : ℝ) :
    μ {ω | ∃ k ∈ powers, ∃ t : Finset ι,
      t ⊆ s ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, ω ∈ E k i} ≤
      (powers.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ s.card * p ^ q) := by
  classical
  have hset : {ω | ∃ k ∈ powers, ∃ t : Finset ι,
      t ⊆ s ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, ω ∈ E k i} =
      ⋃ k ∈ powers, {ω | ∃ t : Finset ι,
        t ⊆ s ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, ω ∈ E k i} := by
    ext ω
    simp
  rw [hset]
  calc
    _ ≤ ∑ k ∈ powers, μ {ω | ∃ t : Finset ι,
        t ⊆ s ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, ω ∈ E k i} :=
      measure_biUnion_finset_le powers _
    _ ≤ ∑ _k ∈ powers, (2 : ℝ≥0∞) ^ s.card * p ^ q := by
      apply Finset.sum_le_sum
      intro k hk
      exact measure_many_independent_events_le μ (E k) (hE k hk) s hp
        (hprob k hk) q
    _ = _ := by simp [nsmul_eq_mul]

theorem exists_many_misses_of_few_successes {ι : Type*} (s : Finset ι)
    (good : ι → Prop) [DecidablePred good]
    (hgood : ((s.filter good).card : ℝ) < (s.card : ℝ) / 20) :
    ∃ t : Finset ι, t ⊆ s ∧ (19 / 20 : ℝ) * s.card < (t.card : ℝ) ∧
      ∀ i ∈ t, ¬ good i := by
  classical
  refine ⟨s.filter (fun i => ¬ good i), Finset.filter_subset _ _, ?_, ?_⟩
  · have hcard := Finset.card_filter_add_card_filter_not (s := s) good
    have hcardR : ((s.filter good).card : ℝ) +
        ((s.filter (fun i => ¬ good i)).card : ℝ) = s.card := by
      exact_mod_cast hcard
    linarith
  · intro i hi
    exact (Finset.mem_filter.mp hi).2

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_PhaseRanges
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233

theorem threshold_mem_Icc_of_abs_bounds {a x : ℝ}
    (ha : 0 < a) (hlo : a ≤ |x|) (hhi : |x| ≤ 1 / 2) :
    1 - Int.fract x ∈ Set.Icc a (1 - a) := by
  rcases le_or_gt 0 x with hx | hx
  · have habs : |x| = x := abs_of_nonneg hx
    have hfract : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx, by linarith⟩
    rw [hfract]
    constructor <;> linarith
  · have habs : |x| = -x := abs_of_neg hx
    have hfract : Int.fract (-x) = -x :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hnz : Int.fract (-x) ≠ 0 := by rw [hfract]; linarith
    have heq := Int.fract_neg hnz
    simp only [neg_neg] at heq
    rw [heq, hfract]
    constructor <;> linarith

theorem phase_small_window {m K G α k : ℝ}
    (hm : 0 < m) (hK : 0 < K) (hG : 0 < G)
    (hαlo : 1 / (m * K) ≤ α) (hαhi : α ≤ 2 / (m * K))
    (hklo : G * K ≤ |k|) (hkhi : |k| ≤ m * K / 4) :
    1 - Int.fract (k * α) ∈ Set.Icc (G / m) (1 - G / m) := by
  have hmK : 0 < m * K := mul_pos hm hK
  have hα : 0 < α := lt_of_lt_of_le (one_div_pos.mpr hmK) hαlo
  have hlo' : G / m ≤ |k| * α := by
    calc
      G / m = (G * K) * (1 / (m * K)) := by field_simp
      _ ≤ |k| * α := mul_le_mul hklo hαlo (le_of_lt (one_div_pos.mpr hmK))
        (abs_nonneg k)
  have hhi' : |k| * α ≤ 1 / 2 := by
    calc
      |k| * α ≤ (m * K / 4) * (2 / (m * K)) :=
        mul_le_mul hkhi hαhi (le_of_lt hα) (by positivity)
      _ = 1 / 2 := by field_simp <;> ring
  apply threshold_mem_Icc_of_abs_bounds (div_pos hG hm)
  · simpa only [abs_mul, abs_of_pos hα] using hlo'
  · simpa only [abs_mul, abs_of_pos hα] using hhi'

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleParameterRecursion
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.average_eq_trialAverage _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Invariant233.CircleParameterRecursion
open PrescribedPhaseRealization SamplingHorizon FiniteWindow

private theorem global_agree {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (n i : ℕ) (hi : i ≤ (states hs height n).d) :
    globalFrequency hs height i = (states hs height n).q i :=
  (Classical.choose_spec (exists_global_frequency hs height)).1 n i hi

private theorem global_block {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (n i : ℕ) (hi : i ≤ (choices hs height n).m) :
    globalFrequency hs height ((states hs height n).d + i) =
      (choices hs height n).sampling.q i := by
  rw [global_agree hs height (n + 1) _ (by rw [states_d_succ]; omega)]
  exact spliceFrequency_add _ _ _ _ (choices hs height n).sampling.q_zero

private theorem blockEnd_eq {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n : ℕ) :
    (constructed hs height φ).blockEnd n = (states hs height n).d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [CircleParameterData.blockEnd_succ, ih, states_d_succ]
    simp [constructed]

private theorem cost_eq {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n : ℕ) :
    (states hs height n).cost =
      ∑ j ∈ Finset.Icc 1 n, (constructed hs height φ).C j * (constructed hs height φ).m j := by
  induction n with
  | zero => simp [states, initial]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih]
    rfl

private theorem block_mem {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n i : ℕ) :
    i ∈ (constructed hs height φ).block (n + 1) ↔
      (states hs height n).d < i ∧ i ≤ (states hs height n).d + (choices hs height n).m := by
  rw [CircleParameterData.mem_block_iff]
  simp only [Nat.add_sub_cancel, blockEnd_eq, states_d_succ]

private theorem coefficientBound_eq {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n : ℕ) :
    (constructed hs height φ).coefficientBound (n + 1) =
      Real.exp ((((states hs height n).K : ℝ) + 1) * (states hs height n).cost) := by
  simp only [CircleParameterData.coefficientBound, Nat.add_sub_cancel]
  rw [← cost_eq hs height φ n]
  rfl

private theorem sample_index_bound {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n r : ℕ) :
    r < (constructed hs height φ).q ((constructed hs height φ).blockEnd n) ↔
      r < (states hs height n).q (states hs height n).d := by
  rw [blockEnd_eq]
  change r < globalFrequency hs height (states hs height n).d ↔ _
  rw [global_agree hs height n _ le_rfl]

private theorem samples_eq {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n r : ℕ)
    (hr : r < (states hs height n).q (states hs height n).d) :
    (constructed hs height φ).samples (n + 1) r =
      (choices hs height n).sampling.samples ⟨r, hr⟩ := by
  simp [constructed, hr]

private theorem alpha_block {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n : ℕ)
    (i : Fin (choices hs height n).m) :
    (constructed hs height φ).alpha θ ((states hs height n).d + (i.val + 1)) =
      Int.fract (((choices hs height n).sampling.q (i.val + 1) : ℝ) * θ) := by
  unfold CircleParameterData.alpha
  change Int.fract ((globalFrequency hs height _ : ℝ) * θ) = _
  rw [global_block hs height n _ (by have := i.isLt; omega)]

private theorem constructed_phases {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n i : ℕ)
    (hi : i ∈ (constructed hs height φ).block (n + 1)) :
    1 / (constructed hs height φ).N (n + 1) < (constructed hs height φ).alpha θ i ∧
      (constructed hs height φ).alpha θ i < 2 / (constructed hs height φ).N (n + 1) := by
  have hmem := (block_mem hs height φ n i).mp hi
  let r : Fin (choices hs height n).m := ⟨i - (states hs height n).d - 1, by omega⟩
  have heq : (states hs height n).d + (r.val + 1) = i := by dsimp [r]; omega
  have hphase := (choices hs height n).sampling.phases r
  rw [← alpha_block hs height φ n r, heq] at hphase
  exact hphase

private theorem convolution_eq_supported (K : ℕ) (A B : ℤ → ℂ)
    (hB : Function.support B ⊆ Set.Icc (-(K : ℤ)) (K : ℤ)) (n : ℕ) :
    CircleParameterData.convolutionCoefficient K A B (-(n : ℤ)) =
      convolution K A B n := by
  classical
  unfold CircleParameterData.convolutionCoefficient FiniteWindow.convolution
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : |(n : ℤ) + i| ≤ (K : ℤ)
  · simp [hi]
  · simp only [hi, ite_false, if_false]
    have hzero : B (-(n : ℤ) - i) = 0 := by
      by_contra hne
      have hmem := hB (Function.mem_support.mpr hne)
      have ha : |-(n : ℤ) - i| ≤ (K : ℤ) := abs_le.mpr hmem
      have heq : -(n : ℤ) - i = -((n : ℤ) + i) := by ring
      rw [heq, abs_neg] at ha
      exact hi ha
    simp [hzero]

private theorem constructed_ratios {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n i : ℕ)
    (hi : i ∈ (constructed hs height φ).block (n + 1)) :
    (constructed hs height φ).N (n + 1) ≤
      ((constructed hs height φ).q (i + 1) : ℝ) / (constructed hs height φ).q i := by
  have hmem := (block_mem hs height φ n i).mp hi
  by_cases hlt : i < (states hs height n).d + (choices hs height n).m
  · let r := i - (states hs height n).d
    have hr : r < (choices hs height n).m := by dsimp [r]; omega
    have heq : (states hs height n).d + r = i := by dsimp [r]; omega
    have hq0 := global_block hs height n r hr.le
    have hq1 := global_block hs height n (r + 1) (by omega)
    rw [heq] at hq0
    rw [← Nat.add_assoc, heq] at hq1
    change ((choices hs height n).m : ℝ) * (states hs height n).K ≤
      (globalFrequency hs height (i + 1) : ℝ) / globalFrequency hs height i
    rw [hq0, hq1]
    exact (le_max_right _ _).trans ((choices hs height n).sampling.q_ratio r hr)
  · have heq : i = (states hs height (n + 1)).d := by
      rw [states_d_succ]
      omega
    have hm : 0 < (choices hs height (n + 1)).m := by
      have := (choices hs height (n + 1)).m_large
      omega
    have hq0 := global_block hs height (n + 1) 0 (Nat.zero_le _)
    have hq1 := global_block hs height (n + 1) 1 hm
    simp only [Nat.add_zero, ← heq] at hq0 hq1
    change ((choices hs height n).m : ℝ) * (states hs height n).K ≤
      (globalFrequency hs height (i + 1) : ℝ) / globalFrequency hs height i
    rw [hq0, hq1]
    exact (le_max_left _ _).trans ((choices hs height (n + 1)).sampling.q_ratio 0 hm)

private theorem constructed_spread {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n : ℕ) (k : ℤ)
    (hlo : (constructed hs height φ).N (n + 1) / 4 ≤ |(k : ℝ)|)
    (hhi : |(k : ℝ)| ≤ ((constructed hs height φ).m (n + 1) : ℝ) ^
      ((4 / 5 : ℝ) * (constructed hs height φ).m (n + 1))) :
    ((constructed hs height φ).m (n + 1) : ℝ) / 20 ≤
      (((constructed hs height φ).block (n + 1)).filter (fun i =>
        1 - Int.fract ((k : ℝ) * (constructed hs height φ).alpha θ i) ∈
          Set.Icc ((constructed hs height φ).b (n + 1))
            (1 - (constructed hs height φ).b (n + 1)))).card := by
  classical
  have hspread := (choices hs height n).sampling.spread k hlo
    (by simpa [constructed] using hhi)
  simp only [Finset.card_univ, Fintype.card_fin, ProductPhases.strictPhaseGoodCount] at hspread
  let f : Fin (choices hs height n).m → ℕ := fun r => (states hs height n).d + (r.val + 1)
  have hcard :
      (Finset.univ.filter (fun r : Fin (choices hs height n).m =>
        1 - Int.fract ((k : ℝ) * Int.fract
          (((choices hs height n).sampling.q (r.val + 1) : ℝ) * θ)) ∈
            Set.Ioo (((choices hs height n).m : ℝ) ^ (-19 / 20 : ℝ))
              (1 - ((choices hs height n).m : ℝ) ^ (-19 / 20 : ℝ)))).card ≤
      (((constructed hs height φ).block (n + 1)).filter (fun i =>
        1 - Int.fract ((k : ℝ) * (constructed hs height φ).alpha θ i) ∈
          Set.Icc ((constructed hs height φ).b (n + 1))
            (1 - (constructed hs height φ).b (n + 1)))).card := by
    apply Finset.card_le_card_of_injOn f
    · intro r hr
      obtain ⟨_, hr⟩ := Finset.mem_filter.mp hr
      apply Finset.mem_filter.mpr
      constructor
      · apply (block_mem hs height φ n (f r)).mpr
        dsimp [f]
        have := r.isLt
        omega
      · change 1 - Int.fract ((k : ℝ) * (constructed hs height φ).alpha θ
            ((states hs height n).d + (r.val + 1))) ∈ _
        rw [alpha_block]
        have hneg : (-19 / 20 : ℝ) = -(19 / 20 : ℝ) := by norm_num
        rw [hneg] at hr
        exact ⟨hr.1.le, hr.2.le⟩
    · intro r _ s _ hrs
      apply Fin.ext
      dsimp [f] at hrs
      omega
  exact hspread.trans (by exact_mod_cast hcard)

private theorem prod_constructed_block {A : Type*} [CommMonoid A]
    {θ : ℝ} (hs : CircleStageSupply θ) (height : ℕ → ℕ)
    (φ : ℕ → ℕ → C(Circle, ℝ)) (n : ℕ) (f : ℕ → A) :
    (∏ i ∈ (constructed hs height φ).block (n + 1), f i) =
      ∏ r : Fin (choices hs height n).m, f ((states hs height n).d + (r.val + 1)) := by
  classical
  symm
  apply Finset.prod_bij (fun r _ => (states hs height n).d + (r.val + 1))
  · intro r _
    apply (block_mem hs height φ n _).mpr
    have := r.isLt
    omega
  · intro r _ s _ hrs
    apply Fin.ext
    omega
  · intro i hi
    have hmem := (block_mem hs height φ n i).mp hi
    refine ⟨⟨i - (states hs height n).d - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only
    omega
  · intro r _
    rfl

private theorem samplingAverage_eq {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n r : ℕ)
    (hr : r < (states hs height n).q (states hs height n).d)
    (endpoint : Bool) (x : Circle) :
    (constructed hs height φ).samplingAverage θ (n + 1) r endpoint x =
      TrialSampling.average (choices hs height n).m
        ((choices hs height n).sampling.samples ⟨r, hr⟩) endpoint
        (fun i : Fin (choices hs height n).m =>
          Int.fract (((choices hs height n).sampling.q (i.val + 1) : ℝ) * θ))
        (fun i : Fin (choices hs height n).m =>
          ((choices hs height n).sampling.q (i.val + 1) : ℤ) • x) := by
  unfold CircleParameterData.samplingAverage TrialSampling.average
  rw [samples_eq hs height φ n r hr, one_div]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [prod_constructed_block]
  apply Finset.prod_congr rfl
  intro i _
  rw [alpha_block]
  congr 2
  unfold CircleParameterData.coordinate
  change CircleParameterData.rep (globalFrequency hs height
    ((states hs height n).d + (i.val + 1)) • x) = _
  rw [global_block hs height n _ (by have := i.isLt; omega)]
  simp

private theorem shift_eq {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n r : ℕ) :
    (constructed hs height φ).shift (n + 1) r =
      (r : ℝ) / (states hs height n).q (states hs height n).d := by
  unfold CircleParameterData.shift
  simp only [Nat.add_sub_cancel, blockEnd_eq]
  change (r : ℝ) / globalFrequency hs height (states hs height n).d = _
  rw [global_agree hs height n _ le_rfl]

private theorem ell_eq {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ)) (n : ℕ) :
    (constructed hs height φ).ell (n + 1) =
      1 / (((n + 2 : ℕ) : ℝ) ^ 2 * (1 + ((states hs height n).d : ℝ)) *
        (states hs height n).q (states hs height n).d) := by
  unfold CircleParameterData.ell
  simp only [Nat.add_sub_cancel, blockEnd_eq]
  change 1 / (((n + 2 : ℕ) : ℝ) ^ 2 * (1 + ((states hs height n).d : ℝ)) *
    globalFrequency hs height (states hs height n).d) = _
  rw [global_agree hs height n _ le_rfl]

private theorem constructed_laws {θ : ℝ} (hs : CircleStageSupply θ)
    (height : ℕ → ℕ) (φ : ℕ → ℕ → C(Circle, ℝ))
    (hφnonneg : ∀ j n x, 0 ≤ φ j n x)
    (hφsum : ∀ j x, ∑ n ∈ Finset.range (height j + 1), φ j n x = 1)
    (hφsupport : ∀ j, 1 ≤ j → ∀ n, ∀ x ∈ tsupport (φ j n),
      dist (x + (((n : ℝ) * θ : ℝ) : Circle)) 0 < 1 / (10 * (j : ℝ))) :
    CircleParameterLaws θ (constructed hs height φ) := by
  have hmpos (n : ℕ) : 0 < (choices hs height n).m := by
    have := (choices hs height n).m_large
    omega
  have hLmono : Monotone (fun n => (choices hs height n).L) := by
    apply monotone_nat_of_le_succ
    intro n
    exact (choices hs height (n + 1)).L_previous
  have globalSpec := Classical.choose_spec (exists_global_frequency hs height)
  refine {
    m_pos := ?_
    K_pos := ?_
    G_pos := ?_
    q_pos := globalSpec.2.1
    L_pos := ?_
    C_pos := ?_
    epsilon_pos := ?_
    partition_nonneg := fun j _ n _ x => hφnonneg j n x
    partition_sum := fun j _ x => hφsum j x
    partition_support := fun j hj n _ x hx => hφsupport j hj n x hx
    frequency_zero := ?_
    frequency_increasing := globalSpec.2.2.1
    frequency_divisible := globalSpec.2.2.2
    phase_bounds := ?_
    frequency_ratios := ?_
    spread_high := ?_
    spread_low := ?_
    initial_K := rfl
    initial_G := rfl
    L_ge_one := ?_
    L_monotone := ?_
    C_eq := fun _ _ => rfl
    m_ge_K := ?_
    m_ge_pow := ?_
    m_ge_G := ?_
    m_ge_200 := ?_
    next_K := ?_
    K_double := ?_
    next_G_gap := ?_
    attenuation_m := ?_
    attenuation_G := ?_
    continuity_height := ?_
    polynomial_lower := ?_
    polynomial_attenuation := ?_
    samples_nonempty := ?_
    samples_positive := ?_
    samples_range := ?_
    samples_phase := ?_
    sampling_L2 := ?_ }
  · intro j _
    exact hmpos (j - 1)
  · intro j _
    exact (states hs height (j - 1)).K_pos
  · intro j _
    exact (states hs height (j - 1)).G_pos
  · intro j _
    exact (by norm_num : (0 : ℝ) < 1).trans_le (choices hs height (j - 1)).L_one
  · intro j _
    exact ((by norm_num : (0 : ℝ) < 1).trans_le
      (choices hs height (j - 1)).L_one).trans_le (le_max_left _ _)
  · intro j _
    exact (choices hs height (j - 1)).epsilon_pos
  · exact (global_agree hs height 0 0 (Nat.zero_le _)).trans rfl
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact constructed_phases hs height φ n
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact constructed_ratios hs height φ n
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact constructed_spread hs height φ n
  · intro j hj k hlo hhi i hi
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have ha := constructed_phases hs height φ n i hi
    exact phase_small_window (by exact_mod_cast hmpos n)
      (by exact_mod_cast (states hs height n).K_pos)
      (by exact_mod_cast (states hs height n).G_pos) ha.1.le ha.2.le hlo hhi
  · intro j _
    exact (choices hs height (j - 1)).L_one
  · intro j k _ hjk
    exact hLmono (Nat.sub_le_sub_right hjk 1)
  · intro j _
    exact (choices hs height (j - 1)).m_K
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (choices hs height n).m_pow
  · intro j _
    exact (choices hs height (j - 1)).m_G
  · intro j _
    exact (choices hs height (j - 1)).m_large
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rfl
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (choices hs height n).double
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (choices hs height n).gap
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (choices hs height n).attenuation_m
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (choices hs height n).gain
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (choices hs height n).continuity
  · intro j hj A B _hAs hBs hA hB hA0 hB0
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [coefficientBound_eq] at hA hB
    obtain ⟨r, hr, hcoef⟩ := (choices hs height n).polynomial A B
      (fun i _ => hA i) (fun i _ => hB i) hA0 hB0
    refine ⟨r, Finset.mem_Icc.mpr ⟨Nat.zero_le _, hr⟩, ?_⟩
    rw [convolution_eq_supported _ A B hBs]
    exact hcoef
  · intro j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact (choices hs height n).attenuation
  · intro j hj r hr
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hr' := (sample_index_bound hs height φ n r).mp hr
    rw [samples_eq hs height φ n r hr']
    exact (choices hs height n).sampling.samples_nonempty ⟨r, hr'⟩
  · intro j hj r hr l hl
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hr' := (sample_index_bound hs height φ n r).mp hr
    rw [samples_eq hs height φ n r hr'] at hl
    exact (choices hs height n).sampling.samples_positive ⟨r, hr'⟩ l hl
  · intro j hj r hr l hl
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hr' := (sample_index_bound hs height φ n r).mp hr
    rw [samples_eq hs height φ n r hr'] at hl
    exact (choices hs height n).sampling.samples_range ⟨r, hr'⟩ l hl
  · intro j hj r hr l hl
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hr' := (sample_index_bound hs height φ n r).mp hr
    rw [samples_eq hs height φ n r hr'] at hl
    rw [shift_eq, ell_eq]
    exact (choices hs height n).sampling.samples_phase ⟨r, hr'⟩ l hl
  · intro j hj r hr endpoint
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hr' := (sample_index_bound hs height φ n r).mp hr
    have heq : (fun x : Circle => (constructed hs height φ).samplingAverage θ
        (n + 1) r endpoint x - 1) =
      (fun x : Circle => TrialSampling.average (choices hs height n).m
        ((choices hs height n).sampling.samples ⟨r, hr'⟩) endpoint
        (fun i : Fin (choices hs height n).m =>
          Int.fract (((choices hs height n).sampling.q (i.val + 1) : ℝ) * θ))
        (fun i : Fin (choices hs height n).m =>
          ((choices hs height n).sampling.q (i.val + 1) : ℤ) • x) - 1) := by
      funext x
      rw [samplingAverage_eq hs height φ n r hr']
    rw [heq]
    exact (choices hs height n).sampling.sampling_L2 ⟨r, hr'⟩ endpoint

theorem exists_parameters_of_stage_supply {θ : ℝ} (hθ : Irrational θ)
    (hs : CircleStageSupply θ) : ∃ p : CircleParameterData, CircleParameterLaws θ p := by
  obtain ⟨height, φ, hnonneg, hsum, hsupport, _⟩ := exists_preparatory_partitions hθ
  exact ⟨constructed hs height φ, constructed_laws hs height φ hnonneg hsum hsupport⟩

end Invariant233.CircleParameterRecursion

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SeparatedCharacterFrequencies
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
namespace SeparatedCharacterFrequencies

open scoped BigOperators
open Finset

theorem sum_ne_zero_of_prefix_domination (v : ℕ → ℤ) (q : ℕ → ℝ) (H : ℝ)
    (m : ℕ) (hq : ∀ i < m, 0 < q i)
    (hbound : ∀ i < m, |(v i : ℝ)| ≤ H)
    (hdom : ∀ k < m, H * (∑ i ∈ range k, q i) < q k)
    (hv : ∃ i < m, v i ≠ 0) :
    (∑ i ∈ range m, (v i : ℝ) * q i) ≠ 0 := by
  induction m with
  | zero => simp at hv
  | succ m ih =>
    by_cases hvm : v m = 0
    · have hv' : ∃ i < m, v i ≠ 0 := by
        obtain ⟨i, hi, hvi⟩ := hv
        refine ⟨i, ?_, hvi⟩
        by_contra h
        have : i = m := by omega
        subst i
        exact hvi hvm
      simpa [sum_range_succ, hvm] using
        ih (fun i hi => hq i (by omega)) (fun i hi => hbound i (by omega))
          (fun k hk => hdom k (by omega)) hv'
    · have hm : m < m + 1 := Nat.lt_succ_self m
      have hpre : |∑ i ∈ range m, (v i : ℝ) * q i| ≤ H * ∑ i ∈ range m, q i := by
        calc
          |∑ i ∈ range m, (v i : ℝ) * q i| ≤
              ∑ i ∈ range m, |(v i : ℝ) * q i| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ range m, H * q i := by
            apply sum_le_sum
            intro i hi
            have hi' : i < m + 1 := by simpa using (lt_trans (mem_range.mp hi) hm)
            rw [abs_mul, abs_of_pos (hq i hi')]
            exact mul_le_mul_of_nonneg_right (hbound i hi') (hq i hi').le
          _ = H * ∑ i ∈ range m, q i := (mul_sum _ _ _).symm
      have hvpos : (0 : ℤ) < |v m| := abs_pos.mpr hvm
      have hvone : (1 : ℤ) ≤ |v m| := by omega
      have hvone' : (1 : ℝ) ≤ |(v m : ℝ)| := by exact_mod_cast hvone
      have hlast : q m ≤ |(v m : ℝ) * q m| := by
        rw [abs_mul, abs_of_pos (hq m hm)]
        nlinarith [hq m hm]
      intro hzero
      rw [sum_range_succ] at hzero
      have heq : (∑ i ∈ range m, (v i : ℝ) * q i) = -((v m : ℝ) * q m) := by
        linarith
      have habs : |∑ i ∈ range m, (v i : ℝ) * q i| = |(v m : ℝ) * q m| := by
        rw [heq, abs_neg]
      have hstrict := hdom m hm
      linarith

theorem prefix_domination_of_relative_gaps (q : ℕ → ℝ) (H : ℝ) (m : ℕ)
    (hH : 0 ≤ H) (hq : ∀ i, 0 < q i) (hmono : Monotone q)
    (hgap : ∀ i, i + 1 < m → (H * (m : ℝ)) * q i < q (i + 1)) :
    ∀ k < m, H * (∑ i ∈ range k, q i) < q k := by
  intro k hk
  cases k with
  | zero => simpa using hq 0
  | succ l =>
    have hsum : (∑ i ∈ range (l + 1), q i) ≤ (l + 1 : ℕ) * q l := by
      calc
        (∑ i ∈ range (l + 1), q i) ≤ ∑ _i ∈ range (l + 1), q l := by
          apply sum_le_sum
          intro i hi
          exact hmono (by simpa using mem_range.mp hi)
        _ = (l + 1 : ℕ) * q l := by simp
    have hlm : ((l + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk.le
    calc
      H * (∑ i ∈ range (l + 1), q i) ≤ H * (((l + 1 : ℕ) : ℝ) * q l) :=
        mul_le_mul_of_nonneg_left hsum hH
      _ ≤ H * ((m : ℝ) * q l) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hlm (hq l).le) hH
      _ = (H * (m : ℝ)) * q l := by ring
      _ < q (l + 1) := hgap l hk

theorem fourier_zsmul (v q : ℤ) (x : AddCircle (1 : ℝ)) :
    fourier v (q • x) = fourier (v * q) x := by
  simp only [fourier_apply, mul_zsmul]

theorem product_fourier_characters (v q : ℕ → ℤ) (m : ℕ) (x : AddCircle (1 : ℝ)) :
    (∏ i ∈ range m, fourier (v i) (q i • x)) =
      fourier (∑ i ∈ range m, v i * q i) x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, sum_range_succ, ih, fourier_add, fourier_zsmul]

theorem integral_fourier_eq_zero {k : ℤ} (hk : k ≠ 0) :
    (∫ x : AddCircle (1 : ℝ), fourier k x) = 0 := by
  exact MeasureTheory.integral_eq_zero_of_add_right_eq_neg
    (fourier_add_half_inv_index hk (by norm_num))

theorem integral_product_fourier_eq_zero (v q : ℕ → ℤ) (m : ℕ)
    (hfreq : (∑ i ∈ range m, v i * q i) ≠ 0) :
    (∫ x : AddCircle (1 : ℝ), ∏ i ∈ range m, fourier (v i) (q i • x)) = 0 := by
  simp_rw [product_fourier_characters]
  exact integral_fourier_eq_zero hfreq

theorem eventually_nonzero_frequency (v : ℕ → ℤ) (q : ℕ → ℕ → ℕ) (m : ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Filter.Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) Filter.atTop Filter.atTop)
    (hv : ∃ i < m, v i ≠ 0) :
    ∀ᶠ j in Filter.atTop, (∑ i ∈ range m, v i * (q j i : ℤ)) ≠ 0 := by
  let H : ℝ := ∑ i ∈ range m, |(v i : ℝ)|
  have hH : 0 ≤ H := sum_nonneg (fun _ _ => abs_nonneg _)
  have hbound : ∀ i < m, |(v i : ℝ)| ≤ H := by
    intro i hi
    change |(v i : ℝ)| ≤ ∑ k ∈ range m, |(v k : ℝ)|
    exact single_le_sum (fun k _ => abs_nonneg (v k : ℝ)) (mem_range.mpr hi)
  have hgaps : ∀ᶠ j in Filter.atTop, ∀ i ∈ range m,
      i + 1 < m → (H * (m : ℝ)) * (q j i : ℝ) < (q j (i + 1) : ℝ) := by
    rw [Finset.eventually_all]
    intro i hi
    by_cases him : i + 1 < m
    · filter_upwards [(hgap i him).eventually_gt_atTop (H * (m : ℝ))] with j hj
      intro _
      exact (lt_div_iff₀ (by exact_mod_cast hq j i)).mp hj
    · exact Filter.Eventually.of_forall (fun _ h => (him h).elim)
  filter_upwards [hgaps] with j hj
  have hqreal : ∀ i, (0 : ℝ) < q j i := fun i => by exact_mod_cast hq j i
  have hmonoreal : Monotone (fun i => (q j i : ℝ)) := by
    intro a b hab
    change (q j a : ℝ) ≤ (q j b : ℝ)
    exact_mod_cast hmono j hab
  have hdom := prefix_domination_of_relative_gaps (fun i => (q j i : ℝ)) H m
    hH hqreal hmonoreal (fun i hi => hj i (mem_range.mpr (by omega)) hi)
  have hreal := sum_ne_zero_of_prefix_domination v (fun i => (q j i : ℝ)) H m
    (fun i _ => hqreal i) hbound hdom hv
  exact_mod_cast hreal

theorem eventually_integral_product_fourier_eq_zero
    (v : ℕ → ℤ) (q : ℕ → ℕ → ℕ) (m : ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Filter.Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) Filter.atTop Filter.atTop)
    (hv : ∃ i < m, v i ≠ 0) :
    ∀ᶠ j in Filter.atTop,
      (∫ x : AddCircle (1 : ℝ), ∏ i ∈ range m, fourier (v i) ((q j i : ℤ) • x)) = 0 := by
  filter_upwards [eventually_nonzero_frequency v q m hq hmono hgap hv] with j hj
  exact integral_product_fourier_eq_zero v (fun i => (q j i : ℤ)) m hj

end SeparatedCharacterFrequencies
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CharacterWeakConvergence
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233
namespace CharacterWeakConvergence

open MeasureTheory Filter Set
open scoped Topology NNReal

section Integral
variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem pullbackIntegral_norm_le (φ : C(X, Y)) : ‖pullbackIntegral μ φ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  have h := norm_integral_le_of_norm_le_const
    (μ := μ) (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm (φ x)))
  simpa using h

end Integral

theorem tendsto_of_dense_span
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : ℕ → E →L[ℂ] ℂ) (M : E →L[ℂ] ℂ) (C : ℝ≥0)
    (hL : ∀ n, ‖L n‖₊ ≤ C) (s : Set E)
    (hs : (Submodule.span ℂ s).topologicalClosure = ⊤)
    (hconv : ∀ f ∈ s, Tendsto (fun n => L n f) atTop (𝓝 (M f)))
    (f : E) : Tendsto (fun n => L n f) atTop (𝓝 (M f)) := by
  let S : Submodule ℂ E :=
    { carrier := {f | Tendsto (fun n => L n f) atTop (𝓝 (M f))}
      zero_mem' := by simp
      add_mem' := by
        intro f g hf hg
        simpa only [Set.mem_ofPred_eq, map_add] using hf.add hg
      smul_mem' := by
        intro c f hf
        simpa only [Set.mem_ofPred_eq, map_smul] using hf.const_smul c }
  have hclosed : IsClosed (S : Set E) := by
    apply Equicontinuous.isClosed_setOfPred_tendsto _ M.continuous
    exact (LipschitzWith.uniformEquicontinuous (fun n => (L n : E → ℂ)) C
      (fun n => (L n).lipschitz.weaken (hL n))).equicontinuous
  have hsS : Submodule.span ℂ s ≤ S := Submodule.span_le.mpr hconv
  have htop : (⊤ : Submodule ℂ E) ≤ S := by
    rw [← hs]
    exact Submodule.topologicalClosure_minimal _ hsS hclosed
  exact htop (Submodule.mem_top)

local instance circleVolumeProbability :
    IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by simp [AddCircle.measure_univ]⟩

theorem integral_mFourier_eq_zero {m : ℕ} {v : Fin m → ℤ} (hv : v ≠ 0) :
    (∫ y : UnitAddTorus (Fin m), UnitAddTorus.mFourier v y) = 0 := by
  change (∫ y : Fin m → AddCircle (1 : ℝ), ∏ i, fourier (v i) (y i)) = 0
  rw [integral_fintype_prod_volume_eq_prod]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (SeparatedCharacterFrequencies.integral_fourier_eq_zero hi)

theorem tendsto_integral_joint_characters
    (q : ℕ → ℕ → ℕ) (m : ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    (f : C(UnitAddTorus (Fin m), ℂ)) :
    Tendsto (fun j => ∫ x : AddCircle (1 : ℝ),
      f (fun i : Fin m => (q j i.val : ℤ) • x)) atTop
      (𝓝 (∫ y : UnitAddTorus (Fin m), f y)) := by
  let φ : ℕ → C(AddCircle (1 : ℝ), UnitAddTorus (Fin m)) := fun j =>
    ⟨fun x i => (q j i.val : ℤ) • x, by fun_prop⟩
  let L : ℕ → C(UnitAddTorus (Fin m), ℂ) →L[ℂ] ℂ :=
    fun j => pullbackIntegral volume (φ j)
  let M : C(UnitAddTorus (Fin m), ℂ) →L[ℂ] ℂ :=
    pullbackIntegral volume (ContinuousMap.id _)
  have hL : ∀ j, ‖L j‖₊ ≤ (1 : ℝ≥0) := by
    intro j
    exact_mod_cast pullbackIntegral_norm_le volume (φ j)
  have hconv : ∀ g ∈ Set.range (UnitAddTorus.mFourier (d := Fin m)),
      Tendsto (fun j => L j g) atTop (𝓝 (M g)) := by
    rintro _ ⟨v, rfl⟩
    by_cases hv : v = 0
    · subst v
      simp only [UnitAddTorus.mFourier_zero]
      simp [L, M, pullbackIntegral_apply]
    · let v' : ℕ → ℤ := fun n => if h : n < m then v ⟨n, h⟩ else 0
      have hv' : ∃ i < m, v' i ≠ 0 := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
        refine ⟨i.val, i.isLt, ?_⟩
        simpa [v'] using hi
      have hprod : ∀ j (x : AddCircle (1 : ℝ)),
          UnitAddTorus.mFourier v (φ j x) =
            ∏ i ∈ Finset.range m, fourier (v' i) ((q j i : ℤ) • x) := by
        intro j x
        change (∏ i : Fin m, fourier (v i) ((q j i.val : ℤ) • x)) = _
        simpa [v'] using Fin.prod_univ_eq_prod_range
          (fun i => fourier (v' i) ((q j i : ℤ) • x)) m
      have hevent : ∀ᶠ j in atTop, L j (UnitAddTorus.mFourier v) = 0 := by
        filter_upwards [SeparatedCharacterFrequencies.eventually_integral_product_fourier_eq_zero
          v' q m hq hmono hgap hv'] with j hj
        change (∫ x : AddCircle (1 : ℝ), UnitAddTorus.mFourier v (φ j x)) = 0
        simpa only [hprod] using hj
      have hM : M (UnitAddTorus.mFourier v) = 0 := integral_mFourier_eq_zero hv
      rw [hM]
      exact tendsto_const_nhds.congr' (hevent.mono fun _ h => h.symm)
  exact tendsto_of_dense_span L M 1 hL _
    UnitAddTorus.span_mFourier_closure_eq_top hconv f

end CharacterWeakConvergence
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CharacterLawConvergence
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233
namespace CharacterLaws

open MeasureTheory Filter
open scoped Topology

theorem tendsto_apply_of_uniform_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : ℕ → E →L[ℂ] ℂ) (M : E →L[ℂ] ℂ)
    (hL : ∀ j, ‖L j‖ ≤ 1)
    (hconv : ∀ f, Tendsto (fun j => L j f) atTop (𝓝 (M f)))
    {f : ℕ → E} {g : E} (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun j => L j (f j)) atTop (𝓝 (M g)) := by
  have hnorm : Tendsto (fun j => ‖f j - g‖) atTop (𝓝 0) := by
    have hg : Tendsto (fun _ : ℕ => g) atTop (𝓝 g) := tendsto_const_nhds
    simpa using (hf.sub hg).norm
  have hsmall : Tendsto (fun j => L j (f j - g)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hnorm
    calc
      ‖L j (f j - g)‖ ≤ ‖L j‖ * ‖f j - g‖ := (L j).le_opNorm _
      _ ≤ 1 * ‖f j - g‖ := mul_le_mul_of_nonneg_right (hL j) (norm_nonneg _)
      _ = ‖f j - g‖ := one_mul _
  simpa only [map_sub, sub_add_cancel, zero_add] using hsmall.add (hconv g)

theorem tendsto_integral_character_phase
    {Z : Type*} [TopologicalSpace Z]
    (q : ℕ → ℕ → ℕ) (m : ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    {a : ℕ → Z} {b : Z} (ha : Tendsto a atTop (𝓝 b))
    (f : C(Z × UnitAddTorus (Fin m), ℂ)) :
    Tendsto (fun j => ∫ x : AddCircle (1 : ℝ),
      f (a j, fun i : Fin m => (q j i.val : ℤ) • x)) atTop
      (𝓝 (∫ y : UnitAddTorus (Fin m), f (b, y))) := by
  let : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    circleHaar.property
  let L : ℕ → C(UnitAddTorus (Fin m), ℂ) →L[ℂ] ℂ :=
    fun j => CharacterWeakConvergence.pullbackIntegral volume
      (characterMap (fun i : Fin m => q j i.val))
  let M : C(UnitAddTorus (Fin m), ℂ) →L[ℂ] ℂ :=
    CharacterWeakConvergence.pullbackIntegral volume (ContinuousMap.id _)
  exact tendsto_apply_of_uniform_bound L M
    (fun j => CharacterWeakConvergence.pullbackIntegral_norm_le volume _)
    (fun g => CharacterWeakConvergence.tendsto_integral_joint_characters
      q m hq hmono hgap g)
    (f.curry.continuous.tendsto b |>.comp ha)

theorem integral_characterPhaseLaw {Z : Type*} [TopologicalSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] {m : ℕ} (q : Fin m → ℕ) (a : Z)
    (f : C(Z × UnitAddTorus (Fin m), ℂ)) :
    (∫ z, f z ∂(characterPhaseLaw q a : Measure _)) =
      ∫ x : AddCircle (1 : ℝ), f (a, characterMap q x) := by
  change (∫ z, f z ∂Measure.map (fun x => (a, characterMap q x)) volume) = _
  rw [integral_map
    (by fun_prop : Continuous (fun x => (a, characterMap q x))).measurable.aemeasurable
    f.continuous.aestronglyMeasurable]

theorem integral_haarPhaseLaw {Z : Type*} [TopologicalSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] (m : ℕ) (a : Z)
    (f : C(Z × UnitAddTorus (Fin m), ℂ)) :
    (∫ z, f z ∂(haarPhaseLaw m a : Measure _)) =
      ∫ y : UnitAddTorus (Fin m), f (a, y) := by
  change (∫ z, f z ∂Measure.map (fun y : UnitAddTorus (Fin m) => (a, y)) volume) = _
  rw [integral_map
    (by fun_prop : Continuous (fun y : UnitAddTorus (Fin m) => (a, y))).measurable.aemeasurable
    f.continuous.aestronglyMeasurable]

theorem tendsto_characterPhaseLaw
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (q : ℕ → ℕ → ℕ) (m : ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    {a : ℕ → Z} {b : Z} (ha : Tendsto a atTop (𝓝 b)) :
    Tendsto (fun j => characterPhaseLaw (fun i : Fin m => q j i.val) (a j)) atTop
      (𝓝 (haarPhaseLaw m b)) := by
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mpr
  intro f
  have h := tendsto_integral_character_phase q m hq hmono hgap ha f.toContinuousMap
  simpa only [← BoundedContinuousFunction.coe_toContinuousMap,
    integral_characterPhaseLaw, integral_haarPhaseLaw, characterMap, ContinuousMap.coe_mk] using h

end CharacterLaws
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CharacterPhaseRealization
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
namespace PrescribedPhaseRealization

open Filter
open scoped Topology

theorem exists_phase_approximation_family {θ : ℝ} (hθ : Irrational θ)
    (target : ℕ → ℝ) (htarget₀ : ∀ i, 0 < target i)
    (htarget₁ : ∀ i, target i < 1) {q₀ : ℕ} (hq₀ : 0 < q₀) :
    ∃ q : ℕ → ℕ → ℕ,
      (∀ j, q j 0 = q₀) ∧ (∀ j i, 0 < q j i) ∧
      (∀ j, StrictMono (q j)) ∧ (∀ j i, q j i ∣ q j (i + 1)) ∧
      (∀ i, Tendsto (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop) ∧
      ∀ i, Tendsto (fun j => Int.fract ((q j (i + 1) : ℝ) * θ)) atTop
        (𝓝 (target i)) := by
  classical
  have hex : ∀ j : ℕ, ∃ q : ℕ → ℕ,
      q 0 = q₀ ∧ (∀ i, 0 < q i) ∧
      ∀ i, q i ∣ q (i + 1) ∧ q i < q (i + 1) ∧
        (j + 1) * q i ≤ q (i + 1) ∧
        |Int.fract ((q (i + 1) : ℝ) * θ) - target i| < 1 / ((j : ℝ) + 1) := by
    intro j
    exact exists_divisible_phase_approximation hθ target
      (fun _ => 1 / ((j : ℝ) + 1)) (fun _ => j + 1)
      htarget₀ htarget₁ (fun _ => by positivity) hq₀
  choose q hzero hpos hstep using hex
  refine ⟨q, hzero, hpos, ?_, ?_, ?_, ?_⟩
  · intro j
    exact strictMono_nat_of_lt_succ (fun i => (hstep j i).2.1)
  · intro j i
    exact (hstep j i).1
  · intro i
    apply tendsto_atTop_mono (f := fun j : ℕ => (j : ℝ) + 1)
    · intro j
      apply (le_div_iff₀ (by exact_mod_cast hpos j i)).mpr
      exact_mod_cast (hstep j i).2.2.1
    · exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  · intro i
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun j => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [Real.dist_eq] using (hstep j i).2.2.2.le

end PrescribedPhaseRealization
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CharacterSamplingLimit
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.CharacterLaws

open MeasureTheory Filter
open scoped Topology

theorem tendsto_integral_character_phase_of_ae_continuous
    {Z : Type*} [PseudoEMetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (q : ℕ → ℕ → ℕ) (m : ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    {a : ℕ → Z} {b : Z} (ha : Tendsto a atTop (𝓝 b))
    {f : Z × UnitAddTorus (Fin m) → ℝ} (hf : Measurable f)
    (hc : ∀ᵐ y : UnitAddTorus (Fin m), ContinuousAt f (b, y))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ z, |f z| ≤ B) :
    Tendsto (fun j => ∫ x : AddCircle (1 : ℝ),
      f (a j, fun i : Fin m => (q j i.val : ℤ) • x)) atTop
      (𝓝 (∫ y : UnitAddTorus (Fin m), f (b, y))) := by
  have hclaw : ∀ᵐ z ∂(haarPhaseLaw m b : Measure _), ContinuousAt f z := by
    change ∀ᵐ z ∂Measure.map (fun y : UnitAddTorus (Fin m) => (b, y)) volume,
      ContinuousAt f z
    apply (ae_map_iff
      (by fun_prop : Continuous (fun y : UnitAddTorus (Fin m) => (b, y))).measurable.aemeasurable
      (measurableSet_of_continuousAt f)).mpr
    exact hc
  have h := WeakConvergenceAEContinuous.tendsto_integral_of_ae_continuous
    (tendsto_characterPhaseLaw q m hq hmono hgap ha) hf hclaw hB hb
  have hmap (j : ℕ) :
      (∫ z, f z ∂(characterPhaseLaw (fun i : Fin m => q j i.val) (a j) : Measure _)) =
        ∫ x : AddCircle (1 : ℝ), f (a j, fun i : Fin m => (q j i.val : ℤ) • x) := by
    change (∫ z, f z ∂Measure.map
      (fun x => (a j, characterMap (fun i : Fin m => q j i.val) x)) volume) = _
    rw [integral_map
      (by fun_prop : Continuous
        (fun x => (a j, characterMap (fun i : Fin m => q j i.val) x))).measurable.aemeasurable
      hf.aestronglyMeasurable]
    rfl
  have hlim : (∫ z, f z ∂(haarPhaseLaw m b : Measure _)) =
      ∫ y : UnitAddTorus (Fin m), f (b, y) := by
    change (∫ z, f z ∂Measure.map (fun y : UnitAddTorus (Fin m) => (b, y)) volume) = _
    rw [integral_map
      (by fun_prop : Continuous (fun y : UnitAddTorus (Fin m) => (b, y))).measurable.aemeasurable
      hf.aestronglyMeasurable]
  simpa only [hmap, hlim] using h

end Invariant233.CharacterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleSamplingKernelBridge
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
namespace Invariant233.CircleParameterData

theorem kernel_eq_manuscriptKernel (m : ℕ) (z v : ℝ)
    (hv : v ∈ Set.Ico (0 : ℝ) 1) :
    kernel m z v = ScalarSampling.manuscriptKernel m z v := by
  have he : Int.fract v = v := Int.fract_eq_self.mpr hv
  simp only [kernel, kernelWidth, delta, ScalarSampling.manuscriptKernel,
    ScalarSampling.circleKernel, ScalarSampling.rawKernel, ScalarSampling.delta, he,
    Set.indicator_apply, Set.mem_Ioo, one_div]
  split_ifs <;> simp_all

theorem starting_kernel_fract (m : ℕ) (z v : ℝ) :
    orientedKernel false m z (Int.fract v) =
      ScalarSampling.manuscriptKernel m z (Int.fract v) := by
  simpa only [orientedKernel, Bool.false_eq_true, ↓reduceIte] using
    kernel_eq_manuscriptKernel m z (Int.fract v)
      ⟨Int.fract_nonneg v, Int.fract_lt_one v⟩

theorem endpoint_kernel_fract (m : ℕ) (z v : ℝ) :
    orientedKernel true m z (Int.fract v) =
      ScalarSampling.manuscriptEndpointKernel m z (Int.fract v) := by
  simpa only [orientedKernel, ↓reduceIte, ScalarSampling.manuscriptEndpointKernel] using
    kernel_eq_manuscriptKernel m (z - Int.fract v) (Int.fract v)
      ⟨Int.fract_nonneg v, Int.fract_lt_one v⟩

end Invariant233.CircleParameterData

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSampling
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

lemma manuscript_parameters {m : ℕ} (hm : 200 ≤ m) :
    0 < (m : ℝ) ^ (-(3 / 5 : ℝ)) ∧
      (m : ℝ) ^ (-(3 / 5 : ℝ)) ≤ 1 ∧
      0 < 1 / (m : ℝ)^2 ∧ 1 / (m : ℝ)^2 ≤ 1 / 2 := by
  have hmR : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  refine ⟨Real.rpow_pos_of_pos hmp _,
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num),
    one_div_pos.mpr (sq_pos_of_pos hmp), ?_⟩
  exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by nlinarith)

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped Topology

namespace Invariant233.ScalarSampling

lemma continuousAt_ite_lt_of_ne {X : Type*} [TopologicalSpace X]
    {f g a b : X → ℝ} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (ha : ContinuousAt a x) (hb : ContinuousAt b x) (hne : f x ≠ g x) :
    ContinuousAt (fun y => if f y < g y then a y else b y) x := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply ha.congr_of_eventuallyEq
    filter_upwards [hf.eventually_lt hg hlt] with y hy
    exact ite_eq_left hy
  · apply hb.congr_of_eventuallyEq
    filter_upwards [hg.eventually_lt hf hgt] with y hy
    exact ite_eq_right (not_lt.mpr hy.le)

lemma continuousAt_ite_le_of_ne {X : Type*} [TopologicalSpace X]
    {f g a b : X → ℝ} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (ha : ContinuousAt a x) (hb : ContinuousAt b x) (hne : f x ≠ g x) :
    ContinuousAt (fun y => if f y ≤ g y then a y else b y) x := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply ha.congr_of_eventuallyEq
    filter_upwards [hf.eventually_lt hg hlt] with y hy
    exact ite_eq_left hy.le
  · apply hb.congr_of_eventuallyEq
    filter_upwards [hg.eventually_lt hf hgt] with y hy
    exact ite_eq_right (not_le.mpr hy)

theorem continuousAt_rawKernel_pair {h α : ℝ} (hh : h ≠ 0) (p : ℝ × ℝ)
    (hdelta : delta p.1 ≠ 0) (hcut : α ≠ delta p.1)
    (hzero : p.2 ≠ 0) (hedge : p.2 ≠ h * delta p.1) :
    ContinuousAt (fun q : ℝ × ℝ => rawKernel h α q.1 q.2) p := by
  have hd : ContinuousAt (fun q : ℝ × ℝ => delta q.1) p :=
    continuous_fst.continuousAt.min (continuousAt_const.sub continuous_fst.continuousAt)
  have hheight : ContinuousAt (fun q : ℝ × ℝ => h * delta q.1) p := continuousAt_const.mul hd
  have hinv : ContinuousAt (fun q : ℝ × ℝ => (h * delta q.1)⁻¹) p :=
    hheight.inv₀ (mul_ne_zero hh hdelta)
  have he := continuousAt_ite_lt_of_ne continuous_snd.continuousAt hheight
    hinv (continuousAt_const (y := (0 : ℝ))) hedge
  have hz := continuousAt_ite_lt_of_ne (continuousAt_const (y := (0 : ℝ)))
    continuous_snd.continuousAt he (continuousAt_const (y := (0 : ℝ))) hzero.symm
  have hc := continuousAt_ite_le_of_ne (continuousAt_const (y := α)) hd hz
    (continuousAt_const (y := (0 : ℝ))) hcut
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  simp only [rawKernel, Set.indicator_apply, mem_Ioo, ite_and]

theorem continuousAt_circleKernel_pair {h α : ℝ} (hh : h ≠ 0) (p : ℝ × ℝ)
    (hz : Int.fract p.1 ≠ 0) (hv : Int.fract p.2 ≠ 0)
    (hcut : α ≠ delta (Int.fract p.1))
    (hedge : Int.fract p.2 ≠ h * delta (Int.fract p.1)) :
    ContinuousAt (fun q : ℝ × ℝ => circleKernel h α q.1 q.2) p := by
  have hdz : 0 < delta (Int.fract p.1) := by
    apply lt_min
    · exact lt_of_le_of_ne (Int.fract_nonneg _) hz.symm
    · exact sub_pos.mpr (Int.fract_lt_one _)
  have hzfloor : p.1 ≠ (⌊p.1⌋ : ℤ) := by
    intro heq
    apply hz
    rw [heq]; simp
  have hvfloor : p.2 ≠ (⌊p.2⌋ : ℤ) := by
    intro heq
    apply hv
    rw [heq]; simp
  have hrep : ContinuousAt (fun q : ℝ × ℝ => (Int.fract q.1, Int.fract q.2)) p :=
    ((continuousAt_fract hzfloor).comp continuous_fst.continuousAt).prodMk
      ((continuousAt_fract hvfloor).comp continuous_snd.continuousAt)
  exact (continuousAt_rawKernel_pair hh (Int.fract p.1, Int.fract p.2)
    hdz.ne' hcut hv hedge).comp_of_eq hrep rfl

theorem continuousAt_circleEndpoint_pair {h α : ℝ} (hh : h ≠ 0) (p : ℝ × ℝ)
    (hz : Int.fract (p.1 - p.2) ≠ 0) (hv : Int.fract p.2 ≠ 0)
    (hcut : α ≠ delta (Int.fract (p.1 - p.2)))
    (hedge : Int.fract p.2 ≠ h * delta (Int.fract (p.1 - p.2))) :
    ContinuousAt (fun q : ℝ × ℝ => circleKernel h α (q.1 - q.2) q.2) p := by
  have hshear : ContinuousAt (fun q : ℝ × ℝ => (q.1-q.2, q.2)) p :=
    (continuous_fst.continuousAt.sub continuous_snd.continuousAt).prodMk continuous_snd.continuousAt
  exact (continuousAt_circleKernel_pair hh (p.1-p.2, p.2) hz hv hcut hedge).comp_of_eq hshear rfl

lemma ae_fract_sub_ne (c a : ℝ) : ∀ᵐ x : ℝ ∂volume, Int.fract (x-c) ≠ a := by
  rw [ae_iff]
  apply Set.Countable.measure_zero
  apply (Set.countable_range (fun n : ℤ => a + c + n)).mono
  intro x hx
  change ¬Int.fract (x-c) ≠ a at hx
  have heq := not_not.mp hx
  refine ⟨⌊x-c⌋, ?_⟩
  have hsum := Int.fract_add_floor (x-c)
  rw [heq] at hsum
  linarith

lemma ae_delta_fract_sub_ne (c a : ℝ) :
    ∀ᵐ x : ℝ ∂volume, delta (Int.fract (x-c)) ≠ a := by
  filter_upwards [ae_fract_sub_ne c a, ae_fract_sub_ne c (1-a)] with x hx hy
  intro heq
  unfold delta at heq
  rcases le_total (Int.fract (x-c)) (1-Int.fract (x-c)) with h | h
  · rw [min_eq_left h] at heq
    exact hx heq
  · rw [min_eq_right h] at heq
    apply hy
    linarith

theorem ae_joint_continuousAt_circleKernel {h α : ℝ} (hh : h ≠ 0)
    (v : ℝ) (hv : Int.fract v ≠ 0) :
    ∀ᵐ z : ℝ ∂volume,
      ContinuousAt (fun p : ℝ × ℝ => circleKernel h α p.1 p.2) (z,v) := by
  filter_upwards [ae_fract_sub_ne 0 0, ae_delta_fract_sub_ne 0 α,
    ae_delta_fract_sub_ne 0 (Int.fract v / h)] with z hz hc he
  simp only [sub_zero] at hz hc he
  apply continuousAt_circleKernel_pair hh (z,v) hz hv hc.symm
  intro heq
  apply he
  rw [heq]
  field_simp

theorem ae_joint_continuousAt_circleEndpoint {h α : ℝ} (hh : h ≠ 0)
    (v : ℝ) (hv : Int.fract v ≠ 0) :
    ∀ᵐ z : ℝ ∂volume,
      ContinuousAt (fun p : ℝ × ℝ => circleKernel h α (p.1-p.2) p.2) (z,v) := by
  filter_upwards [ae_fract_sub_ne v 0, ae_delta_fract_sub_ne v α,
    ae_delta_fract_sub_ne v (Int.fract v / h)] with z hz hc he
  apply continuousAt_circleEndpoint_pair hh (z,v) hz hv hc.symm
  intro heq
  apply he
  rw [heq]
  field_simp

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingTestContinuity
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.average_eq_trialAverage _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Invariant233.SamplingTests

lemma measurable_kernel (endpoint : Bool) (m : ℕ) :
    Measurable (fun p : ℝ × ℝ => kernel endpoint m p.1 p.2) := by
  have hd : Measurable (fun p : ℝ × ℝ => CircleParameterData.delta p.1) :=
    (measurable_fract.comp measurable_fst).min
      (measurable_const.sub (measurable_fract.comp measurable_fst))
  have hk : Measurable (fun p : ℝ × ℝ => CircleParameterData.kernel m p.1 p.2) := by
    unfold CircleParameterData.kernel
    apply Measurable.ite
    · exact (measurableSet_le measurable_const hd).inter
        ((measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_lt measurable_snd (measurable_const.mul hd)))
    · exact measurable_const.div (measurable_const.mul hd)
    · exact measurable_const
  cases endpoint
  · exact hk.comp (measurable_fst.prodMk (measurable_fract.comp measurable_snd))
  · exact hk.comp ((measurable_fst.sub (measurable_fract.comp measurable_snd)).prodMk
      (measurable_fract.comp measurable_snd))

lemma measurable_circleKernel (endpoint : Bool) (m : ℕ) :
    Measurable (fun p : ℝ × Circle => circleKernel endpoint m p.1 p.2) :=
  (measurable_kernel endpoint m).comp
    ((CircleParameterData.measurable_rep.comp measurable_snd).prodMk measurable_fst)

lemma measurable_average (endpoint : Bool) (m d : ℕ) (s : Finset ℕ) :
    Measurable (average endpoint m d s) := by
  unfold average
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro n hn
  apply Finset.measurable_prod
  intro i hi
  have hp : Measurable (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) =>
      (n : ℝ) * z.1 i) :=
    measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)
  have hx : Measurable (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) => z.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  exact (measurable_circleKernel endpoint m).comp (hp.prodMk hx)

lemma measurable_errorSq (endpoint : Bool) (m d : ℕ) (s : Finset ℕ) :
    Measurable (errorSq endpoint m d s) :=
  ((measurable_average endpoint m d s).sub measurable_const).pow_const 2

lemma kernel_bounds (endpoint : Bool) {m : ℕ} (hm : 0 < m) (z v : ℝ) :
    0 ≤ kernel endpoint m z v ∧
      kernel endpoint m z v ≤ (m : ℝ)^2 / CircleParameterData.kernelWidth m :=
  CircleParameterData.orientedKernel_bounds endpoint hm z (Int.fract v)

lemma average_bounds (endpoint : Bool) {m : ℕ} (hm : 0 < m)
    (d : ℕ) (s : Finset ℕ) (z : (Fin d → ℝ) × UnitAddTorus (Fin d)) :
    0 ≤ average endpoint m d s z ∧ average endpoint m d s z ≤
      ((m : ℝ)^2 / CircleParameterData.kernelWidth m) ^ d := by
  classical
  let B : ℝ := (m : ℝ)^2 / CircleParameterData.kernelWidth m
  have hB : 0 ≤ B := by dsimp [B, CircleParameterData.kernelWidth] <;> positivity
  have hnon (n : ℕ) : 0 ≤ ∏ i : Fin d,
      circleKernel endpoint m ((n : ℝ) * z.1 i) (z.2 i) :=
    Finset.prod_nonneg fun i _ => (kernel_bounds endpoint hm _ _).1
  have hupper (n : ℕ) : (∏ i : Fin d,
      circleKernel endpoint m ((n : ℝ) * z.1 i) (z.2 i)) ≤ B ^ d := by
    calc
      _ ≤ ∏ _i : Fin d, B := Finset.prod_le_prod
        (fun i _ => (kernel_bounds endpoint hm _ _).1)
        (fun i _ => (kernel_bounds endpoint hm _ _).2)
      _ = _ := by simp
  unfold average
  refine ⟨mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => hnon n), ?_⟩
  by_cases hs : s.card = 0
  · simp only [hs, Nat.cast_zero, inv_zero, zero_mul]
    exact pow_nonneg hB d
  · have hsR : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs
    calc
      _ ≤ (s.card : ℝ)⁻¹ * ∑ _n ∈ s, B ^ d :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => hupper n) (by positivity)
      _ = B ^ d := by simp [hsR]

lemma errorSq_bounds (endpoint : Bool) {m : ℕ} (hm : 0 < m)
    (d : ℕ) (s : Finset ℕ) (z : (Fin d → ℝ) × UnitAddTorus (Fin d)) :
    0 ≤ errorSq endpoint m d s z ∧ |errorSq endpoint m d s z| ≤
      (((m : ℝ)^2 / CircleParameterData.kernelWidth m) ^ d + 1) ^ 2 := by
  have ha := average_bounds endpoint hm d s z
  have hb : 0 ≤ ((m : ℝ)^2 / CircleParameterData.kernelWidth m) ^ d := by
    unfold CircleParameterData.kernelWidth
    positivity
  unfold errorSq
  refine ⟨sq_nonneg _, ?_⟩
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (average endpoint m d s z),
    mul_nonneg ha.1 (sub_nonneg.mpr ha.2)]

lemma ae_joint_continuousAt_kernel (endpoint : Bool) {m : ℕ} (hm : 200 ≤ m)
    (v : ℝ) (hv : Int.fract v ≠ 0) :
    ∀ᵐ z : ℝ ∂volume,
      ContinuousAt (fun p : ℝ × ℝ => kernel endpoint m p.1 p.2) (z,v) := by
  have hh := (ScalarSampling.manuscript_parameters hm).1
  have hvfloor : v ≠ (⌊v⌋ : ℤ) := by
    intro heq
    apply hv
    rw [heq]
    simp
  have hf : ContinuousAt Int.fract v := continuousAt_fract hvfloor
  have hcomp (z : ℝ) : ContinuousAt
      (fun p : ℝ × ℝ => (p.1, Int.fract p.2)) (z,v) :=
    continuous_fst.continuousAt.prodMk (hf.comp_of_eq continuous_snd.continuousAt rfl)
  cases endpoint
  · filter_upwards [ScalarSampling.ae_joint_continuousAt_circleKernel hh.ne'
      (Int.fract v) (by simpa using hv)] with z hz
    have h := hz.comp_of_eq (hcomp z) rfl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact CircleParameterData.starting_kernel_fract m p.1 p.2
  · filter_upwards [ScalarSampling.ae_joint_continuousAt_circleEndpoint hh.ne'
      (Int.fract v) (by simpa using hv)] with z hz
    have h := hz.comp_of_eq (hcomp z) rfl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact CircleParameterData.endpoint_kernel_fract m p.1 p.2

lemma ae_joint_continuousAt_circleKernel (endpoint : Bool) {m : ℕ} (hm : 200 ≤ m)
    (v : ℝ) (hv : Int.fract v ≠ 0) :
    ∀ᵐ x : Circle ∂volume,
      ContinuousAt (fun p : ℝ × Circle => circleKernel endpoint m p.1 p.2) (v,x) := by
  let : NullSingletonClass (volume : Measure Circle) := by
    constructor
    intro x
    simpa using (AddCircle.volume_closedBall (T := (1 : ℝ)) (x := x) 0)
  have hc := CocycleSupport.measurePreserving_circleRepresentative.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (ae_joint_continuousAt_kernel endpoint hm v hv))
  filter_upwards [hc, (volume : Measure Circle).ae_ne 0] with x hx hxzero
  have hr : ContinuousAt CircleParameterData.rep x :=
    continuous_subtype_val.continuousAt.comp
      (AddCircle.continuousAt_equivIco (1 : ℝ) 0 hxzero)
  have hp : ContinuousAt
      (fun p : ℝ × Circle => (CircleParameterData.rep p.2, p.1)) (v,x) :=
    (hr.comp_of_eq continuous_snd.continuousAt rfl).prodMk continuous_fst.continuousAt
  exact hx.comp_of_eq hp rfl

lemma continuousAt_average_of_kernel (endpoint : Bool) (m d : ℕ) (s : Finset ℕ)
    (τ : Fin d → ℝ) (y : UnitAddTorus (Fin d))
    (h : ∀ n ∈ s, ∀ i : Fin d,
      ContinuousAt (fun p : ℝ × Circle => circleKernel endpoint m p.1 p.2)
        ((n : ℝ) * τ i, y i)) :
    ContinuousAt (average endpoint m d s) (τ,y) := by
  have hterm (n : ℕ) (hn : n ∈ s) (i : Fin d) :
      ContinuousAt (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) =>
        circleKernel endpoint m ((n : ℝ) * z.1 i) (z.2 i)) (τ,y) := by
    have ha : ContinuousAt (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) => z.1 i)
        (τ,y) := (continuousAt_apply i τ).comp_of_eq continuous_fst.continuousAt rfl
    have hy : ContinuousAt (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) => z.2 i)
        (τ,y) := (continuousAt_apply i y).comp_of_eq continuous_snd.continuousAt rfl
    have hnphase : ContinuousAt
        (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) => (n : ℝ) * z.1 i) (τ,y) :=
      continuousAt_const.mul ha
    have hmap : ContinuousAt
        (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) => ((n : ℝ) * z.1 i, z.2 i))
        (τ,y) := hnphase.prodMk hy
    exact ContinuousAt.comp
      (f := fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) => ((n : ℝ) * z.1 i, z.2 i))
      (g := fun p : ℝ × Circle => circleKernel endpoint m p.1 p.2)
      (h n hn i) hmap
  have hp (n : ℕ) (hn : n ∈ s) :
      ContinuousAt (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) =>
        ∏ i : Fin d, circleKernel endpoint m ((n : ℝ) * z.1 i) (z.2 i)) (τ,y) :=
    tendsto_finsetProd Finset.univ (fun i _ => hterm n hn i)
  have hs : ContinuousAt (fun z : (Fin d → ℝ) × UnitAddTorus (Fin d) =>
      ∑ n ∈ s, ∏ i : Fin d, circleKernel endpoint m ((n : ℝ) * z.1 i) (z.2 i)) (τ,y) :=
    tendsto_finsetSum s hp
  exact hs.const_mul _

lemma ae_joint_continuousAt_average (endpoint : Bool) {m : ℕ} (hm : 200 ≤ m)
    (d : ℕ) (s : Finset ℕ) (τ : Fin d → ℝ)
    (hphase : ∀ n ∈ s, ∀ i, Int.fract ((n : ℝ) * τ i) ≠ 0) :
    ∀ᵐ y : UnitAddTorus (Fin d) ∂volume,
      ContinuousAt (average endpoint m d s) (τ,y) := by
  let : IsProbabilityMeasure (volume : Measure Circle) :=
    CharacterLaws.circleHaar.property
  have hc (n : ℕ) (hn : n ∈ s) (i : Fin d) :
      ∀ᵐ y : UnitAddTorus (Fin d) ∂volume,
        ContinuousAt (fun p : ℝ × Circle => circleKernel endpoint m p.1 p.2)
          ((n : ℝ) * τ i, y i) :=
    (measurePreserving_eval (fun _ : Fin d => (volume : Measure Circle)) i).quasiMeasurePreserving.ae
      (ae_joint_continuousAt_circleKernel endpoint hm _ (hphase n hn i))
  have hall : ∀ᵐ y : UnitAddTorus (Fin d) ∂volume, ∀ n ∈ s, ∀ i : Fin d,
      ContinuousAt (fun p : ℝ × Circle => circleKernel endpoint m p.1 p.2)
        ((n : ℝ) * τ i, y i) := by
    rw [Finset.eventually_all]
    intro n hn
    exact ae_all_iff.mpr (hc n hn)
  filter_upwards [hall] with y hy
  exact continuousAt_average_of_kernel endpoint m d s τ y hy

lemma ae_joint_continuousAt_errorSq (endpoint : Bool) {m : ℕ} (hm : 200 ≤ m)
    (d : ℕ) (s : Finset ℕ) (τ : Fin d → ℝ)
    (hphase : ∀ n ∈ s, ∀ i, Int.fract ((n : ℝ) * τ i) ≠ 0) :
    ∀ᵐ y : UnitAddTorus (Fin d) ∂volume,
      ContinuousAt (errorSq endpoint m d s) (τ,y) := by
  filter_upwards [ae_joint_continuousAt_average endpoint hm d s τ hphase] with y hy
  exact (hy.sub continuousAt_const).pow 2

end Invariant233.SamplingTests

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingTestLimit
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace Invariant233.SamplingTests

theorem tendsto_integral_errorSq (endpoint : Bool) {m : ℕ} (hm : 200 ≤ m)
    (d : ℕ) (s : Finset ℕ) (q : ℕ → ℕ → ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < d → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    {a : ℕ → Fin d → ℝ} {τ : Fin d → ℝ} (ha : Tendsto a atTop (𝓝 τ))
    (hphase : ∀ n ∈ s, ∀ i, Int.fract ((n : ℝ) * τ i) ≠ 0) :
    Tendsto (fun j => ∫ x : Circle,
      errorSq endpoint m d s (a j, fun i : Fin d => (q j i.val : ℤ) • x)) atTop
      (𝓝 (∫ y : UnitAddTorus (Fin d), errorSq endpoint m d s (τ,y))) := by
  exact CharacterLaws.tendsto_integral_character_phase_of_ae_continuous
    q d hq hmono hgap ha (measurable_errorSq endpoint m d s)
    (ae_joint_continuousAt_errorSq endpoint hm d s τ hphase)
    (sq_nonneg _) (fun z => (errorSq_bounds endpoint (by omega) d s z).2)

theorem eventually_integral_errorSq_lt (endpoint : Bool) {m : ℕ} (hm : 200 ≤ m)
    (d : ℕ) (s : Finset ℕ) (q : ℕ → ℕ → ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < d → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    {a : ℕ → Fin d → ℝ} {τ : Fin d → ℝ} (ha : Tendsto a atTop (𝓝 τ))
    (hphase : ∀ n ∈ s, ∀ i, Int.fract ((n : ℝ) * τ i) ≠ 0)
    {δ : ℝ} (hδ : (∫ y : UnitAddTorus (Fin d), errorSq endpoint m d s (τ,y)) < δ) :
    ∀ᶠ j in atTop, (∫ x : Circle,
      errorSq endpoint m d s (a j, fun i : Fin d => (q j i.val : ℤ) • x)) < δ :=
  (tendsto_integral_errorSq endpoint hm d s q hq hmono hgap ha hphase).eventually_lt_const hδ

theorem eventually_simultaneous_errorSq_lt {ι : Type*} [Finite ι]
    {m : ℕ} (hm : 200 ≤ m) (d : ℕ) (s : ι → Finset ℕ)
    (q : ℕ → ℕ → ℕ) (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < d → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    {a : ℕ → Fin d → ℝ} {τ : Fin d → ℝ} (ha : Tendsto a atTop (𝓝 τ))
    (hphase : ∀ r, ∀ n ∈ s r, ∀ i, Int.fract ((n : ℝ) * τ i) ≠ 0)
    (δ : ι → Bool → ℝ)
    (hδ : ∀ r endpoint, (∫ y : UnitAddTorus (Fin d),
      errorSq endpoint m d (s r) (τ,y)) < δ r endpoint) :
    ∀ᶠ j in atTop, ∀ r endpoint, (∫ x : Circle,
      errorSq endpoint m d (s r) (a j, fun i : Fin d => (q j i.val : ℤ) • x)) <
        δ r endpoint := by
  apply Filter.eventually_all.mpr
  intro r
  apply Filter.eventually_all.mpr
  intro endpoint
  exact eventually_integral_errorSq_lt endpoint hm d (s r) q hq hmono hgap ha
    (hphase r) (hδ r endpoint)

theorem exists_character_sampling_block {ι : Type*} [Finite ι]
    {θ : ℝ} (hθ : Irrational θ) {m : ℕ} (hm : 200 ≤ m)
    (d : ℕ) (s : ι → Finset ℕ) (τ : Fin d → ℝ)
    (hτ : ∀ i, 0 < τ i ∧ τ i < 1)
    (hphase : ∀ r, ∀ n ∈ s r, ∀ i, Int.fract ((n : ℝ) * τ i) ≠ 0)
    (δ : ι → Bool → ℝ)
    (hδ : ∀ r endpoint, (∫ y : UnitAddTorus (Fin d),
      errorSq endpoint m d (s r) (τ,y)) < δ r endpoint)
    (U : Set (Fin d → ℝ)) (hU : U ∈ 𝓝 τ) (R : ℝ)
    {q₀ : ℕ} (hq₀ : 0 < q₀) :
    ∃ q : ℕ → ℕ, q 0 = q₀ ∧ (∀ i, 0 < q i) ∧ StrictMono q ∧
      (∀ i, q i ∣ q (i + 1)) ∧
      (∀ i < d, R ≤ (q (i + 1) : ℝ) / q i) ∧
      (fun i : Fin d => Int.fract ((q (i.val + 1) : ℝ) * θ)) ∈ U ∧
      ∀ r endpoint, (∫ x : Circle, errorSq endpoint m d (s r)
        ((fun i : Fin d => Int.fract ((q (i.val + 1) : ℝ) * θ)),
         (fun i : Fin d => (q (i.val + 1) : ℤ) • x))) < δ r endpoint := by
  classical
  let target : ℕ → ℝ := fun i => if hi : i < d then τ ⟨i,hi⟩ else 1/2
  have ht0 : ∀ i, 0 < target i := by
    intro i
    dsimp [target]
    split_ifs with hi
    · exact (hτ ⟨i,hi⟩).1
    · norm_num
  have ht1 : ∀ i, target i < 1 := by
    intro i
    dsimp [target]
    split_ifs with hi
    · exact (hτ ⟨i,hi⟩).2
    · norm_num
  obtain ⟨q, hzero, hpos, hstrict, hdiv, hgap, hlimit⟩ :=
    PrescribedPhaseRealization.exists_phase_approximation_family hθ target ht0 ht1 hq₀
  let a : ℕ → Fin d → ℝ := fun j i => Int.fract ((q j (i.val + 1) : ℝ) * θ)
  have ha : Tendsto a atTop (𝓝 τ) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [target, dite_eq_left i.isLt] using hlimit i.val
  have htests := eventually_simultaneous_errorSq_lt hm d s
    (fun j i => q j (i+1)) (fun j i => hpos j (i+1))
    (fun j => (hstrict j).monotone.comp (fun i k hik => Nat.add_le_add_right hik 1))
    (fun i _ => hgap (i+1)) ha hphase δ hδ
  have hratios : ∀ᶠ j in atTop, ∀ i ∈ Finset.range d,
      R ≤ (q j (i+1) : ℝ) / q j i := by
    rw [Finset.eventually_all]
    intro i hi
    exact (hgap i).eventually_ge_atTop R
  obtain ⟨j, hjtest, hjU, hjR⟩ := (htests.and ((ha.eventually hU).and hratios)).exists
  refine ⟨q j, hzero j, hpos j, hstrict j, hdiv j, ?_, hjU, hjtest⟩
  intro i hi
  exact hjR i (Finset.mem_range.mpr hi)

end Invariant233.SamplingTests

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_IntegerPhaseWindow
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.ProductPhases

theorem mem_nonzeroIntegerWindow {R : ℝ} {k : ℤ} :
    k ∈ nonzeroIntegerWindow R ↔ k ≠ 0 ∧ |(k : ℝ)| ≤ R := by
  simp only [nonzeroIntegerWindow, Finset.mem_erase, Finset.mem_Icc]
  constructor
  · rintro ⟨hk, hlo, hhi⟩
    refine ⟨hk, abs_le.mpr ⟨?_, Int.le_floor.mp hhi⟩⟩
    have hn : -k ≤ Int.floor R := by omega
    have hh := Int.le_floor.mp hn
    simp only [Int.cast_neg] at hh
    linarith
  · rintro ⟨hk, habs⟩
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    have hn : -k ≤ Int.floor R := Int.le_floor.mpr (by push_cast <;> linarith)
    exact ⟨hk, by omega, Int.le_floor.mpr hhi⟩

theorem card_nonzeroIntegerWindow {R : ℝ} (hR : 0 ≤ R) :
    ((nonzeroIntegerWindow R).card : ℤ) = 2 * Int.floor R := by
  have hf : 0 ≤ Int.floor R := Int.floor_nonneg.mpr hR
  have hz : (0 : ℤ) ∈ Finset.Icc (-Int.floor R) (Int.floor R) := by
    simp only [Finset.mem_Icc]
    omega
  have he := Finset.card_erase_add_one hz
  have he' : ((nonzeroIntegerWindow R).card : ℤ) + 1 =
      ((Finset.Icc (-Int.floor R) (Int.floor R)).card : ℤ) := by
    exact_mod_cast he
  have hI := Int.card_Icc_of_le (a := -Int.floor R) (b := Int.floor R) (by omega)
  omega

theorem card_nonzeroIntegerWindow_le {R : ℝ} (hR : 0 ≤ R) :
    ((nonzeroIntegerWindow R).card : ℝ) ≤ 2 * R := by
  have he : ((nonzeroIntegerWindow R).card : ℝ) = 2 * (Int.floor R : ℝ) := by
    exact_mod_cast card_nonzeroIntegerWindow hR
  rw [he]
  exact mul_le_mul_of_nonneg_left (Int.floor_le R) (by norm_num)

theorem mem_largePhaseTimes {N R : ℝ} (hN : 0 < N) {k : ℤ} :
    k ∈ largePhaseTimes N R ↔ N / 4 ≤ |(k : ℝ)| ∧ |(k : ℝ)| ≤ R := by
  simp only [largePhaseTimes, Finset.mem_filter, mem_nonzeroIntegerWindow]
  constructor
  · rintro ⟨⟨_, hR⟩, hlo⟩
    exact ⟨hlo, hR⟩
  · rintro ⟨hlo, hR⟩
    refine ⟨⟨?_, hR⟩, hlo⟩
    intro hk
    subst k
    norm_num at hlo
    linarith

theorem card_largePhaseTimes_le {N R : ℝ} (hR : 0 ≤ R) :
    ((largePhaseTimes N R).card : ℝ) ≤ 2 * R := by
  apply le_trans _ (card_nonzeroIntegerWindow_le hR)
  unfold largePhaseTimes
  exact_mod_cast Finset.card_filter_le
    (nonzeroIntegerWindow R) (fun k : ℤ => N / 4 ≤ |(k : ℝ)|)

end Invariant233.ProductPhases

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_PhaseFailureSummability
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233.ProductPhases

theorem failureBound_nonneg {m : ℝ} (hm : 0 ≤ m) : 0 ≤ failureBound m := by
  unfold failureBound
  positivity

theorem ten_mul_phaseWidth_le_one {m : ℝ} (hm : 100 ≤ m) :
    10 * m ^ (-19 / 20 : ℝ) ≤ 1 := by
  have hm0 : 0 ≤ m := by linarith
  have hs : (10 : ℝ) ≤ Real.sqrt m := by
    nlinarith [Real.sq_sqrt hm0, Real.sqrt_nonneg m]
  have hb : m ^ (-19 / 20 : ℝ) ≤ (10 : ℝ)⁻¹ := by
    calc
      m ^ (-19 / 20 : ℝ) ≤ m ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (Real.sqrt m)⁻¹ := by rw [Real.rpow_neg hm0, ← Real.sqrt_eq_rpow]
      _ ≤ (10 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hs
  nlinarith

theorem failureBound_eq_exp {m : ℝ} (hm : 0 < m) :
    failureBound m = 2 * Real.exp (-(41 / 400 : ℝ) * m * Real.log m +
      (Real.log 2 + (19 / 20 : ℝ) * Real.log 10) * m) := by
  unfold failureBound
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 10) (Real.rpow_nonneg hm.le _),
    ← Real.rpow_mul hm.le]
  simp only [Real.rpow_def_of_pos hm,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10)]
  rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

theorem eventually_failureBound_le_exp :
    ∀ᶠ m : ℝ in atTop, failureBound m ≤ Real.exp (-m) := by
  let C : ℝ := Real.log 2 + (19 / 20 : ℝ) * Real.log 10
  have hl : ∀ᶠ m : ℝ in atTop,
      (400 / 41 : ℝ) * (C + 2) ≤ Real.log m :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (Real.log 2), hl]
    with m hm hm2 hlog
  rw [failureBound_eq_exp (by linarith)]
  have he : -(41 / 400 : ℝ) * m * Real.log m + C * m ≤ -2 * m := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (show 0 ≤ m by linarith)]
  calc
    2 * Real.exp (-(41 / 400 : ℝ) * m * Real.log m + C * m) =
        Real.exp (Real.log 2 + (-(41 / 400 : ℝ) * m * Real.log m + C * m)) := by
      conv_rhs => rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (-m) := Real.exp_le_exp.mpr (by linarith)

theorem summable_failureBound_of_nat_le {m : ℕ → ℝ}
    (hm : ∀ j : ℕ, (j : ℝ) ≤ m j) (hmnonneg : ∀ j, 0 ≤ m j) :
    Summable (fun j => failureBound (m j)) := by
  have hmtop : Tendsto m atTop atTop :=
    tendsto_atTop_mono hm tendsto_natCast_atTop_atTop
  have hb := hmtop.eventually eventually_failureBound_le_exp
  apply Real.summable_exp_neg_nat.of_norm_bounded_eventually_nat
  filter_upwards [hb] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg (failureBound_nonneg (hmnonneg j))]
  exact hj.trans (Real.exp_le_exp.mpr (neg_le_neg (hm j)))

end Invariant233.ProductPhases

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_LargePhaseAssembly
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductPhases

theorem measure_largePhaseFailure_le {ι : Type*}
    (μ : Measure (ι → ℝ)) (J : Finset ι) (N : ℝ) (hm : 100 ≤ (J.card : ℝ))
    (hind : ∀ k : ℤ, iIndepSet
      (fun i => {θ : ι → ℝ | 1 - Int.fract ((k : ℝ) * θ i) ∉
        Set.Icc ((J.card : ℝ) ^ (-19 / 20 : ℝ))
          (1 - (J.card : ℝ) ^ (-19 / 20 : ℝ))}) μ)
    (hmiss : ∀ k ∈ largePhaseTimes N ((J.card : ℝ) ^ ((4 / 5 : ℝ) * J.card)),
      ∀ i ∈ J, μ {θ : ι → ℝ | 1 - Int.fract ((k : ℝ) * θ i) ∉
        Set.Icc ((J.card : ℝ) ^ (-19 / 20 : ℝ))
          (1 - (J.card : ℝ) ^ (-19 / 20 : ℝ))} ≤
        ENNReal.ofReal (10 * (J.card : ℝ) ^ (-19 / 20 : ℝ))) :
    μ (largePhaseFailure J N) ≤ ENNReal.ofReal (failureBound J.card) := by
  classical
  let m : ℝ := J.card
  let b : ℝ := m ^ (-19 / 20 : ℝ)
  let R : ℝ := m ^ ((4 / 5 : ℝ) * m)
  let q : ℝ := (19 / 20 : ℝ) * m
  let times := largePhaseTimes N R
  let E : ℤ → ι → Set (ι → ℝ) := fun k i =>
    {θ | 1 - Int.fract ((k : ℝ) * θ i) ∉ Set.Icc b (1 - b)}
  have hm0 : 0 ≤ m := by dsimp [m] <;> positivity
  have hb : 0 ≤ b := Real.rpow_nonneg hm0 _
  have hq : 0 ≤ q := by dsimp [q] <;> positivity
  have hp : ENNReal.ofReal (10 * b) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (ten_mul_phaseWidth_le_one hm)
  have hsub : largePhaseFailure J N ⊆
      {θ | ∃ k ∈ times, ∃ t : Finset ι,
        t ⊆ J ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, θ ∈ E k i} := by
    intro θ hθ
    obtain ⟨k, hk, hsmall⟩ := hθ
    obtain ⟨t, ht, hcard, htmiss⟩ :=
      Invariant233.exists_many_misses_of_few_successes J
        (fun i => 1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Icc b (1 - b)) hsmall
    exact ⟨k, hk, t, ht, hcard.le, htmiss⟩
  have hprob := Invariant233.measure_exists_many_independent_events_le μ E J times
    (fun k _ => hind k) hp hmiss q
  have hnum : (times.card : ℝ) *
      ((2 : ℝ) ^ J.card * (10 * b) ^ q) ≤ failureBound m := by
    calc
      (times.card : ℝ) * ((2 : ℝ) ^ J.card * (10 * b) ^ q) ≤
          (2 * R) * ((2 : ℝ) ^ J.card * (10 * b) ^ q) :=
        mul_le_mul_of_nonneg_right (card_largePhaseTimes_le (Real.rpow_nonneg hm0 _))
          (by positivity)
      _ = failureBound m := by
        dsimp [failureBound, R, b, q, m]
        rw [Real.rpow_natCast]
        ring
  calc
    μ (largePhaseFailure J N) ≤ μ {θ | ∃ k ∈ times, ∃ t : Finset ι,
      t ⊆ J ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, θ ∈ E k i} := measure_mono hsub
    _ ≤ (times.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ J.card *
      ENNReal.ofReal (10 * b) ^ q) := hprob
    _ = ENNReal.ofReal ((times.card : ℝ) * ((2 : ℝ) ^ J.card * (10 * b) ^ q)) := by
      rw [ENNReal.ofReal_mul (p := (times.card : ℝ)) (Nat.cast_nonneg _),
        ENNReal.ofReal_mul (p := (2 : ℝ) ^ J.card) (by positivity),
        ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hq]
      simp
    _ ≤ ENNReal.ofReal (failureBound m) := ENNReal.ofReal_le_ofReal hnum

theorem iIndepSet_phaseMiss_infinitePi {ι : Type*} (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (b : ℝ) (k : ℤ) :
    iIndepSet (fun i => {θ : ι → ℝ | 1 - Int.fract ((k : ℝ) * θ i) ∉
      Set.Icc b (1 - b)}) (Measure.infinitePi ν) := by
  have hA : MeasurableSet {x : ℝ | 1 - Int.fract ((k : ℝ) * x) ∉
      Set.Icc b (1 - b)} := by
    exact ((measurable_const.sub (measurable_const.mul measurable_id).fract)
      measurableSet_Icc).compl
  have hm : ∀ i : ι, MeasurableSet {θ : ι → ℝ |
      1 - Int.fract ((k : ℝ) * θ i) ∉ Set.Icc b (1 - b)} :=
    fun i => hA.preimage (measurable_pi_apply i)
  apply (iIndepSet_iff_meas_biInter hm).mpr
  intro S
  have hi : iIndepFun (fun i (θ : ι → ℝ) => θ i) (Measure.infinitePi ν) :=
    iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  exact hi.measure_inter_preimage_eq_mul S (fun _ _ => hA)

theorem infinitePi_phaseMiss_eq {ι : Type*} (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (b : ℝ) (k : ℤ) (i : ι) :
    (Measure.infinitePi ν) {θ : ι → ℝ |
      1 - Int.fract ((k : ℝ) * θ i) ∉ Set.Icc b (1 - b)} =
      ν i {x : ℝ | 1 - Int.fract ((k : ℝ) * x) ∉ Set.Icc b (1 - b)} := by
  have hA : MeasurableSet {x : ℝ | 1 - Int.fract ((k : ℝ) * x) ∉
      Set.Icc b (1 - b)} := by
    exact ((measurable_const.sub (measurable_const.mul measurable_id).fract)
      measurableSet_Icc).compl
  simpa only [Measure.infinitePi_map_eval, Set.preimage_ofPred_eq] using
    (Measure.map_apply (μ := Measure.infinitePi ν)
      (f := fun θ : ι → ℝ => θ i) (measurable_pi_apply i) hA).symm

end Invariant233.ProductPhases

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_StrictPhaseStability
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped Topology

namespace Invariant233.ProductPhases

theorem threshold_fiber_countable {k : ℝ} (hk : k ≠ 0) (c : ℝ) :
    Set.Countable {x : ℝ | 1 - Int.fract (k * x) = c} := by
  apply (Set.countable_range (fun n : ℤ => ((n : ℝ) + 1 - c) / k)).mono
  intro x hx
  refine ⟨Int.floor (k * x), ?_⟩
  apply (div_eq_iff hk).mpr
  change 1 - (k * x - (Int.floor (k * x) : ℝ)) = c at hx
  nlinarith

theorem ae_threshold_ne (μ : Measure ℝ) [NullSingletonClass μ]
    {k : ℝ} (hk : k ≠ 0) (c : ℝ) :
    ∀ᵐ x ∂μ, 1 - Int.fract (k * x) ≠ c :=
  (threshold_fiber_countable hk c).ae_notMem μ

theorem threshold_Ioo_ae_eq_Icc (μ : Measure ℝ) [NullSingletonClass μ]
    {k : ℝ} (hk : k ≠ 0) (b : ℝ) :
    {x : ℝ | 1 - Int.fract (k * x) ∈ Set.Ioo b (1 - b)} =ᵐ[μ]
      {x : ℝ | 1 - Int.fract (k * x) ∈ Set.Icc b (1 - b)} := by
  apply Filter.eventuallyEq_set.mpr
  filter_upwards [ae_threshold_ne μ hk b, ae_threshold_ne μ hk (1 - b)]
    with x hlo hhi
  change (b < 1 - Int.fract (k * x) ∧ 1 - Int.fract (k * x) < 1 - b) ↔
    (b ≤ 1 - Int.fract (k * x) ∧ 1 - Int.fract (k * x) ≤ 1 - b)
  constructor
  · exact fun h => ⟨h.1.le, h.2.le⟩
  · exact fun h => ⟨lt_of_le_of_ne h.1 hlo.symm, lt_of_le_of_ne h.2 hhi⟩

theorem continuousAt_threshold_of_mem_Ioo {b k x : ℝ} (hb : 0 < b)
    (hx : 1 - Int.fract (k * x) ∈ Set.Ioo b (1 - b)) :
    ContinuousAt (fun y : ℝ => 1 - Int.fract (k * y)) x := by
  have hnotint : k * x ≠ (Int.floor (k * x) : ℝ) := by
    intro he
    have hf : Int.fract (k * x) = 0 := by exact sub_eq_zero.mpr he
    rw [hf] at hx
    have := hx.2
    linarith
  exact continuousAt_const.sub ((continuousAt_fract hnotint).comp
    (continuous_const.mul continuous_id).continuousAt)

theorem eventually_threshold_mem_Ioo {b k x : ℝ} (hb : 0 < b)
    (hx : 1 - Int.fract (k * x) ∈ Set.Ioo b (1 - b)) :
    ∀ᶠ y in 𝓝 x, 1 - Int.fract (k * y) ∈ Set.Ioo b (1 - b) :=
  (continuousAt_threshold_of_mem_Ioo hb hx).eventually_mem (isOpen_Ioo.mem_nhds hx)

theorem eventually_finite_phase_tests {ι : Type*} (powers : Finset ℤ)
    (witness : ℤ → Finset ι) (θ : ι → ℝ) {b : ℝ} (hb : 0 < b)
    (hgood : ∀ k ∈ powers, ∀ i ∈ witness k,
      1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Ioo b (1 - b)) :
    ∀ᶠ φ in 𝓝 θ, ∀ k ∈ powers, ∀ i ∈ witness k,
      1 - Int.fract ((k : ℝ) * φ i) ∈ Set.Ioo b (1 - b) := by
  apply (Filter.eventually_all_finset powers).mpr
  intro k hk
  apply (Filter.eventually_all_finset (witness k)).mpr
  intro i hi
  exact (continuous_apply i).continuousAt.eventually
    (eventually_threshold_mem_Ioo hb (hgood k hk i hi))

end Invariant233.ProductPhases

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_StrictPhaseTrials
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductPhases

theorem strictPhaseGoodCount_ae_eq {ι : Type*} (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] [∀ i, NullSingletonClass (ν i)]
    (J : Finset ι) (b : ℝ) (k : ℤ) (hk : k ≠ 0) :
    ∀ᵐ θ ∂Measure.infinitePi ν, strictPhaseGoodCount J b k θ = phaseGoodCount J b k θ := by
  classical
  have hcoord : ∀ i : ι, ∀ᵐ θ ∂Measure.infinitePi ν,
      (1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Ioo b (1 - b) ↔
        1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Icc b (1 - b)) := by
    intro i
    have hi : ∀ᵐ x ∂(Measure.infinitePi ν).map (fun θ : ι → ℝ => θ i),
        (1 - Int.fract ((k : ℝ) * x) ∈ Set.Ioo b (1 - b) ↔
          1 - Int.fract ((k : ℝ) * x) ∈ Set.Icc b (1 - b)) := by
      rw [Measure.infinitePi_map_eval]
      exact Filter.eventuallyEq_set.mp (threshold_Ioo_ae_eq_Icc (ν i) (by exact_mod_cast hk) b)
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hi
  filter_upwards [(Filter.eventually_all_finset J).mpr (fun i _ => hcoord i)] with θ hθ
  unfold strictPhaseGoodCount phaseGoodCount
  congr 1
  ext i
  simp only [Finset.mem_filter]
  exact and_congr_right fun hi => hθ i hi

theorem strictLargePhaseFailure_ae_eq {ι : Type*} (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] [∀ i, NullSingletonClass (ν i)]
    (J : Finset ι) {N : ℝ} (hN : 0 < N) :
    strictLargePhaseFailure J N =ᵐ[Measure.infinitePi ν] largePhaseFailure J N := by
  let times := largePhaseTimes N ((J.card : ℝ) ^ ((4 / 5 : ℝ) * J.card))
  have hc : ∀ᵐ θ ∂Measure.infinitePi ν, ∀ k ∈ times,
      strictPhaseGoodCount J ((J.card : ℝ) ^ (-19 / 20 : ℝ)) k θ =
        phaseGoodCount J ((J.card : ℝ) ^ (-19 / 20 : ℝ)) k θ := by
    apply (Filter.eventually_all_finset times).mpr
    intro k hk
    apply strictPhaseGoodCount_ae_eq ν J _ k
    intro hzero
    have hh := ((mem_largePhaseTimes hN).mp hk).1
    simp only [hzero, Int.cast_zero, abs_zero] at hh
    linarith
  apply Filter.eventuallyEq_set.mpr
  filter_upwards [hc] with θ hθ
  change (∃ k ∈ times, (strictPhaseGoodCount J _ k θ : ℝ) < (J.card : ℝ) / 20) ↔
    (∃ k ∈ times, (phaseGoodCount J _ k θ : ℝ) < (J.card : ℝ) / 20)
  constructor
  · rintro ⟨k, hk, hsmall⟩
    exact ⟨k, hk, by simpa only [hθ k hk] using hsmall⟩
  · rintro ⟨k, hk, hsmall⟩
    exact ⟨k, hk, by simpa only [hθ k hk] using hsmall⟩

theorem not_mem_strictLargePhaseFailure_iff {ι : Type*} (J : Finset ι)
    {N : ℝ} (hN : 0 < N) (θ : ι → ℝ) :
    θ ∉ strictLargePhaseFailure J N ↔ strictLargePhaseCondition J N θ := by
  simp only [strictLargePhaseFailure, Set.mem_ofPred_eq, not_exists, not_and,
    not_lt, strictLargePhaseCondition, mem_largePhaseTimes hN]
  constructor
  · intro h k hlo hhi
    exact h k ⟨hlo, hhi⟩
  · intro h k hk
    exact h k hk.1 hk.2

theorem uniformProduct_measure_strictLargePhaseFailure_le {ι : Type*}
    (S : ι → ℝ) (hS : ∀ i, 0 < S i) (J : Finset ι)
    {N : ℝ} (hN : 0 < N) (hm : 100 ≤ (J.card : ℝ))
    (hblock : ∀ i ∈ J, S i = N) :
    (Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Set.Icc (1 / S i) (2 / S i)))) (strictLargePhaseFailure J N) ≤
      ENNReal.ofReal (failureBound J.card) := by
  let ν : ι → Measure ℝ := fun i =>
    ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))
  let (i : ι) : IsProbabilityMeasure (ν i) :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) (hS i))
  let (i : ι) : NullSingletonClass (ν i) :=
    InvariantProjection.IndependentAngles.intervalLaw_nullSingletonClass _ _
  change (Measure.infinitePi ν) (strictLargePhaseFailure J N) ≤ _
  rw [measure_congr (strictLargePhaseFailure_ae_eq ν J hN)]
  apply measure_largePhaseFailure_le (Measure.infinitePi ν) J N hm
  · exact fun k => iIndepSet_phaseMiss_infinitePi ν _ k
  · intro k hk i hi
    rw [infinitePi_phaseMiss_eq ν _ k i]
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top (ν i) _) (by positivity)).mpr
    change (ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))).real
      {x : ℝ | 1 - Int.fract ((k : ℝ) * x) ∉
        Set.Icc ((J.card : ℝ) ^ (-19 / 20 : ℝ))
          (1 - (J.card : ℝ) ^ (-19 / 20 : ℝ))} ≤ _
    rw [hblock i hi]
    exact Invariant233.ModuloIntervalMeasure.uniform_angle_threshold_miss_le
      hN ((mem_largePhaseTimes hN).mp hk).1 (by positivity)

theorem intervalProduct_ae_strict_bounds {ι : Type*} [Countable ι]
    (S : ι → ℝ) (hS : ∀ i, 0 < S i) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
        (Set.Icc (1 / S i) (2 / S i))),
      ∀ i, θ i ∈ Set.Ioo (1 / S i) (2 / S i) := by
  let ν : ι → Measure ℝ := fun i =>
    ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))
  let (i : ι) : IsProbabilityMeasure (ν i) :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) (hS i))
  let (i : ι) : NullSingletonClass (ν i) :=
    InvariantProjection.IndependentAngles.intervalLaw_nullSingletonClass _ _
  apply ae_all_iff.mpr
  intro i
  have hi : ∀ᵐ x ∂ν i, x ∈ Set.Ioo (1 / S i) (2 / S i) := by
    have hc : ∀ᵐ x ∂ν i, x ∈ Set.Icc (1 / S i) (2 / S i) :=
      ae_cond_mem measurableSet_Icc
    filter_upwards [hc, (ν i).ae_ne (1 / S i), (ν i).ae_ne (2 / S i)] with x hx hlo hhi
    exact ⟨lt_of_le_of_ne hx.1 hlo.symm, lt_of_le_of_ne hx.2 hhi⟩
  have hmap : ∀ᵐ x ∂(Measure.infinitePi ν).map (fun θ : ι → ℝ => θ i),
      x ∈ Set.Ioo (1 / S i) (2 / S i) := by
    rw [Measure.infinitePi_map_eval]
    exact hi
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hmap

theorem eventually_strictLargePhaseCondition {ι : Type*} (J : Finset ι)
    (hJ : 0 < J.card) {N : ℝ} (hN : 0 < N) (θ : ι → ℝ)
    (hθ : strictLargePhaseCondition J N θ) :
    ∀ᶠ φ in 𝓝 θ, strictLargePhaseCondition J N φ := by
  classical
  let b : ℝ := (J.card : ℝ) ^ (-19 / 20 : ℝ)
  let times := largePhaseTimes N ((J.card : ℝ) ^ ((4 / 5 : ℝ) * J.card))
  let witness : ℤ → Finset ι := fun k =>
    J.filter (fun i => 1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Ioo b (1 - b))
  have hb : 0 < b := Real.rpow_pos_of_pos (by exact_mod_cast hJ) _
  have htests := eventually_finite_phase_tests times witness θ hb
    (fun _ _ _ hi => (Finset.mem_filter.mp hi).2)
  filter_upwards [htests] with φ hφ
  intro k hlo hhi
  have hk : k ∈ times := (mem_largePhaseTimes hN).mpr ⟨hlo, hhi⟩
  have hc : (J.card : ℝ) / 20 ≤ ((witness k).card : ℝ) := hθ k hlo hhi
  have hsub : witness k ⊆ J.filter
      (fun i => 1 - Int.fract ((k : ℝ) * φ i) ∈ Set.Ioo b (1 - b)) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, hφ k hk i hi⟩
  apply hc.trans
  change ((witness k).card : ℝ) ≤ ((J.filter
    (fun i => 1 - Int.fract ((k : ℝ) * φ i) ∈ Set.Ioo b (1 - b))).card : ℝ)
  exact_mod_cast Finset.card_le_card hsub

end Invariant233.ProductPhases

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_NonresonantPhaseTrials
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductPhases

theorem infinitePi_ae_nonresonant {ι : Type*} [Countable ι]
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, NullSingletonClass (ν i)] :
    ∀ᵐ θ ∂Measure.infinitePi ν, ∀ i, ∀ k : ℤ, k ≠ 0 →
      Int.fract ((k : ℝ) * θ i) ≠ 0 := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro k
  by_cases hk : k = 0
  · exact Filter.Eventually.of_forall (fun _ h => (h hk).elim)
  have hi : ∀ᵐ x ∂ν i, Int.fract ((k : ℝ) * x) ≠ 0 := by
    filter_upwards [ae_threshold_ne (ν i) (k := (k : ℝ)) (by exact_mod_cast hk) 1] with x hx
    intro hz
    exact hx (by simp only [hz, sub_zero])
  have hmap : ∀ᵐ x ∂(Measure.infinitePi ν).map (fun θ : ι → ℝ => θ i),
      Int.fract ((k : ℝ) * x) ≠ 0 := by
    rw [Measure.infinitePi_map_eval]
    exact hi
  exact (ae_of_ae_map (measurable_pi_apply i).aemeasurable hmap).mono (fun _ h _ => h)

end Invariant233.ProductPhases

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_TrialSamplingSelection
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.TrialSampling

lemma phaseLaw_probability (m : ℕ) {N : ℝ} (hN : 0 < N) :
    IsProbabilityMeasure (phaseLaw m N) := by
  let : IsProbabilityMeasure
      (ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))) :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) hN)
  dsimp [phaseLaw]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma measurable_kernel_pair (m : ℕ) :
    Measurable (fun p : ℝ × ℝ => CircleParameterData.kernel m p.1 p.2) := by
  have hd : Measurable (fun p : ℝ × ℝ => CircleParameterData.delta p.1) :=
    measurable_fst.fract.min (measurable_const.sub measurable_fst.fract)
  unfold CircleParameterData.kernel
  apply Measurable.ite
  · exact (measurableSet_le measurable_const hd).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd (measurable_const.mul hd)))
  · exact measurable_const.div (measurable_const.mul hd)
  · exact measurable_const

lemma measurable_orientedKernel_pair (m : ℕ) (endpoint : Bool) :
    Measurable (fun p : ℝ × ℝ =>
      CircleParameterData.orientedKernel endpoint m p.1 p.2) := by
  cases endpoint
  · exact measurable_kernel_pair m
  · exact (measurable_kernel_pair m).comp
      ((measurable_fst.sub measurable_snd).prodMk measurable_snd)

lemma measurable_average_pair (m : ℕ) (samples : Finset ℕ) (endpoint : Bool) :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → Circle) =>
      average m samples endpoint p.1 p.2) := by
  unfold average
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro n hn
  apply Finset.measurable_prod
  intro i hi
  have hz : Measurable (fun p : (Fin m → ℝ) × (Fin m → Circle) =>
      CircleParameterData.rep (p.2 i)) :=
    CircleParameterData.measurable_rep.comp
      ((show Measurable (fun z : Fin m → Circle => z i) from measurable_pi_apply i).comp
        measurable_snd)
  have hv : Measurable (fun p : (Fin m → ℝ) × (Fin m → Circle) =>
      Int.fract ((n : ℝ) * p.1 i)) :=
    (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).fract
  exact (measurable_orientedKernel_pair m endpoint).comp (hz.prodMk hv)

lemma measurable_squaredError (m : ℕ) (samples : Finset ℕ) (endpoint : Bool) :
    Measurable (squaredError m samples endpoint) := by
  exact (((measurable_average_pair m samples endpoint).sub_const 1).pow_const 2).ennreal_ofReal.lintegral_prod_right'

theorem exists_strict_trials_of_moment_budget
    (m : ℕ) {N : ℝ} (hN : 0 < N) (hm : 100 ≤ (m : ℝ))
    {ι : Type*} (s : Finset ι) (samples : ι → Finset ℕ)
    {ε δ : ℝ≥0∞} (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞)
    (hmoment : ∀ t ∈ s, ∀ endpoint : Bool,
      (∫⁻ phase, squaredError m (samples t) endpoint phase ∂phaseLaw m N) ≤ δ)
    (hbudget : ENNReal.ofReal (ProductPhases.failureBound m) +
      (2 * s.card : ℝ≥0∞) * (δ / ε) < 1) :
    ∃ phase : Fin m → ℝ,
      (∀ i, phase i ∈ Set.Ioo (1 / N) (2 / N)) ∧
      (∀ i, ∀ k : ℤ, k ≠ 0 → Int.fract ((k : ℝ) * phase i) ≠ 0) ∧
      ProductPhases.strictLargePhaseCondition Finset.univ N phase ∧
      ∀ t ∈ s, ∀ endpoint : Bool, squaredError m (samples t) endpoint phase < ε := by
  classical
  let ν : Fin m → Measure ℝ := fun _ =>
    ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))
  let : IsProbabilityMeasure
      (ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))) :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) hN)
  let : NullSingletonClass
      (ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))) :=
    InvariantProjection.IndependentAngles.intervalLaw_nullSingletonClass _ _
  let : IsProbabilityMeasure (phaseLaw m N) := phaseLaw_probability m hN
  have hbad : phaseLaw m N
      (ProductPhases.strictLargePhaseFailure (Finset.univ : Finset (Fin m)) N) ≤
      ENNReal.ofReal (ProductPhases.failureBound m) := by
    simpa only [phaseLaw, Finset.card_univ, Fintype.card_fin] using
      ProductPhases.uniformProduct_measure_strictLargePhaseFailure_le
        (fun _ : Fin m => N) (fun _ => hN) Finset.univ hN
        (by simpa only [Finset.card_univ, Fintype.card_fin] using hm) (fun _ _ => rfl)
  have hP := (ProductPhases.intervalProduct_ae_strict_bounds
      (fun _ : Fin m => N) (fun _ => hN)).and
    (ProductPhases.infinitePi_ae_nonresonant ν)
  obtain ⟨phase, hphase, hspread, htests⟩ :=
    Invariant233.exists_finite_tests_of_uniform_expectation_bound
      (phaseLaw m N) (s.product (Finset.univ : Finset Bool))
      (fun t => squaredError m (samples t.1) t.2)
      (ProductPhases.strictLargePhaseFailure Finset.univ N) hε0 hεtop
      (fun t _ => (measurable_squaredError m (samples t.1) t.2).aemeasurable)
      (fun t ht => hmoment t.1 (Finset.mem_product.mp ht).1 t.2)
      hbad (by simpa [Finset.card_product, mul_comm] using hbudget)
      _ hP
  refine ⟨phase, hphase.1, hphase.2,
    (ProductPhases.not_mem_strictLargePhaseFailure_iff Finset.univ hN phase).mp hspread, ?_⟩
  intro t ht endpoint
  exact htests (t, endpoint) (Finset.mem_product.mpr ⟨ht, Finset.mem_univ _⟩)

lemma tendsto_failureBound_nat :
    Tendsto (fun m : ℕ => ENNReal.ofReal (ProductPhases.failureBound m)) atTop (𝓝 0) := by
  have hs := ProductPhases.summable_failureBound_of_nat_le
    (m := fun n : ℕ => (n : ℝ)) (fun _ => le_rfl) (fun n => Nat.cast_nonneg n)
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hs.tendsto_atTop_zero

end Invariant233.TrialSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingTestTrialBridge
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.SamplingTests

lemma squaredError_eq_lintegral (endpoint : Bool) (m : ℕ) (s : Finset ℕ)
    (τ : Fin m → ℝ) :
    TrialSampling.squaredError m s endpoint τ =
      ∫⁻ y : UnitAddTorus (Fin m), ENNReal.ofReal (errorSq endpoint m m s (τ,y)) := rfl

lemma integrable_errorSq_comp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (endpoint : Bool) {m : ℕ} (hm : 0 < m)
    (d : ℕ) (s : Finset ℕ) (a : X → (Fin d → ℝ) × UnitAddTorus (Fin d))
    (ha : Measurable a) : Integrable (fun x => errorSq endpoint m d s (a x)) μ := by
  apply Integrable.of_bound ((measurable_errorSq endpoint m d s).comp ha).aestronglyMeasurable
    ((((m : ℝ)^2 / CircleParameterData.kernelWidth m) ^ d + 1) ^ 2)
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, Function.comp_apply] using (errorSq_bounds endpoint hm d s (a x)).2

lemma squaredError_eq_ofReal_integral (endpoint : Bool) {m : ℕ} (hm : 0 < m)
    (s : Finset ℕ) (τ : Fin m → ℝ) :
    TrialSampling.squaredError m s endpoint τ =
      ENNReal.ofReal (∫ y : UnitAddTorus (Fin m), errorSq endpoint m m s (τ,y)) := by
  let : IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin m))) :=
    (CharacterLaws.torusHaar m).property
  rw [squaredError_eq_lintegral]
  symm
  exact ofReal_integral_eq_lintegral_ofReal
    (integrable_errorSq_comp volume endpoint hm m s (fun y => (τ,y))
      (measurable_const.prodMk measurable_id))
    (Filter.Eventually.of_forall fun y => (errorSq_bounds endpoint hm m s (τ,y)).1)

lemma eLpNorm_error_sq_eq_ofReal_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (endpoint : Bool) {m : ℕ} (hm : 0 < m)
    (d : ℕ) (s : Finset ℕ) (a : X → (Fin d → ℝ) × UnitAddTorus (Fin d))
    (ha : Measurable a) :
    eLpNorm (fun x => average endpoint m d s (a x) - 1) 2 μ ^ 2 =
      ENNReal.ofReal (∫ x, errorSq endpoint m d s (a x) ∂μ) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral
    (f := fun x => average endpoint m d s (a x) - 1) (μ := μ)
    (p := (2 : NNReal)) (by norm_num)
  norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at h
  rw [h, ofReal_integral_eq_lintegral_ofReal
    (integrable_errorSq_comp μ endpoint hm d s a ha)
    (Filter.Eventually.of_forall fun x => (errorSq_bounds endpoint hm d s (a x)).1)]
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rfl

lemma eLpNorm_error_lt_iff_integral_lt {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (endpoint : Bool) {m : ℕ} (hm : 0 < m)
    (d : ℕ) (s : Finset ℕ) (a : X → (Fin d → ℝ) × UnitAddTorus (Fin d))
    (ha : Measurable a) {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun x => average endpoint m d s (a x) - 1) 2 μ < ENNReal.ofReal r ↔
      (∫ x, errorSq endpoint m d s (a x) ∂μ) < r ^ 2 := by
  have hpow := ENNReal.rpow_lt_rpow_iff
    (x := eLpNorm (fun x => average endpoint m d s (a x) - 1) 2 μ)
    (y := ENNReal.ofReal r) (z := (2 : ℝ)) (by norm_num)
  rw [ENNReal.rpow_two, ENNReal.rpow_two,
    eLpNorm_error_sq_eq_ofReal_integral μ endpoint hm d s a ha,
    ← ENNReal.ofReal_pow hr.le] at hpow
  rw [ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hr)] at hpow
  exact hpow.symm

theorem exists_character_sampling_block_L2 {ι : Type*} [Finite ι]
    {θ : ℝ} (hθ : Irrational θ) {m : ℕ} (hm : 200 ≤ m)
    (s : ι → Finset ℕ) (τ : Fin m → ℝ) (hτ : ∀ i, 0 < τ i ∧ τ i < 1)
    (hphase : ∀ r, ∀ n ∈ s r, ∀ i, Int.fract ((n : ℝ) * τ i) ≠ 0)
    (ρ : ι → Bool → ℝ) (hρ : ∀ r endpoint, 0 < ρ r endpoint)
    (htests : ∀ r endpoint, TrialSampling.squaredError m (s r) endpoint τ <
      ENNReal.ofReal ((ρ r endpoint) ^ 2))
    (U : Set (Fin m → ℝ)) (hU : U ∈ 𝓝 τ) (R : ℝ)
    {q₀ : ℕ} (hq₀ : 0 < q₀) :
    ∃ q : ℕ → ℕ, q 0 = q₀ ∧ (∀ i, 0 < q i) ∧ StrictMono q ∧
      (∀ i, q i ∣ q (i + 1)) ∧
      (∀ i < m, R ≤ (q (i + 1) : ℝ) / q i) ∧
      (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)) ∈ U ∧
      ∀ r endpoint, eLpNorm (fun x : Circle =>
        TrialSampling.average m (s r) endpoint
          (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ))
          (fun i : Fin m => (q (i.val + 1) : ℤ) • x) - 1) 2 circleMeasure <
            ENNReal.ofReal (ρ r endpoint) := by
  have hreal (r : ι) (endpoint : Bool) :
      (∫ y : UnitAddTorus (Fin m), errorSq endpoint m m (s r) (τ,y)) <
        (ρ r endpoint)^2 := by
    have h := htests r endpoint
    rw [squaredError_eq_ofReal_integral endpoint (by omega)] at h
    exact (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos (hρ r endpoint))).mp h
  obtain ⟨q, hzero, hpos, hstrict, hdiv, hgap, hUq, hsq⟩ :=
    exists_character_sampling_block hθ hm m s τ hτ hphase
      (fun r e => (ρ r e)^2) hreal U hU R hq₀
  refine ⟨q, hzero, hpos, hstrict, hdiv, hgap, hUq, ?_⟩
  intro r endpoint
  have hmap : Measurable (fun x : Circle =>
      ((fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)),
       (fun i : Fin m => (q (i.val + 1) : ℤ) • x))) := by fun_prop
  exact (eLpNorm_error_lt_iff_integral_lt volume endpoint (by omega) m (s r)
    _ hmap (hρ r endpoint)).mpr (hsq r endpoint)

end Invariant233.SamplingTests

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CharacterSamplingStage
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology

namespace Invariant233.SamplingTests

theorem exists_character_stage_of_moment_budget
    {ι : Type*} [Fintype ι] {θ : ℝ} (hθ : Irrational θ)
    {m : ℕ} (hm : 200 ≤ m) {N : ℝ} (hN : 2 < N)
    (samples : ι → Finset ℕ) (hpositive : ∀ r, ∀ n ∈ samples r, 0 < n)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ≥0∞}
    (hmoment : ∀ r endpoint, (∫⁻ phase,
      TrialSampling.squaredError m (samples r) endpoint phase ∂TrialSampling.phaseLaw m N) ≤ δ)
    (hbudget : ENNReal.ofReal (ProductPhases.failureBound m) +
      (2 * Fintype.card ι : ℝ≥0∞) * (δ / ENNReal.ofReal (ρ ^ 2)) < 1)
    (R : ℝ) {q₀ : ℕ} (hq₀ : 0 < q₀) :
    ∃ q : ℕ → ℕ, q 0 = q₀ ∧ (∀ i, 0 < q i) ∧ StrictMono q ∧
      (∀ i, q i ∣ q (i + 1)) ∧
      (∀ i < m, R ≤ (q (i + 1) : ℝ) / q i) ∧
      (∀ i : Fin m, Int.fract ((q (i.val + 1) : ℝ) * θ) ∈ Ioo (1/N) (2/N)) ∧
      ProductPhases.strictLargePhaseCondition Finset.univ N
        (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)) ∧
      ∀ r endpoint, eLpNorm (fun x : Circle =>
        TrialSampling.average m (samples r) endpoint
          (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ))
          (fun i : Fin m => (q (i.val + 1) : ℤ) • x) - 1) 2 circleMeasure <
            ENNReal.ofReal ρ := by
  classical
  have hNpos : 0 < N := by linarith
  have hm100 : (100 : ℝ) ≤ m := by
    have hmR : (200 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  obtain ⟨τ, hbox, hnonres, hspread, htests⟩ :=
    TrialSampling.exists_strict_trials_of_moment_budget m hNpos
      hm100
      (Finset.univ : Finset ι) samples
      (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hρ))) ENNReal.ofReal_ne_top
      (fun r _ endpoint => hmoment r endpoint) (by simpa using hbudget)
  have hτ : ∀ i, 0 < τ i ∧ τ i < 1 := by
    intro i
    exact ⟨(one_div_pos.mpr hNpos).trans (hbox i).1,
      (hbox i).2.trans ((div_lt_one hNpos).mpr hN)⟩
  have hphase : ∀ r, ∀ n ∈ samples r, ∀ i, Int.fract ((n : ℝ) * τ i) ≠ 0 := by
    intro r n hn i
    exact hnonres i (n : ℤ) (by exact_mod_cast (hpositive r n hn).ne')
  let U : Set (Fin m → ℝ) := {a | (∀ i, a i ∈ Ioo (1/N) (2/N)) ∧
    ProductPhases.strictLargePhaseCondition Finset.univ N a}
  have hU : U ∈ 𝓝 τ := by
    have hb : ∀ᶠ a in 𝓝 τ, ∀ i : Fin m, a i ∈ Ioo (1/N) (2/N) := by
      apply Filter.eventually_all.mpr
      intro i
      exact (continuous_apply i).continuousAt.eventually_mem (isOpen_Ioo.mem_nhds (hbox i))
    have hs := ProductPhases.eventually_strictLargePhaseCondition
      (Finset.univ : Finset (Fin m)) (by simpa using (show 0 < m by omega)) hNpos τ hspread
    exact hb.and hs
  obtain ⟨q, hzero, hpos, hstrict, hdiv, hgap, hUq, hnorm⟩ :=
    exists_character_sampling_block_L2 hθ hm samples τ hτ hphase
      (fun _ _ => ρ) (fun _ _ => hρ) (fun r e => htests r (Finset.mem_univ r) e)
      U hU R hq₀
  exact ⟨q, hzero, hpos, hstrict, hdiv, hgap, hUq.1, hUq.2, hnorm⟩

end Invariant233.SamplingTests

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingAsymptotics
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233.SamplingAsymptotics

theorem tendsto_pow_self_of_tendsto_zero {a : ℕ → ℝ}
    (ha : ∀ᶠ n in atTop, 0 ≤ a n) (hlim : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => (a n) ^ n) atTop (𝓝 0) := by
  have hu : ∀ᶠ n in atTop, a n ≤ (1 / 2 : ℝ) :=
    hlim.eventually_le_const (by norm_num)
  apply squeeze_zero' _ _
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1))
  · filter_upwards [ha] with n hn using pow_nonneg hn n
  · filter_upwards [ha, hu] with n hn hnu
    exact pow_le_pow_left₀ hn hnu n

theorem tendsto_logarithmic_diagonal (C a b : ℝ) (hC : 0 ≤ C) (hab : a < b) :
    Tendsto (fun n : ℕ =>
      (C * (n : ℝ) ^ a * Real.log n) ^ n / (n : ℝ) ^ (b * n))
      atTop (𝓝 0) := by
  let r : ℕ → ℝ := fun n => C * Real.log n / (n : ℝ) ^ (b - a)
  have hr : Tendsto r atTop (𝓝 0) := by
    have h := ((isLittleO_log_rpow_atTop (sub_pos.mpr hab)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [r, mul_div_assoc] using h.const_mul C
  have hrnonneg : ∀ᶠ n in atTop, 0 ≤ r n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg (mul_nonneg hC (Real.log_nonneg hnreal))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  apply (tendsto_pow_self_of_tendsto_zero hrnonneg hr).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.rpow_mul_natCast hnpos.le, ← div_pow]
  congr 1
  dsimp [r]
  rw [Real.rpow_sub hnpos]
  field_simp

theorem tendsto_source_diagonal :
    Tendsto (fun n : ℕ =>
      (8 * (n : ℝ) ^ (3 / 5 : ℝ) * Real.log n) ^ n /
        (n : ℝ) ^ ((69 / 100 : ℝ) * n)) atTop (𝓝 0) :=
  tendsto_logarithmic_diagonal 8 (3 / 5) (69 / 100) (by norm_num) (by norm_num)

theorem tendsto_dimension_mul_rpow {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => (n : ℝ) * (n : ℝ) ^ (-r)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hr)).comp
    tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  change (n : ℝ) ^ (-(r - 1)) = _
  rw [show -(r - 1) = 1 + -r by ring, Real.rpow_add hnpos, Real.rpow_one]

theorem tendsto_one_add_pow {a : ℕ → ℝ}
    (ha : ∀ᶠ n in atTop, 0 ≤ a n)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 0)) :
    Tendsto (fun n => (1 + a n) ^ n) atTop (𝓝 1) := by
  have he : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * a n)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using
      (Real.continuous_exp.tendsto 0).comp hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
  · filter_upwards [ha] with n hn
    exact one_le_pow₀ (by linarith : 1 ≤ 1 + a n)
  · filter_upwards [ha] with n hn
    calc
      (1 + a n) ^ n ≤ (Real.exp (a n)) ^ n :=
        pow_le_pow_left₀ (by linarith) (by simpa [add_comm] using Real.add_one_le_exp (a n)) n
      _ = Real.exp ((n : ℝ) * a n) := (Real.exp_nat_mul _ _).symm

theorem tendsto_one_sub_pow {a : ℕ → ℝ}
    (ha : ∀ᶠ n in atTop, a n ∈ Set.Icc 0 1)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 0)) :
    Tendsto (fun n => (1 - a n) ^ n) atTop (𝓝 1) := by
  have hl : Tendsto (fun n : ℕ => 1 - (n : ℝ) * a n) atTop (𝓝 1) := by
    simpa using hlim.const_sub 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [ha] with n hn
    simpa only [sub_eq_add_neg, mul_neg] using
      (one_add_mul_le_pow (show (-2 : ℝ) ≤ -a n by linarith [hn.2]) n)
  · filter_upwards [ha] with n hn
    exact pow_le_one₀ (sub_nonneg.mpr hn.2) (by linarith [hn.1])

theorem tendsto_one_add_pow_pred {a : ℕ → ℝ}
    (ha : ∀ᶠ n in atTop, 0 ≤ a n)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 0)) :
    Tendsto (fun n => (1 + a n) ^ (n - 1)) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_one_add_pow ha hlim)
  · filter_upwards [ha] with n hn
    exact one_le_pow₀ (by linarith : 1 ≤ 1 + a n)
  · filter_upwards [ha] with n hn
    exact pow_le_pow_right₀ (by linarith : 1 ≤ 1 + a n) (Nat.sub_le n 1)

theorem eventually_mem_unit_of_dimension_small {a : ℕ → ℝ}
    (ha : ∀ᶠ n in atTop, 0 ≤ a n)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, a n ∈ Set.Icc 0 1 := by
  have hu := hlim.eventually_le_const (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [ha, hu, eventually_ge_atTop (1 : ℕ)] with n hn hnu hn1
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  exact ⟨hn, by nlinarith [mul_nonneg (sub_nonneg.mpr hnreal) hn]⟩

theorem tendsto_momentBase_pow :
    Tendsto (fun n => (momentBase n) ^ n) atTop (𝓝 1) := by
  apply tendsto_one_add_pow (Eventually.of_forall fun n => by positivity)
  simpa only [mul_left_comm, mul_zero] using
    (tendsto_dimension_mul_rpow (by norm_num : (1 : ℝ) < 6 / 5)).const_mul 4

theorem tendsto_kernelMass_pow :
    Tendsto (fun n => (kernelMass n) ^ n) atTop (𝓝 1) := by
  have hn : ∀ᶠ n : ℕ in atTop, 0 ≤ 2 * (n : ℝ) ^ (-(2 : ℝ)) :=
    Eventually.of_forall fun n => by positivity
  have hl : Tendsto (fun n : ℕ => (n : ℝ) * (2 * (n : ℝ) ^ (-(2 : ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_left_comm, mul_zero] using
      (tendsto_dimension_mul_rpow (by norm_num : (1 : ℝ) < 2)).const_mul 2
  exact tendsto_one_sub_pow (eventually_mem_unit_of_dimension_small hn hl) hl

theorem tendsto_idealError : Tendsto idealError atTop (𝓝 0) := by
  change Tendsto (fun n => (momentBase n) ^ n - 2 * (kernelMass n) ^ n + 1)
    atTop (𝓝 0)
  convert
    (tendsto_momentBase_pow.sub (tendsto_kernelMass_pow.const_mul 2)).add_const 1
    using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

theorem tendsto_productError (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (productError C) atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun n =>
    4 * (n : ℝ) ^ (-(6 / 5 : ℝ)) + C * (n : ℝ) ^ (-(50 : ℝ))
  have ha : ∀ᶠ n in atTop, 0 ≤ a n :=
    Eventually.of_forall fun n => by dsimp [a] <;> positivity
  have hfirst := (tendsto_dimension_mul_rpow (by norm_num : (1 : ℝ) < 6 / 5)).const_mul 4
  have hsecond := (tendsto_dimension_mul_rpow (by norm_num : (1 : ℝ) < 50)).const_mul C
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 0) := by
    simpa only [a, mul_add, mul_left_comm, mul_zero, add_zero] using hfirst.add hsecond
  have hp := tendsto_one_add_pow_pred ha hlim
  have he : Tendsto (fun n : ℕ => (n : ℝ) * (C * (n : ℝ) ^ (-(50 : ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_left_comm, mul_zero] using hsecond
  change Tendsto (fun n : ℕ => (n : ℝ) * (C * (n : ℝ) ^ (-(50 : ℝ))) *
    (momentBase n + C * (n : ℝ) ^ (-(50 : ℝ))) ^ (n - 1)) atTop (𝓝 0)
  simpa only [momentBase, a, add_assoc, zero_mul] using he.mul hp

theorem tendsto_meanSquareBound (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (meanSquareBound C) atTop (𝓝 0) := by
  have hd : Tendsto diagonalError atTop (𝓝 0) := tendsto_source_diagonal
  change Tendsto (fun n => 2 * (diagonalError n + 3 * productError C n) +
    2 * idealError n) atTop (𝓝 0)
  simpa only [mul_zero, add_zero] using
    ((hd.add ((tendsto_productError C hC).const_mul 3)).const_mul 2).add
      (tendsto_idealError.const_mul 2)

end Invariant233.SamplingAsymptotics

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingMeanSquare
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.SamplingAsymptotics

theorem tendsto_ofReal_meanSquareBound (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun m => ENNReal.ofReal (meanSquareBound C m)) atTop (𝓝 0) := by
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (tendsto_meanSquareBound C hC)

end Invariant233.SamplingAsymptotics

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SyndeticSampling
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.SyndeticSampling

theorem card_hits_in_blocks {P : ℕ → Prop} [DecidablePred P] (L : ℕ)
    (hhit : ∀ k : ℕ, ∃ r : ℕ, r ≤ L ∧ P (k + r)) (a M : ℕ) :
    M ≤ ((Finset.Ico a (a + M * (L + 1))).filter P).card := by
  classical
  choose r hr hP using hhit
  let f : ℕ → ℕ := fun i => a + i * (L + 1) + r (a + i * (L + 1))
  have hupper (i : ℕ) : f i < a + (i + 1) * (L + 1) := by
    dsimp [f]
    have := hr (a + i * (L + 1))
    nlinarith
  have hlower (i : ℕ) : a + i * (L + 1) ≤ f i := by
    dsimp [f]
    omega
  have hstrict : StrictMono f := by
    intro i j hij
    have hmul := Nat.mul_le_mul_right (L + 1) (show i + 1 ≤ j by omega)
    exact (hupper i).trans_le ((Nat.add_le_add_left hmul a).trans (hlower j))
  have hsub : (Finset.range M).image f ⊆
      (Finset.Ico a (a + M * (L + 1))).filter P := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    have hiM : i < M := Finset.mem_range.mp hi
    have hmul := Nat.mul_le_mul_right (L + 1) (show i + 1 ≤ M by omega)
    apply Finset.mem_filter.mpr
    constructor
    · refine Finset.mem_Ico.mpr ⟨?_, (hupper i).trans_le (Nat.add_le_add_left hmul a)⟩
      exact (Nat.le_add_right a (i * (L + 1))).trans (hlower i)
    · exact hP (a + i * (L + 1))
  have hcard : ((Finset.range M).image f).card = M := by
    rw [Finset.card_image_of_injective _ hstrict.injective, Finset.card_range]
  calc
    M = ((Finset.range M).image f).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

theorem card_hits_in_half_interval {P : ℕ → Prop} [DecidablePred P] (L : ℕ)
    (hhit : ∀ k : ℕ, ∃ r : ℕ, r ≤ L ∧ P (k + r))
    {Q : ℝ} (hQ : 8 * ((L : ℝ) + 1) ≤ Q) :
    Q / (8 * ((L : ℝ) + 1)) ≤
      (((Finset.Icc ⌈Q / 2⌉₊ ⌊Q⌋₊).filter P).card : ℝ) := by
  let a : ℕ := ⌈Q / 2⌉₊
  let M : ℕ := ⌊Q / (4 * ((L : ℝ) + 1))⌋₊
  have hL : 0 < (L : ℝ) + 1 := by positivity
  have hQ0 : 0 ≤ Q := by nlinarith
  have hMlo : Q / (4 * ((L : ℝ) + 1)) - 1 < (M : ℝ) := by
    exact Nat.sub_one_lt_floor _
  have hMhi : (M : ℝ) ≤ Q / (4 * ((L : ℝ) + 1)) :=
    Nat.floor_le (by positivity)
  have ha : (a : ℝ) < Q / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hMbound : (M : ℝ) * ((L : ℝ) + 1) ≤ Q / 4 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    have h := (le_div_iff₀ (show 0 < 4 * ((L : ℝ) + 1) by positivity)).mp hMhi
    nlinarith
  have hend : ((a + M * (L + 1) : ℕ) : ℝ) ≤ Q := by
    push_cast
    nlinarith
  have hsub : ((Finset.Ico a (a + M * (L + 1))).filter P) ⊆
      (Finset.Icc ⌈Q / 2⌉₊ ⌊Q⌋₊).filter P := by
    intro n hn
    obtain ⟨hni, hpn⟩ := Finset.mem_filter.mp hn
    obtain ⟨han, hne⟩ := Finset.mem_Ico.mp hni
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨han, ?_⟩, hpn⟩
    apply Nat.le_floor
    exact (show (n : ℝ) ≤ ((a + M * (L + 1) : ℕ) : ℝ) by exact_mod_cast hne.le).trans hend
  have hcard := (card_hits_in_blocks L hhit a M).trans (Finset.card_le_card hsub)
  have hcardReal : (M : ℝ) ≤
      (((Finset.Icc ⌈Q / 2⌉₊ ⌊Q⌋₊).filter P).card : ℝ) := by exact_mod_cast hcard
  have hratio : 2 ≤ Q / (4 * ((L : ℝ) + 1)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have hdouble : Q / (4 * ((L : ℝ) + 1)) = 2 * (Q / (8 * ((L : ℝ) + 1))) := by
    field_simp
    ring
  linarith

theorem exists_uniform_hitting_window {θ : ℝ} (hθ : Irrational θ)
    (O : Set (AddCircle (1 : ℝ))) (hO : IsOpen O) (hOne : O.Nonempty) :
    ∃ L : ℕ, ∀ x : AddCircle (1 : ℝ), ∃ r : ℕ, r ≤ L ∧
      x + r • (θ : AddCircle (1 : ℝ)) ∈ O := by
  classical
  obtain ⟨L, φ, hnonneg, hsum, hsupport, hzero⟩ :=
    Invariant233.exists_irrational_rotation_partition hθ O hO hOne
  refine ⟨L, ?_⟩
  intro x
  have hsumne : (∑ r ∈ Finset.range (L + 1), φ r x) ≠ 0 := by
    rw [hsum x]
    norm_num
  obtain ⟨r, hr, hφ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
  refine ⟨r, Nat.le_of_lt_succ (Finset.mem_range.mp hr), ?_⟩
  exact hsupport r ⟨x, subset_tsupport (φ r) hφ, rfl⟩

theorem exists_uniform_phase_hitting_window {θ : ℝ} (hθ : Irrational θ)
    (t ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, ∀ k : ℕ, ∃ r : ℕ, r ≤ L ∧
      Int.fract (((k + r : ℕ) : ℝ) * θ - t) ∈ Set.Ioo 0 ε := by
  let O : Set (AddCircle (1 : ℝ)) :=
    (fun z : ℝ => (z : AddCircle (1 : ℝ))) '' Set.Ioo 0 (min ε 1)
  have hO : IsOpen O := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hOne : O.Nonempty :=
    (Set.nonempty_Ioo.mpr (lt_min hε zero_lt_one)).image _
  obtain ⟨L, hL⟩ := exists_uniform_hitting_window hθ O hO hOne
  refine ⟨L, ?_⟩
  intro k
  obtain ⟨r, hr, hmem⟩ := hL ((((k : ℝ) * θ - t) : ℝ) : AddCircle (1 : ℝ))
  obtain ⟨z, hz, hze⟩ := hmem
  have he : ((((k + r : ℕ) : ℝ) * θ - t : ℝ) : AddCircle (1 : ℝ)) =
      ((((k : ℝ) * θ - t) : ℝ) : AddCircle (1 : ℝ)) +
        r • (θ : AddCircle (1 : ℝ)) := by
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul, ← AddCircle.coe_add]
    congr 1
    push_cast
    ring
  have hf : Int.fract z = Int.fract (((k + r : ℕ) : ℝ) * θ - t) := by
    have h := congrArg (fun x : AddCircle (1 : ℝ) =>
      (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)) (hze.trans he.symm)
    simpa only [AddCircle.coe_equivIco_mk_apply, div_one, mul_one] using h
  have hz01 : 0 ≤ z ∧ z < 1 := ⟨hz.1.le, hz.2.trans_le (min_le_right ε 1)⟩
  rw [Int.fract_eq_self.mpr hz01] at hf
  refine ⟨r, hr, ?_⟩
  rw [← hf]
  exact ⟨hz.1, hz.2.trans_le (min_le_left ε 1)⟩

open Filter
open scoped Topology

theorem tendsto_sampling_horizon :
    Tendsto (fun m : ℕ => (m : ℝ) ^ ((7 / 10 : ℝ) * m)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 20] with m hm
  have hmr : (20 : ℝ) ≤ m := by exact_mod_cast hm
  have h := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ m by linarith) (show (1 : ℝ) ≤ (7 / 10 : ℝ) * m by linarith)
  simpa only [Real.rpow_one] using h

theorem eventually_exists_prescribed_phase_sampling_powers {θ : ℝ}
    (hθ : Irrational θ) (shift width : ℝ) (hwidth : 0 < width) :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, N ≤ m ^ 2 →
      ∃ t : Finset ℕ,
        (∀ n ∈ t, (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n ∧
          (n : ℝ) ≤ (m : ℝ) ^ ((7 / 10 : ℝ) * m)) ∧
        (∀ n ∈ t, Int.fract ((n : ℝ) * θ - shift) ∈ Set.Ioo 0 width) ∧
        (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (t.card : ℝ) ∧
        (∀ n ∈ t, 0 < n) ∧
        ∀ n ∈ t, ∀ n' ∈ t, n ≠ n' → ∀ v v' : ℤ,
          |v| ≤ (m ^ 300 : ℕ) → |v'| ≤ (m ^ 300 : ℕ) →
          (v ≠ 0 ∨ v' ≠ 0) →
          (N * m ^ 1000 : ℕ) < |v * (n : ℤ) + v' * (n' : ℤ)| := by
  classical
  obtain ⟨L, hL⟩ := exists_uniform_phase_hitting_window hθ shift width hwidth
  let c : ℝ := 1 / (8 * ((L : ℝ) + 1))
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hselection := SeparatedPowers.eventually_select_from_supply c hc
  have hm : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hgrowth := SeparatedPowers.eventually_power_gap hm 4 0 (7 / 10) 1002 (by norm_num)
  filter_upwards [hselection, hgrowth,
    tendsto_sampling_horizon.eventually_ge_atTop (8 * ((L : ℝ) + 1)),
    eventually_ge_atTop 20] with m hselect hgrowth hQlarge hm20
  intro N hN
  let Q : ℝ := (m : ℝ) ^ ((7 / 10 : ℝ) * m)
  let P : ℕ → Prop := fun n => Int.fract ((n : ℝ) * θ - shift) ∈ Set.Ioo 0 width
  let s : Finset ℕ := (Finset.Icc ⌈Q / 2⌉₊ ⌊Q⌋₊).filter P
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hQpos : 0 < Q := Real.rpow_pos_of_pos hmpos _
  have hinterval : ∀ n ∈ s, Q / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ Q := by
    intro n hn
    have hni := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    constructor
    · exact (Nat.le_ceil (Q / 2)).trans (by exact_mod_cast hni.1)
    · exact (show (n : ℝ) ≤ (⌊Q⌋₊ : ℝ) by exact_mod_cast hni.2).trans (Nat.floor_le hQpos.le)
  have hsize : c * Q ≤ (s.card : ℝ) := by
    have h := card_hits_in_half_interval (P := P) L hL (Q := Q) hQlarge
    simpa only [s, P, c, div_eq_mul_inv, one_mul, mul_comm] using h
  have hR : N * m ^ 1000 ≤ m ^ 1002 := by
    calc
      N * m ^ 1000 ≤ m ^ 2 * m ^ 1000 := Nat.mul_le_mul_right _ hN
      _ = m ^ 1002 := by rw [← pow_add]
  have hRreal : ((N * m ^ 1000 : ℕ) : ℝ) ≤ (m : ℝ) ^ (1002 : ℝ) := by
    rw [show (1002 : ℝ) = ((1002 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact_mod_cast hR
  have hRlt : ((N * m ^ 1000 : ℕ) : ℝ) < Q / 2 := by
    have hp := Real.rpow_pos_of_pos hmpos (1002 : ℝ)
    simp only [zero_mul, Real.rpow_zero, mul_one] at hgrowth
    dsimp [Q]
    linarith
  obtain ⟨t, hts, hcard, hsep⟩ := hselect N hN s (by
    intro n hn
    have h := hRlt.trans_le (hinterval n hn).1
    exact_mod_cast h) hsize
  refine ⟨t, (fun n hn => hinterval n (hts hn)), ?_, hcard, ?_, hsep⟩
  · intro n hn
    exact (Finset.mem_filter.mp (hts hn)).2
  · intro n hn
    have h := (half_pos hQpos).trans_le (hinterval n (hts hn)).1
    exact_mod_cast h

theorem eventually_exists_simultaneous_phase_sampling_powers {θ : ℝ}
    (hθ : Irrational θ) (q : ℕ) (shift width : Fin q → ℝ)
    (hwidth : ∀ r, 0 < width r) :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, N ≤ m ^ 2 →
      ∃ t : Fin q → Finset ℕ, ∀ r : Fin q,
        (∀ n ∈ t r, (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n ∧
          (n : ℝ) ≤ (m : ℝ) ^ ((7 / 10 : ℝ) * m)) ∧
        (∀ n ∈ t r, Int.fract ((n : ℝ) * θ - shift r) ∈ Set.Ioo 0 (width r)) ∧
        (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ ((t r).card : ℝ) ∧
        (∀ n ∈ t r, 0 < n) ∧
        ∀ n ∈ t r, ∀ n' ∈ t r, n ≠ n' → ∀ v v' : ℤ,
          |v| ≤ (m ^ 300 : ℕ) → |v'| ≤ (m ^ 300 : ℕ) →
          (v ≠ 0 ∨ v' ≠ 0) →
          (N * m ^ 1000 : ℕ) < |v * (n : ℤ) + v' * (n' : ℤ)| := by
  classical
  have hall := Filter.eventually_all.mpr (fun r : Fin q =>
    eventually_exists_prescribed_phase_sampling_powers hθ (shift r) (width r) (hwidth r))
  filter_upwards [hall] with m hm
  intro N hN
  choose t ht using (fun r : Fin q => hm r N hN)
  exact ⟨t, ht⟩

end Invariant233.SyndeticSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_TrialSamplingPowers
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.TrialSampling
open Filter

theorem samplingPair_of_nat_separation {m N n n' : ℕ}
    (hN : 0 < N) (hNm : N ≤ m ^ 2) (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n')
    (hrange : ScalarSampling.samplingHorizon m / 2 ≤ (n : ℝ) ∧
      (n : ℝ) ≤ ScalarSampling.samplingHorizon m)
    (hrange' : ScalarSampling.samplingHorizon m / 2 ≤ (n' : ℝ) ∧
      (n' : ℝ) ≤ ScalarSampling.samplingHorizon m)
    (hsep : ∀ v v' : ℤ, |v| ≤ (m ^ 300 : ℕ) → |v'| ≤ (m ^ 300 : ℕ) →
      (v ≠ 0 ∨ v' ≠ 0) →
        (N * m ^ 1000 : ℕ) < |v * (n : ℤ) + v' * (n' : ℤ)|) :
    ScalarSampling.SamplingPair m N N n n' where
  N₀_pos := by exact_mod_cast hN
  N₀_le := le_rfl
  N_le := by exact_mod_cast hNm
  n_pos := hn
  n'_pos := hn'
  distinct := hne
  first_range := hrange
  second_range := hrange'
  separated := by
    intro v v' hv hv' hvv
    exact_mod_cast hsep v v' hv hv' hvv

theorem eventually_exists_scalar_ready_phase_samples {θ : ℝ} (hθ : Irrational θ)
    (q : ℕ) (shift width : Fin q → ℝ) (hwidth : ∀ r, 0 < width r) :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, 0 < N → N ≤ m ^ 2 →
      ∃ samples : Fin q → Finset ℕ, ∀ r : Fin q,
        (samples r).Nonempty ∧
        (∀ n ∈ samples r, ScalarSampling.samplingHorizon m / 2 ≤ (n : ℝ) ∧
          (n : ℝ) ≤ ScalarSampling.samplingHorizon m) ∧
        (∀ n ∈ samples r, Int.fract ((n : ℝ) * θ - shift r) ∈ Set.Ioo 0 (width r)) ∧
        (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ ((samples r).card : ℝ) ∧
        (∀ n ∈ samples r, 0 < n) ∧
        ∀ n ∈ samples r, ∀ n' ∈ samples r, n ≠ n' →
          ScalarSampling.SamplingPair m N N n n' := by
  have hs := SyndeticSampling.eventually_exists_simultaneous_phase_sampling_powers
    hθ q shift width hwidth
  filter_upwards [hs, eventually_ge_atTop (1 : ℕ)] with m hm hm1
  intro N hN hNm
  obtain ⟨samples, hsample⟩ := hm N hNm
  refine ⟨samples, ?_⟩
  intro r
  obtain ⟨hrange, hphase, hcard, hpos, hsep⟩ := hsample r
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hc : 0 < ((samples r).card : ℝ) :=
    (Real.rpow_pos_of_pos hmpos _).trans_le hcard
  refine ⟨Finset.card_pos.mp (by exact_mod_cast hc), hrange, hphase, hcard, hpos, ?_⟩
  intro n hn n' hn' hne
  exact samplingPair_of_nat_separation hN hNm (hpos n hn) (hpos n' hn') hne
    (hrange n hn) (hrange n' hn') (hsep n hn n' hn' hne)

end Invariant233.TrialSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_PrescribedSamplingStage
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Invariant233.TrialSampling

theorem eventually_actual_moment_budget (r : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ (m : ℕ) in atTop,
      ENNReal.ofReal (ProductPhases.failureBound m) +
        (2 * r : ℝ≥0∞) *
          (ENNReal.ofReal (SamplingAsymptotics.meanSquareBound 3509 m) /
            ENNReal.ofReal (ρ ^ 2)) < 1 := by
  have hε0 : ENNReal.ofReal (ρ ^ 2) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hρ))
  have hδ := SamplingAsymptotics.tendsto_ofReal_meanSquareBound 3509 (by norm_num)
  have hdiv : Tendsto (fun m =>
      ENNReal.ofReal (SamplingAsymptotics.meanSquareBound 3509 m) /
        ENNReal.ofReal (ρ ^ 2)) atTop (𝓝 0) := by
    simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hδ (Or.inr hε0)
  have hmul : Tendsto (fun m => (2 * r : ℝ≥0∞) *
      (ENNReal.ofReal (SamplingAsymptotics.meanSquareBound 3509 m) /
        ENNReal.ofReal (ρ ^ 2))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul (a := (2 * r : ℝ≥0∞)) hdiv
        (Or.inr (by finiteness))
  exact (tendsto_failureBound_nat.add hmul).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) + 0 < 1))

theorem eventually_exists_prescribed_sampling_stage {θ : ℝ} (hθ : Irrational θ)
    (r : ℕ) (shift width : Fin r → ℝ) (hwidth : ∀ t, 0 < width t)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, 2 < N → N ≤ m ^ 2 →
      ∀ (R : ℝ) (q₀ : ℕ), 0 < q₀ →
      ∃ samples : Fin r → Finset ℕ,
        (∀ t : Fin r,
          (samples t).Nonempty ∧
          (∀ n ∈ samples t, ScalarSampling.samplingHorizon m / 2 ≤ (n : ℝ) ∧
            (n : ℝ) ≤ ScalarSampling.samplingHorizon m) ∧
          (∀ n ∈ samples t, Int.fract ((n : ℝ) * θ - shift t) ∈ Ioo 0 (width t)) ∧
          (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ ((samples t).card : ℝ) ∧
          (∀ n ∈ samples t, 0 < n) ∧
          ∀ n ∈ samples t, ∀ n' ∈ samples t, n ≠ n' →
            ScalarSampling.SamplingPair m N N n n') ∧
        ∃ q : ℕ → ℕ,
          q 0 = q₀ ∧ (∀ i, 0 < q i) ∧ StrictMono q ∧
          (∀ i, q i ∣ q (i + 1)) ∧
          (∀ i < m, R ≤ (q (i + 1) : ℝ) / q i) ∧
          (∀ i : Fin m, Int.fract ((q (i.val + 1) : ℝ) * θ) ∈
            Ioo (1 / (N : ℝ)) (2 / (N : ℝ))) ∧
          ProductPhases.strictLargePhaseCondition Finset.univ (N : ℝ)
            (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ)) ∧
          ∀ t endpoint,
            eLpNorm (fun x : Circle => average m (samples t) endpoint
              (fun i : Fin m => Int.fract ((q (i.val + 1) : ℝ) * θ))
              (fun i : Fin m => (q (i.val + 1) : ℤ) • x) - 1) 2 circleMeasure <
                ENNReal.ofReal ρ := by
  have hs := eventually_exists_scalar_ready_phase_samples hθ r shift width hwidth
  filter_upwards [hs, eventually_ge_atTop (200 : ℕ), eventually_actual_moment_budget r hρ]
    with m hms hm hbudget
  intro N hN hNm R q₀ hq₀
  have hNpos : 0 < N := by omega
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hNmreal : (N : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hNm
  obtain ⟨samples, hsample⟩ := hms N hNpos hNm
  refine ⟨samples, hsample, ?_⟩
  apply SamplingTests.exists_character_stage_of_moment_budget hθ hm
    (by exact_mod_cast hN) samples (fun t => (hsample t).2.2.2.2.1) hρ
    (δ := ENNReal.ofReal (SamplingAsymptotics.meanSquareBound 3509 m))
    ?_ (by simpa only [Fintype.card_fin] using hbudget) R hq₀
  intro t endpoint
  exact expectation_squaredError_le_actual_bound hm hNreal hNmreal (samples t)
    (hsample t).1 (hsample t).2.2.2.1 (fun n hn => ((hsample t).2.1 n hn).1)
    (hsample t).2.2.2.2.2 endpoint

end Invariant233.TrialSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleSamplingStageSupply
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Invariant233

theorem circleSamplingStage_supply {θ : ℝ} (hθ : Irrational θ)
    (j K d q₀ : ℕ) (hj : 0 < j) (hK : 0 < K) (hq₀ : 0 < q₀) :
    ∀ᶠ m : ℕ in atTop, ∀ R : ℝ, Nonempty (CircleSamplingStage θ j K d q₀ m R) := by
  let shift : Fin q₀ → ℝ := fun r => (r.val : ℝ) / q₀
  let width : Fin q₀ → ℝ := fun _ =>
    1 / (((j + 1 : ℕ) : ℝ) ^ 2 * (1 + (d : ℝ)) * q₀)
  have hwidth : ∀ r, 0 < width r := by
    intro r
    dsimp [width]
    positivity
  have hs := TrialSampling.eventually_exists_prescribed_sampling_stage hθ q₀ shift width
    hwidth (ρ := 1 / (j : ℝ)) (by positivity)
  filter_upwards [hs, eventually_ge_atTop K, eventually_ge_atTop (3 : ℕ)]
    with m hms hmK hm3
  intro R
  have hN : 2 < m * K := by nlinarith
  have hNm : m * K ≤ m ^ 2 := by nlinarith
  obtain ⟨samples, hsample, q, hzero, hpos, hstrict, hdiv, hratio, hphases,
    hspread, hnorm⟩ := hms (m * K) hN hNm R q₀ hq₀
  refine ⟨{
    q := q
    samples := samples
    q_zero := hzero
    q_pos := hpos
    q_strict := hstrict
    q_div := hdiv
    q_ratio := hratio
    phases := ?_
    spread := ?_
    samples_nonempty := fun r => (hsample r).1
    samples_positive := fun r => (hsample r).2.2.2.2.1
    samples_range := fun r => (hsample r).2.1
    samples_phase := fun r => (hsample r).2.2.1
    sampling_L2 := hnorm }⟩
  · simpa only [Nat.cast_mul] using hphases
  · simpa only [Nat.cast_mul] using hspread

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleParametersExistence
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233

theorem exists_circle_parameters_oai {θ : ℝ} (hθ : Irrational θ) :
    ∃ p : CircleParameterData, CircleParameterLaws θ p :=
  CircleParameterRecursion.exists_parameters_of_stage_supply hθ
    (circleSamplingStage_supply hθ)

end Invariant233

end OAI
end

theorem solution : type_of% @OAI.Invariant233.exists_circle_parameters_oai := @OAI.Invariant233.exists_circle_parameters_oai
