-- Prove2me | solution 1 for OAI.Invariant233.ProductSamplingPhaseMoments.expected_average_error_le_source_scale
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:32:22.359516+00:00
-- url     : https://prove2.me/submissions/9af1b5ec-14ab-4746-97f6-b7c5b6cf5f1d

import Mathlib
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Interval
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
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_Q234IR003

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BVDiscrepancy
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace Invariant233.BVDiscrepancy

lemma measurable_tail (a : ℝ) : Measurable (tail a) :=
  measurable_const.indicator measurableSet_Icc

lemma norm_tail_le_one (a x : ℝ) : ‖tail a x‖ ≤ 1 := by
  by_cases hx : x ∈ Icc a 1 <;> simp [tail, hx]

lemma integrable_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (a : ℝ) :
    Integrable (fun ω => tail a (X ω)) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    ((measurable_tail a).comp hX).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => norm_tail_le_one a (X ω)

lemma integral_tail {a : ℝ} (ha : a ∈ Icc 0 1) :
    ∫ x, tail a x ∂unitMeasure = ((1 - a : ℝ) : ℂ) := by
  simp only [tail]
  rw [integral_indicator measurableSet_Icc]
  simp only [unitMeasure, Measure.restrict_restrict measurableSet_Icc]
  rw [inter_eq_left.mpr (Icc_subset_Icc ha.1 le_rfl)]
  simp [max_eq_left (sub_nonneg.mpr ha.2)]

lemma sum_coefficient (f : ℝ → ℂ) (N r : ℕ) :
    ∑ k ∈ Finset.range (r + 1), coefficient f N k = f ((r : ℝ) / N) := by
  induction r with
  | zero => simp
  | succ r hr =>
    rw [Finset.sum_range_succ, hr, coefficient_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    abel

lemma sum_norm_coefficient_le (f : ℝ → ℂ) {N : ℕ} (hN : 0 < N)
    (hf : BoundedVariationOn f (Icc (0 : ℝ) 1)) :
    ∑ k ∈ Finset.range (N + 1), ‖coefficient f N k‖ ≤
      ‖f 0‖ + (eVariationOn f (Icc (0 : ℝ) 1)).toReal := by
  rw [Finset.sum_range_succ']
  simp only [coefficient_zero, coefficient_succ]
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hv := eVariationOn.sum_le_of_monotoneOn_Iic (f := f) (s := Icc (0 : ℝ) 1) (n := N)
    (u := fun k : ℕ => (k : ℝ) / N)
    (fun i _ j _ hij => div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) hNp.le)
    (fun i hi => ⟨div_nonneg (Nat.cast_nonneg _) hNp.le,
      (div_le_one hNp).mpr (Nat.cast_le.mpr hi)⟩)
  have hv' :
      ENNReal.ofReal (∑ k ∈ Finset.range N,
        ‖f (((k : ℝ) + 1) / N) - f ((k : ℝ) / N)‖) ≤
        eVariationOn f (Icc (0 : ℝ) 1) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    simpa only [edist_dist, dist_eq_norm, Nat.cast_add, Nat.cast_one] using hv
  have := (ENNReal.toReal_mono hf hv')
  rw [ENNReal.toReal_ofReal (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at this
  linarith

lemma measurable_step (f : ℝ → ℂ) (N : ℕ) : Measurable (step f N) := by
  unfold step
  exact Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_tail _)

lemma norm_step_le (f : ℝ → ℂ) {N : ℕ} (hN : 0 < N)
    (hf : BoundedVariationOn f (Icc (0 : ℝ) 1)) (x : ℝ) :
    ‖step f N x‖ ≤ ‖f 0‖ + (eVariationOn f (Icc (0 : ℝ) 1)).toReal := by
  calc
    ‖step f N x‖ ≤ ∑ k ∈ Finset.range (N + 1),
        ‖coefficient f N k * tail ((k : ℝ) / N) x‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (N + 1), ‖coefficient f N k‖ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_tail_le_one _ _)
    _ ≤ _ := sum_norm_coefficient_le f hN hf

lemma step_eq_floor (f : ℝ → ℂ) {N : ℕ} (hN : 0 < N)
    {x : ℝ} (hx : x ∈ Icc 0 1) :
    step f N x = f ((⌊(N : ℝ) * x⌋₊ : ℝ) / N) := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNx : 0 ≤ (N : ℝ) * x := mul_nonneg hNp.le hx.1
  have hr : ⌊(N : ℝ) * x⌋₊ ≤ N := by
    apply Nat.floor_le_of_le
    simpa using mul_le_mul_of_nonneg_left hx.2 hNp.le
  have htail (k : ℕ) : tail ((k : ℝ) / N) x =
      if k ≤ ⌊(N : ℝ) * x⌋₊ then 1 else 0 := by
    have hiff : (k : ℝ) / N ≤ x ↔ k ≤ ⌊(N : ℝ) * x⌋₊ := by
      rw [div_le_iff₀ hNp, Nat.le_floor_iff hNx]
      rw [mul_comm]
    simp [tail, Set.indicator_apply, hx.2, hiff]
  unfold step
  simp_rw [htail, mul_ite, mul_one, mul_zero]
  calc
    ∑ k ∈ Finset.range (N + 1),
        (if k ≤ ⌊(N : ℝ) * x⌋₊ then coefficient f N k else 0) =
      ∑ k ∈ Finset.range (⌊(N : ℝ) * x⌋₊ + 1), coefficient f N k := by
        calc
          _ = ∑ k ∈ Finset.range (⌊(N : ℝ) * x⌋₊ + 1),
              (if k ≤ ⌊(N : ℝ) * x⌋₊ then coefficient f N k else 0) := by
            symm
            apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hr))
            intro k hk hkr
            simp only [Finset.mem_range, not_lt] at hkr
            simp [show ¬ k ≤ ⌊(N : ℝ) * x⌋₊ by omega]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_range] at hk
            simp [Nat.le_of_lt_succ hk]
    _ = _ := sum_coefficient f N _

lemma tendsto_step_of_continuousAt (f : ℝ → ℂ) {x : ℝ}
    (hx : x ∈ Icc 0 1) (hcont : ContinuousAt f x) :
    Tendsto (fun n : ℕ => step f (n + 1) x) atTop (𝓝 (f x)) := by
  have hgrid := (tendsto_nat_floor_mul_div_atTop hx.1).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hgrid' : Tendsto (fun n : ℕ =>
      (⌊(((n + 1 : ℕ) : ℝ) * x)⌋₊ : ℝ) / (n + 1 : ℕ)) atTop (𝓝 x) := by
    simpa only [Function.comp_def, mul_comm x] using hgrid
  convert hcont.tendsto.comp hgrid' using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact step_eq_floor f (Nat.succ_pos n) hx

lemma ae_tendsto_step (f : ℝ → ℂ)
    (hf : BoundedVariationOn f (Icc (0 : ℝ) 1)) :
    ∀ᵐ x ∂unitMeasure,
      Tendsto (fun n : ℕ => step f (n + 1) x) atTop (𝓝 (f x)) := by
  have hf' : BoundedVariationOn f (uIcc (0 : ℝ) 1) := by simpa using hf
  have hdiff := hf'.ae_differentiableAt_of_mem_uIcc
  have hdiff' : ∀ᵐ x ∂unitMeasure, x ∈ Icc (0 : ℝ) 1 → DifferentiableAt ℝ f x := by
    exact ae_restrict_of_ae (by simpa using hdiff)
  filter_upwards [hdiff', ae_restrict_mem (μ := volume) measurableSet_Icc] with x hd hx
  exact tendsto_step_of_continuousAt f hx (hd hx).continuousAt

lemma ae_tendsto_step_comp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : Measurable X) (hXac : μ.map X ≪ unitMeasure)
    (f : ℝ → ℂ) (hf : BoundedVariationOn f (Icc (0 : ℝ) 1)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => step f (n + 1) (X ω)) atTop (𝓝 (f (X ω))) :=
  ae_of_ae_map hX.aemeasurable (hXac.ae_le (ae_tendsto_step f hf))

lemma integrable_tail_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (a b : ℝ) : Integrable (fun ω => tail a (X ω) * tail b (Y ω)) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (((measurable_tail a).comp hX).mul ((measurable_tail b).comp hY)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  change ‖tail a (X ω) * tail b (Y ω)‖ ≤ 1
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖tail b (Y ω)‖ :=
      mul_le_mul_of_nonneg_right (norm_tail_le_one _ _) (norm_nonneg _)
    _ ≤ 1 := by simpa only [one_mul] using norm_tail_le_one b (Y ω)

theorem finite_test_discrepancy {Ω ι κ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (u : ι → Ω → ℂ) (v : κ → Ω → ℂ)
    (m : ι → ℂ) (n : κ → ℂ) (ε : ℝ)
    (hint : ∀ i ∈ s, ∀ j ∈ t, Integrable (fun ω => u i ω * v j ω) μ)
    (hdisc : ∀ i ∈ s, ∀ j ∈ t,
      ‖(∫ ω, u i ω * v j ω ∂μ) - m i * n j‖ ≤ ε) :
    ‖(∫ ω, (∑ i ∈ s, a i * u i ω) * (∑ j ∈ t, b j * v j ω) ∂μ) -
        (∑ i ∈ s, a i * m i) * (∑ j ∈ t, b j * n j)‖ ≤
      ε * (∑ i ∈ s, ‖a i‖) * (∑ j ∈ t, ‖b j‖) := by
  have hint' (i : ι) (hi : i ∈ s) (j : κ) (hj : j ∈ t) :
      Integrable (fun ω => (a i * u i ω) * (b j * v j ω)) μ := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      (hint i hi j hj).const_mul (a i * b j)
  have hI :
      (∫ ω, (∑ i ∈ s, a i * u i ω) * (∑ j ∈ t, b j * v j ω) ∂μ) =
      ∑ i ∈ s, ∑ j ∈ t, (a i * b j) * (∫ ω, u i ω * v j ω ∂μ) := by
    simp_rw [Finset.sum_mul_sum]
    rw [integral_finsetSum s (fun i hi => integrable_finsetSum t (hint' i hi))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum t (hint' i hi)]
    apply Finset.sum_congr rfl
    intro j hj
    have heq : (fun ω => a i * u i ω * (b j * v j ω)) =
        fun ω => (a i * b j) * (u i ω * v j ω) := by funext ω; ring
    rw [heq, integral_const_mul]
  have hrewrite :
      (∫ ω, (∑ i ∈ s, a i * u i ω) * (∑ j ∈ t, b j * v j ω) ∂μ) -
        (∑ i ∈ s, a i * m i) * (∑ j ∈ t, b j * n j) =
      ∑ i ∈ s, ∑ j ∈ t, (a i * b j) * ((∫ ω, u i ω * v j ω ∂μ) - m i * n j) := by
    rw [hI, Finset.sum_mul_sum]
    simp_rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hrewrite]
  calc
    ‖∑ i ∈ s, ∑ j ∈ t,
        (a i * b j) * ((∫ ω, u i ω * v j ω ∂μ) - m i * n j)‖ ≤
      ∑ i ∈ s, ∑ j ∈ t,
        ‖(a i * b j) * ((∫ ω, u i ω * v j ω ∂μ) - m i * n j)‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, ‖a i‖ * ‖b j‖ * ε := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left (hdisc i hi j hj)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ε * (∑ i ∈ s, ‖a i‖) * (∑ j ∈ t, ‖b j‖) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

lemma integral_step (f : ℝ → ℂ) (N : ℕ) :
    ∫ x, step f N x ∂unitMeasure =
      ∑ k ∈ Finset.range (N + 1), coefficient f N k * (∫ x, tail ((k : ℝ) / N) x ∂unitMeasure) := by
  unfold step
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro k hk
    exact (integrable_tail unitMeasure measurable_id _).const_mul _

theorem step_discrepancy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) {ε : ℝ} (hε : 0 ≤ ε)
    (hrect : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      ‖(∫ ω, tail a (X ω) * tail b (Y ω) ∂μ) -
        ((1 - a : ℝ) : ℂ) * ((1 - b : ℝ) : ℂ)‖ ≤ ε)
    (f g : ℝ → ℂ) (hf : BoundedVariationOn f (Icc (0 : ℝ) 1))
    (hg : BoundedVariationOn g (Icc (0 : ℝ) 1)) {N : ℕ} (hN : 0 < N) :
    ‖(∫ ω, step f N (X ω) * step g N (Y ω) ∂μ) -
      (∫ x, step f N x ∂unitMeasure) * (∫ y, step g N y ∂unitMeasure)‖ ≤
      ε * (‖f 0‖ + (eVariationOn f (Icc (0 : ℝ) 1)).toReal) *
        (‖g 0‖ + (eVariationOn g (Icc (0 : ℝ) 1)).toReal) := by
  have hgrid (k : ℕ) (hk : k ∈ Finset.range (N + 1)) :
      (k : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
    have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    exact ⟨div_nonneg (Nat.cast_nonneg _) hNp.le,
      (div_le_one hNp).mpr (Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))⟩
  have h := finite_test_discrepancy μ (Finset.range (N + 1)) (Finset.range (N + 1))
    (coefficient f N) (coefficient g N)
    (fun i ω => tail ((i : ℝ) / N) (X ω))
    (fun j ω => tail ((j : ℝ) / N) (Y ω))
    (fun i => ∫ x, tail ((i : ℝ) / N) x ∂unitMeasure)
    (fun j => ∫ y, tail ((j : ℝ) / N) y ∂unitMeasure) ε
    (fun i _ j _ => integrable_tail_mul μ hX hY _ _)
    (fun i hi j hj => by
      rw [integral_tail (hgrid i hi), integral_tail (hgrid j hj)]
      exact hrect _ (hgrid i hi) _ (hgrid j hj))
  rw [← integral_step f N, ← integral_step g N] at h
  change ‖(∫ ω, step f N (X ω) * step g N (Y ω) ∂μ) -
    (∫ x, step f N x ∂unitMeasure) * (∫ y, step g N y ∂unitMeasure)‖ ≤ _ at h
  apply h.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (sum_norm_coefficient_le f hN hf) hε
  · exact sum_norm_coefficient_le g hN hg
  · exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  · positivity

lemma tendsto_integral_step (f : ℝ → ℂ)
    (hf : BoundedVariationOn f (Icc (0 : ℝ) 1)) :
    Tendsto (fun n : ℕ => ∫ x, step f (n + 1) x ∂unitMeasure) atTop
      (𝓝 (∫ x, f x ∂unitMeasure)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun _ => ‖f 0‖ + (eVariationOn f (Icc (0 : ℝ) 1)).toReal)
  · intro n
    exact (measurable_step f (n + 1)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall (norm_step_le f (Nat.succ_pos n) hf)
  · exact ae_tendsto_step f hf

theorem boundedVariation_discrepancy_endpoint {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (haX : μ.map X ≪ unitMeasure) (haY : μ.map Y ≪ unitMeasure)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hrect : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      ‖(∫ ω, tail a (X ω) * tail b (Y ω) ∂μ) -
        ((1 - a : ℝ) : ℂ) * ((1 - b : ℝ) : ℂ)‖ ≤ ε)
    (f g : ℝ → ℂ) (hf : BoundedVariationOn f (Icc (0 : ℝ) 1))
    (hg : BoundedVariationOn g (Icc (0 : ℝ) 1)) :
    ‖(∫ ω, f (X ω) * g (Y ω) ∂μ) -
      (∫ x, f x ∂unitMeasure) * (∫ y, g y ∂unitMeasure)‖ ≤
      ε * (‖f 0‖ + (eVariationOn f (Icc (0 : ℝ) 1)).toReal) *
        (‖g 0‖ + (eVariationOn g (Icc (0 : ℝ) 1)).toReal) := by
  have hprod : Tendsto (fun n : ℕ =>
      ∫ ω, step f (n + 1) (X ω) * step g (n + 1) (Y ω) ∂μ) atTop
      (𝓝 (∫ ω, f (X ω) * g (Y ω) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => (‖f 0‖ + (eVariationOn f (Icc (0 : ℝ) 1)).toReal) *
        (‖g 0‖ + (eVariationOn g (Icc (0 : ℝ) 1)).toReal))
    · intro n
      exact (((measurable_step f (n + 1)).comp hX).mul
        ((measurable_step g (n + 1)).comp hY)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      apply Filter.Eventually.of_forall
      intro ω
      rw [norm_mul]
      exact mul_le_mul (norm_step_le f (Nat.succ_pos n) hf _)
        (norm_step_le g (Nat.succ_pos n) hg _) (norm_nonneg _) (by positivity)
    · filter_upwards [ae_tendsto_step_comp hX haX f hf,
        ae_tendsto_step_comp hY haY g hg] with ω hfx hgy
      exact hfx.mul hgy
  have hlim := (hprod.sub ((tendsto_integral_step f hf).mul
    (tendsto_integral_step g hg))).norm
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n =>
    step_discrepancy μ hX hY hε hrect f g hf hg (Nat.succ_pos n)

lemma norm_bddAbove_of_boundedVariation (f : ℝ → ℂ)
    (hf : BoundedVariationOn f (Icc (0 : ℝ) 1)) :
    BddAbove ((fun x => ‖f x‖) '' Icc (0 : ℝ) 1) := by
  refine ⟨‖f 0‖ + (eVariationOn f (Icc (0 : ℝ) 1)).toReal, ?_⟩
  rintro z ⟨x, hx, rfl⟩
  have hv := hf.dist_le hx (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
  calc
    ‖f x‖ = ‖(f x - f 0) + f 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖f x - f 0‖ + ‖f 0‖ := norm_add_le _ _
    _ ≤ ‖f 0‖ + (eVariationOn f (Icc (0 : ℝ) 1)).toReal := by
      rw [dist_eq_norm] at hv
      linarith

theorem boundedVariation_discrepancy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (haX : μ.map X ≪ unitMeasure) (haY : μ.map Y ≪ unitMeasure)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hrect : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      ‖(∫ ω, tail a (X ω) * tail b (Y ω) ∂μ) -
        ((1 - a : ℝ) : ℂ) * ((1 - b : ℝ) : ℂ)‖ ≤ ε)
    (f g : ℝ → ℂ) (hf : BoundedVariationOn f (Icc (0 : ℝ) 1))
    (hg : BoundedVariationOn g (Icc (0 : ℝ) 1)) :
    ‖(∫ ω, f (X ω) * g (Y ω) ∂μ) -
      (∫ x, f x ∂unitMeasure) * (∫ y, g y ∂unitMeasure)‖ ≤
      ε * (sSup ((fun x => ‖f x‖) '' Icc (0 : ℝ) 1) +
        (eVariationOn f (Icc (0 : ℝ) 1)).toReal) *
        (sSup ((fun x => ‖g x‖) '' Icc (0 : ℝ) 1) +
        (eVariationOn g (Icc (0 : ℝ) 1)).toReal) := by
  have hfs : ‖f 0‖ ≤ sSup ((fun x => ‖f x‖) '' Icc (0 : ℝ) 1) :=
    le_csSup (norm_bddAbove_of_boundedVariation f hf) ⟨0, by norm_num, rfl⟩
  have hgs : ‖g 0‖ ≤ sSup ((fun x => ‖g x‖) '' Icc (0 : ℝ) 1) :=
    le_csSup (norm_bddAbove_of_boundedVariation g hg) ⟨0, by norm_num, rfl⟩
  apply (boundedVariation_discrepancy_endpoint μ hX hY haX haY hε hrect f g hf hg).trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (add_le_add hfs le_rfl) hε
  · exact add_le_add hgs le_rfl
  · positivity
  · exact mul_nonneg hε (add_nonneg ((norm_nonneg _).trans hfs) ENNReal.toReal_nonneg)

end Invariant233.BVDiscrepancy

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_GeometricAverage
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology
open scoped BigOperators

namespace Invariant233

theorem norm_geometric_sum_le (r : ℂ) (hr : r ≠ 1) (hrnorm : ‖r‖ = 1)
    (n : ℕ) :
    ‖∑ k ∈ Finset.range n, r ^ k‖ ≤ 2 / ‖r - 1‖ := by
  rw [geom_sum_eq hr, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖r ^ n - 1‖ ≤ ‖r ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hrnorm]

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FejerKernel
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace Invariant233.Fejer

 theorem kernel_nonneg (H : ℕ) (x : Circle) : 0 ≤ kernel H x :=
  div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

 theorem geometricPolynomial_eq_sum_pow (H : ℕ) (x : Circle) :
    geometricPolynomial H x = ∑ k ∈ Finset.range H, (fourier 1 x) ^ k := by
  apply Finset.sum_congr rfl
  intro k hk
  simp only [fourier_apply, one_zsmul]
  rw [natCast_zsmul, AddCircle.toCircle_nsmul, Circle.coe_pow]

 theorem kernel_complex_expansion (H : ℕ) (x : Circle) :
    (kernel H x : ℂ) = (H : ℂ)⁻¹ *
      ∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        fourier ((k : ℤ) - (l : ℤ)) x := by
  rw [kernel, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.normSq_eq_conj_mul_self]
  unfold geometricPolynomial
  rw [map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, div_eq_inv_mul]
  simp_rw [sub_eq_add_neg, fourier_add, fourier_neg]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

 theorem integral_fourier (n : ℤ) :
    (∫ x : Circle, fourier n x ∂AddCircle.haarAddCircle) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

 theorem integral_kernel_complex (H : ℕ) (hH : H ≠ 0) :
    (∫ x : Circle, (kernel H x : ℂ) ∂AddCircle.haarAddCircle) = 1 := by
  simp_rw [kernel_complex_expansion]
  rw [integral_const_mul]
  rw [integral_finsetSum]
  · simp_rw [integral_finsetSum _ (fun l hl => (fourier _).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      integral_fourier]
    have hsum : (∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        (if (k : ℤ) - (l : ℤ) = 0 then (1 : ℂ) else 0)) = H := by
      simp only [sub_eq_zero, Nat.cast_inj]
      calc
        _ = ∑ k ∈ Finset.range H, (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [Finset.sum_ite_eq, hk, ite_true, if_true]
        _ = H := by simp
    rw [hsum, inv_mul_cancel₀ (by exact_mod_cast hH)]
  · intro k hk
    exact integrable_finsetSum _ (fun l hl => (fourier _).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

 theorem integral_kernel (H : ℕ) (hH : H ≠ 0) :
    (∫ x : Circle, kernel H x ∂AddCircle.haarAddCircle) = 1 := by
  have h := integral_kernel_complex H hH
  have hcast := integral_ofReal (f := kernel H) (𝕜 := ℂ)
    (μ := (AddCircle.haarAddCircle : Measure Circle))
  have hcast2 : (∫ x : Circle, (kernel H x : ℂ) ∂AddCircle.haarAddCircle) =
      Complex.ofReal (∫ x : Circle, kernel H x ∂AddCircle.haarAddCircle) := hcast
  rw [hcast2] at h
  exact_mod_cast h

 theorem integrable_fourier (n : ℤ) :
    Integrable (fun x : Circle => fourier n x) AddCircle.haarAddCircle :=
  (fourier n).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

 theorem coefficient_norm_le_one (H : ℕ) (hH : H ≠ 0) (n : ℤ) :
    ‖coefficient H n‖ ≤ 1 := by
  unfold coefficient fourierCoeff
  calc
    _ ≤ ∫ x : Circle, ‖fourier (-n) x • (kernel H x : ℂ)‖
        ∂AddCircle.haarAddCircle := norm_integral_le_integral_norm _
    _ = ∫ x : Circle, kernel H x ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [smul_eq_mul, norm_mul, fourier_apply, Circle.norm_coe,
        one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (kernel_nonneg H x)]
    _ = 1 := integral_kernel H hH

 theorem difference_mem_frequencies {H k l : ℕ}
    (hk : k ∈ Finset.range H) (hl : l ∈ Finset.range H) :
    (k : ℤ) - (l : ℤ) ∈ frequencies H := by
  simp only [frequencies, Finset.mem_Ioo]
  simp only [Finset.mem_range] at hk hl
  omega

 theorem coefficient_expansion (H : ℕ) (n : ℤ) :
    coefficient H n = (H : ℂ)⁻¹ *
      ∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        if (k : ℤ) - (l : ℤ) = n then (1 : ℂ) else 0 := by
  unfold coefficient
  have heq : (fun x : Circle => (kernel H x : ℂ)) = fun x =>
      (H : ℂ)⁻¹ * ∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        fourier ((k : ℤ) - (l : ℤ)) x := funext (kernel_complex_expansion H)
  rw [heq, fourierCoeff.const_mul]
  congr 1
  have houter : (fun x : Circle => ∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        fourier ((k : ℤ) - (l : ℤ)) x) =
      ∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        (fun x : Circle => fourier ((k : ℤ) - (l : ℤ)) x) := by
    ext x
    simp
  rw [houter, fourierCoeff.sum]
  · simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [fourierCoeff.sum]
    · simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro l hl
      simp only [fourierCoeff_fourier, Pi.single_apply, eq_comm]
    · intro l hl
      exact integrable_fourier _
  · intro k hk
    exact integrable_finsetSum' _ (fun l hl => integrable_fourier _)

 theorem kernel_eq_finite_fourier_sum (H : ℕ) (x : Circle) :
    (kernel H x : ℂ) = ∑ n ∈ frequencies H, coefficient H n * fourier n x := by
  rw [kernel_complex_expansion]
  symm
  simp_rw [coefficient_expansion, mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    difference_mem_frequencies hk hl, ite_true, if_true]

 theorem kernel_le_chord_bound (H : ℕ) (x : Circle) (hx : fourier 1 x ≠ 1) :
    kernel H x ≤ 4 / ((H : ℝ) * ‖fourier 1 x - 1‖ ^ 2) := by
  have hb := Invariant233.norm_geometric_sum_le (fourier 1 x) hx
    (Circle.norm_coe _) H
  rw [← geometricPolynomial_eq_sum_pow] at hb
  rw [kernel, Complex.normSq_eq_norm_sq]
  have hs : ‖geometricPolynomial H x‖ ^ 2 ≤ (2 / ‖fourier 1 x - 1‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  calc
    _ ≤ (2 / ‖fourier 1 x - 1‖) ^ 2 / H :=
      div_le_div_of_nonneg_right hs (Nat.cast_nonneg H)
    _ = 4 / ((H : ℝ) * ‖fourier 1 x - 1‖ ^ 2) := by
      rw [div_pow, div_div]
      congr 1 <;> ring

 theorem chord_lower_bound_coe {t : ℝ} (ht : |t| ≤ 1 / 2) :
    4 * |t| ≤ ‖fourier 1 (t : Circle) - 1‖ := by
  have hangle : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin hangle
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  have hc : 2 * (Real.pi : ℂ) * Complex.I * (1 : ℂ) * (t : ℂ) / (1 : ℂ) =
      Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [fourier_coe_apply]
  norm_num only [Complex.ofReal_one, Int.cast_one] at *
  rw [hc, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : 2 * Real.pi * t / 2 = Real.pi * t := by ring
  rw [hhalf, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hcanc : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by
    field_simp
  rw [hcanc] at hsin
  linarith

 theorem chord_lower_bound (x : Circle) :
    4 * dist x 0 ≤ ‖fourier 1 x - 1‖ := by
  induction x using QuotientAddGroup.induction_on with
  | H t =>
    have hround : (((round t : ℤ) : ℝ) : Circle) = 0 := by
      have hc := AddCircle.coe_zsmul (p := (1 : ℝ)) (n := round t) (x := (1 : ℝ))
      simpa only [zsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using hc
    have hcoe : ((t - round t : ℝ) : Circle) = (t : Circle) := by
      rw [QuotientAddGroup.mk_sub, hround, sub_zero]
    have h := chord_lower_bound_coe (abs_sub_round t)
    rw [hcoe] at h
    simpa only [dist_zero_right, UnitAddCircle.norm_eq] using h

 theorem volume_eq_haar : (volume : Measure Circle) = AddCircle.haarAddCircle := by
  simp only [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

 theorem integral_kernel_volume (H : ℕ) (hH : H ≠ 0) :
    (∫ x : Circle, kernel H x) = 1 := by
  rw [volume_eq_haar]
  exact integral_kernel H hH

 theorem kernel_le_distance_bound (H : ℕ) (hH : H ≠ 0)
    (x : Circle) (hx : x ≠ 0) :
    kernel H x ≤ 1 / (4 * (H : ℝ) * (dist x 0) ^ 2) := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
  have hd : 0 < dist x 0 := dist_pos.mpr hx
  have hc := chord_lower_bound x
  have hcpos : 0 < ‖fourier 1 x - 1‖ := lt_of_lt_of_le (by positivity) hc
  have hxchar : fourier 1 x ≠ 1 := by
    intro heq
    simp only [heq, sub_self, norm_zero, lt_self_iff_false] at hcpos
  calc
    kernel H x ≤ 4 / ((H : ℝ) * ‖fourier 1 x - 1‖ ^ 2) :=
      kernel_le_chord_bound H x hxchar
    _ ≤ 4 / ((H : ℝ) * (4 * dist x 0) ^ 2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hc 2) hHpos.le
    _ = 1 / (4 * (H : ℝ) * (dist x 0) ^ 2) := by
      field_simp

 theorem kernel_le_of_distance_ge (H : ℕ) (hH : H ≠ 0)
    {η : ℝ} (hη : 0 < η) (x : Circle) (hx : η ≤ dist x 0) :
    kernel H x ≤ 1 / (4 * (H : ℝ) * η ^ 2) := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
  have hx0 : x ≠ 0 := by
    intro heq
    subst x
    simp only [dist_self] at hx
    linarith
  apply (kernel_le_distance_bound H hH x hx0).trans
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη.le hx 2) (by positivity)

 theorem card_frequencies_le (H : ℕ) : (frequencies H).card ≤ 2 * H := by
  simp only [frequencies, Int.card_Ioo]
  omega

 theorem coefficient_zero (H : ℕ) (hH : H ≠ 0) : coefficient H 0 = 1 := by
  simpa only [coefficient, fourierCoeff, neg_zero, fourier_zero, one_smul]
    using integral_kernel_complex H hH

end Invariant233.Fejer

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_FourierSampling
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Invariant233.FourierSampling

theorem norm_tensor_sum_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (M : ι → κ → ℂ) (ε : ℝ)
    (hM : ∀ i ∈ s, ∀ j ∈ t, ‖M i j‖ ≤ ε) :
    ‖∑ i ∈ s, ∑ j ∈ t, a i * b j * M i j‖ ≤
      (∑ i ∈ s, ‖a i‖) * (∑ j ∈ t, ‖b j‖) * ε := by
  calc
    _ ≤ ∑ i ∈ s, ‖∑ j ∈ t, a i * b j * M i j‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, ‖a i * b j * M i j‖ :=
      Finset.sum_le_sum fun i hi => norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, ‖a i‖ * ‖b j‖ * ε := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hM i hi j hj) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [← Finset.sum_mul]

theorem integrable_fourier_pair {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X Y : Ω → UnitAddCircle} (hX : Measurable X) (hY : Measurable Y)
    (i j : ℤ) : Integrable (fun ω => fourier i (X ω) * fourier j (Y ω)) μ := by
  apply Integrable.of_bound
    (((fourier i).continuous.measurable.comp hX).mul
      ((fourier j).continuous.measurable.comp hY)).aestronglyMeasurable 1
  filter_upwards with ω
  change ‖fourier i (X ω) * fourier j (Y ω)‖ ≤ 1
  rw [norm_mul]
  have hi : ‖fourier i (X ω)‖ ≤ 1 := by
    simpa only [fourier_norm] using (fourier i).norm_coe_le_norm (X ω)
  have hj : ‖fourier j (Y ω)‖ ≤ 1 := by
    simpa only [fourier_norm] using (fourier j).norm_coe_le_norm (Y ω)
  nlinarith [norm_nonneg (fourier i (X ω)), norm_nonneg (fourier j (Y ω))]

theorem integral_polynomial_mul {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X Y : Ω → UnitAddCircle} (hX : Measurable X) (hY : Measurable Y)
    (s t : Finset ℤ) (a b : ℤ → ℂ) :
    (∫ ω, polynomial s a (X ω) * polynomial t b (Y ω) ∂μ) =
      ∑ i ∈ s, ∑ j ∈ t, a i * b j *
        ∫ ω, fourier i (X ω) * fourier j (Y ω) ∂μ := by
  have hterm : ∀ i j, Integrable
      (fun ω => a i * b j * (fourier i (X ω) * fourier j (Y ω))) μ :=
    fun i j => (integrable_fourier_pair hX hY i j).const_mul _
  have hexpand : ∀ ω,
      polynomial s a (X ω) * polynomial t b (Y ω) =
      ∑ i ∈ s, ∑ j ∈ t, a i * b j * (fourier i (X ω) * fourier j (Y ω)) := by
    intro ω
    rw [polynomial, polynomial, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum s (fun i hi => integrable_finsetSum t (fun j hj => hterm i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum t (fun j hj => hterm i j)]
  simp_rw [integral_const_mul]

theorem polynomial_error_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → UnitAddCircle} (hX : Measurable X) (hY : Measurable Y)
    (s t : Finset ℤ) (hs : 0 ∈ s) (ht : 0 ∈ t) (a b : ℤ → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hchar : ∀ i ∈ s, ∀ j ∈ t, (i, j) ≠ (0, 0) →
      ‖∫ ω, fourier i (X ω) * fourier j (Y ω) ∂μ‖ ≤ ε) :
    ‖(∫ ω, polynomial s a (X ω) * polynomial t b (Y ω) ∂μ) - a 0 * b 0‖ ≤
      (∑ i ∈ s, ‖a i‖) * (∑ j ∈ t, ‖b j‖) * ε := by
  classical
  let M : ℤ → ℤ → ℂ := fun i j =>
    (∫ ω, fourier i (X ω) * fourier j (Y ω) ∂μ) - if i = 0 ∧ j = 0 then 1 else 0
  have hM : ∀ i ∈ s, ∀ j ∈ t, ‖M i j‖ ≤ ε := by
    intro i hi j hj
    by_cases h : i = 0 ∧ j = 0
    · rcases h with ⟨rfl, rfl⟩
      simpa [M] using hε
    · simpa [M, h] using hchar i hi j hj (by simpa using h)
  have hconstant : (∑ i ∈ s, ∑ j ∈ t,
      a i * b j * (if i = 0 ∧ j = 0 then (1 : ℂ) else 0)) = a 0 * b 0 := by
    rw [Finset.sum_eq_single 0]
    · simp [ht]
    · intro i hi hi0
      simp [hi0]
    · exact fun h => (h hs).elim
  rw [integral_polynomial_mul hX hY s t a b, ← hconstant]
  have heq : (∑ i ∈ s, ∑ j ∈ t, a i * b j *
      ∫ ω, fourier i (X ω) * fourier j (Y ω) ∂μ) -
      (∑ i ∈ s, ∑ j ∈ t, a i * b j * (if i = 0 ∧ j = 0 then (1 : ℂ) else 0)) =
      ∑ i ∈ s, ∑ j ∈ t, a i * b j * M i j := by
    simp only [M, mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  exact norm_tensor_sum_le s t a b M ε hM

theorem polynomial_error_le_card {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → UnitAddCircle} (hX : Measurable X) (hY : Measurable Y)
    (s t : Finset ℤ) (hs : 0 ∈ s) (ht : 0 ∈ t) (a b : ℤ → ℂ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ j ∈ t, ‖b j‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hchar : ∀ i ∈ s, ∀ j ∈ t, (i, j) ≠ (0, 0) →
      ‖∫ ω, fourier i (X ω) * fourier j (Y ω) ∂μ‖ ≤ ε) :
    ‖(∫ ω, polynomial s a (X ω) * polynomial t b (Y ω) ∂μ) - a 0 * b 0‖ ≤
      (s.card : ℝ) * t.card * ε := by
  apply (polynomial_error_le hX hY s t hs ht a b hε hchar).trans
  apply mul_le_mul_of_nonneg_right _ hε
  have has : (∑ i ∈ s, ‖a i‖) ≤ (s.card : ℝ) := by
    simpa using Finset.sum_le_sum ha
  have hbs : (∑ j ∈ t, ‖b j‖) ≤ (t.card : ℝ) := by
    simpa using Finset.sum_le_sum hb
  exact mul_le_mul has hbs (Finset.sum_nonneg fun j hj => norm_nonneg _) (by positivity)

theorem integral_product_replacement {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g p q : Ω → ℂ}
    (hfg : Integrable (fun ω => f ω * g ω) μ)
    (hpq : Integrable (fun ω => p ω * q ω) μ)
    (hfp : Integrable (fun ω => f ω - p ω) μ)
    (hgq : Integrable (fun ω => g ω - q ω) μ)
    (hg : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ 1) (hp : ∀ᵐ ω ∂μ, ‖p ω‖ ≤ 1) :
    ‖(∫ ω, f ω * g ω ∂μ) - ∫ ω, p ω * q ω ∂μ‖ ≤
      (∫ ω, ‖f ω - p ω‖ ∂μ) + ∫ ω, ‖g ω - q ω‖ ∂μ := by
  rw [← integral_sub hfg hpq, ← integral_add hfp.norm hgq.norm]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (hfg.sub hpq).norm (hfp.norm.add hgq.norm)
  filter_upwards [hg, hp] with ω hgω hpω
  calc
    ‖f ω * g ω - p ω * q ω‖ = ‖(f ω - p ω) * g ω + p ω * (g ω - q ω)‖ := by
      congr 1
      ring
    _ ≤ ‖(f ω - p ω) * g ω‖ + ‖p ω * (g ω - q ω)‖ := norm_add_le _ _
    _ ≤ ‖f ω - p ω‖ + ‖g ω - q ω‖ := by
      rw [norm_mul, norm_mul]
      have h₁ := mul_le_mul_of_nonneg_left hgω (norm_nonneg (f ω - p ω))
      have h₂ := mul_le_mul_of_nonneg_right hpω (norm_nonneg (g ω - q ω))
      simpa only [mul_one, one_mul] using add_le_add h₁ h₂

theorem test_error_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → UnitAddCircle} (hX : Measurable X) (hY : Measurable Y)
    (s t : Finset ℤ) (hs : 0 ∈ s) (ht : 0 ∈ t) (a b : ℤ → ℂ)
    {f g : Ω → ℂ}
    (hfg : Integrable (fun ω => f ω * g ω) μ)
    (hpq : Integrable (fun ω => polynomial s a (X ω) * polynomial t b (Y ω)) μ)
    (hfp : Integrable (fun ω => f ω - polynomial s a (X ω)) μ)
    (hgq : Integrable (fun ω => g ω - polynomial t b (Y ω)) μ)
    (hg : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ 1)
    (hp : ∀ᵐ ω ∂μ, ‖polynomial s a (X ω)‖ ≤ 1)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ j ∈ t, ‖b j‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hchar : ∀ i ∈ s, ∀ j ∈ t, (i, j) ≠ (0, 0) →
      ‖∫ ω, fourier i (X ω) * fourier j (Y ω) ∂μ‖ ≤ ε) :
    ‖(∫ ω, f ω * g ω ∂μ) - a 0 * b 0‖ ≤
      (∫ ω, ‖f ω - polynomial s a (X ω)‖ ∂μ) +
      (∫ ω, ‖g ω - polynomial t b (Y ω)‖ ∂μ) +
      (s.card : ℝ) * t.card * ε := by
  apply (norm_sub_le_norm_sub_add_norm_sub _ (∫ ω, polynomial s a (X ω) * polynomial t b (Y ω) ∂μ) _).trans
  exact add_le_add
    (integral_product_replacement hfg hpq hfp hgq hg hp)
    (polynomial_error_le_card hX hY s t hs ht a b ha hb hε hchar)

theorem marginal_integral_le {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} {F : Ω → X} (hF : Measurable F)
    {C : ℝ} (hC : 0 ≤ C) (hmap : μ.map F ≤ ENNReal.ofReal C • ν)
    {f : X → ℝ} (hf : Integrable f ν) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ ω, f (F ω) ∂μ) ≤ C * ∫ x, f x ∂ν := by
  have hfi := hf.smul_measure (c := ENNReal.ofReal C) ENNReal.ofReal_ne_top
  rw [← integral_map hF.aemeasurable (hfi.mono_measure hmap).aestronglyMeasurable]
  calc
    _ ≤ ∫ x, f x ∂(ENNReal.ofReal C • ν) :=
      integral_mono_measure hmap (Filter.Eventually.of_forall hf0) hfi
    _ = _ := by rw [integral_smul_measure, ENNReal.toReal_ofReal hC, smul_eq_mul]

theorem marginal_l1_error_le {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} {F : Ω → X} (hF : Measurable F)
    {C : ℝ} (hC : 0 ≤ C) (hmap : μ.map F ≤ ENNReal.ofReal C • ν)
    {f p : X → ℂ} (hfp : Integrable (fun x => f x - p x) ν) :
    (∫ ω, ‖f (F ω) - p (F ω)‖ ∂μ) ≤ C * ∫ x, ‖f x - p x‖ ∂ν :=
  marginal_integral_le hF hC hmap hfp.norm (fun _ => norm_nonneg _)

end Invariant233.FourierSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleKernelConvolution
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.CircleKernelConvolution

local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  norm_num
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem integrable_kernel (k : C(UnitAddCircle, ℝ)) : Integrable k volume := by
  apply Integrable.of_bound k.measurable.aestronglyMeasurable ‖k‖
  exact Filter.Eventually.of_forall k.norm_coe_le_norm

theorem integrable_convolution_integrand (k : C(UnitAddCircle, ℝ))
    {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (x : UnitAddCircle) :
    Integrable (fun y => k (x - y) * f y) volume := by
  apply Integrable.of_bound
    ((k.measurable.comp (measurable_const.sub measurable_id)).mul hf).aestronglyMeasurable ‖k‖
  filter_upwards with y
  change ‖k (x - y) * f y‖ ≤ ‖k‖
  rw [norm_mul, Real.norm_eq_abs (f y), abs_of_nonneg (hf0 y)]
  calc
    ‖k (x - y)‖ * f y ≤ ‖k (x - y)‖ * 1 :=
      mul_le_mul_of_nonneg_left (hf1 y) (norm_nonneg _)
    _ ≤ ‖k‖ := by simpa using k.norm_coe_le_norm (x - y)

theorem convolution_bounds (k : C(UnitAddCircle, ℝ))
    (hk0 : ∀ x, 0 ≤ k x) (hkmass : ∫ x, k x = 1)
    {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (x : UnitAddCircle) :
    0 ≤ convolution k f x ∧ convolution k f x ≤ 1 := by
  constructor
  · exact integral_nonneg fun y => mul_nonneg (hk0 _) (hf0 _)
  · have hki : Integrable (fun y => k (x - y)) volume := by
      apply Integrable.of_bound
        (k.measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable ‖k‖
      exact Filter.Eventually.of_forall fun y => k.norm_coe_le_norm _
    calc
      convolution k f x ≤ ∫ y, k (x - y) := by
        apply integral_mono (integrable_convolution_integrand k hf hf0 hf1 x) hki
        intro y
        exact mul_le_of_le_one_right (hk0 _) (hf1 _)
      _ = ∫ y, k y := integral_sub_left_eq_self k volume x
      _ = 1 := hkmass

theorem fourier_sub_argument (v : ℤ) (x y : UnitAddCircle) :
    fourier v (x - y) = fourier v x * fourier (-v) y := by
  simp [fourier_apply, sub_eq_add_neg, AddCircle.toCircle_add]

theorem integrable_test_character {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (v : ℤ) :
    Integrable (fun y => fourier v y * (f y : ℂ)) volume := by
  apply Integrable.of_bound
    ((fourier v).measurable.mul (Complex.measurable_ofReal.comp hf)).aestronglyMeasurable 1
  filter_upwards with y
  have hv : ‖fourier v y‖ = 1 := by simp [fourier_apply, Circle.norm_coe]
  change ‖fourier v y * (f y : ℂ)‖ ≤ 1
  rw [norm_mul, hv, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 y)]
  exact hf1 y

theorem norm_testCoefficient_le_one {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (v : ℤ) :
    ‖testCoefficient f v‖ ≤ 1 := by
  apply (norm_integral_le_integral_norm _).trans
  have h := integral_mono (integrable_test_character hf hf0 hf1 (-v)).norm
    (integrable_const (1 : ℝ)) (fun y => ?_)
  · simpa using h
  · have hv : ‖fourier (-v) y‖ = 1 := by simp [fourier_apply, Circle.norm_coe]
    rw [norm_mul, hv, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 y)]
    exact hf1 y

theorem convolution_eq_polynomial (k : C(UnitAddCircle, ℝ))
    (s : Finset ℤ) (c : ℤ → ℂ)
    (hk : ∀ x, (k x : ℂ) = FourierSampling.polynomial s c x)
    {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (x : UnitAddCircle) :
    (convolution k f x : ℂ) = FourierSampling.polynomial s
      (fun v => c v * testCoefficient f v) x := by
  rw [convolution, ← integral_complex_ofReal]
  simp_rw [Complex.ofReal_mul, hk, FourierSampling.polynomial, Finset.sum_mul]
  have hterm : ∀ v, Integrable (fun y => c v * fourier v (x - y) * (f y : ℂ)) volume := by
    intro v
    have he : (fun y => c v * fourier v (x - y) * (f y : ℂ)) =
        (fun y => (c v * fourier v x) * (fourier (-v) y * (f y : ℂ))) := by
      funext y
      rw [fourier_sub_argument]
      ring
    rw [he]
    exact (integrable_test_character hf hf0 hf1 (-v)).const_mul _
  rw [integral_finsetSum s (fun v hv => hterm v)]
  apply Finset.sum_congr rfl
  intro v hv
  simp_rw [fourier_sub_argument]
  have he : (fun y => c v * (fourier v x * fourier (-v) y) * (f y : ℂ)) =
      (fun y => (c v * fourier v x) * (fourier (-v) y * (f y : ℂ))) := by
    funext y
    ring
  rw [he, integral_const_mul]
  unfold testCoefficient
  ring

theorem translationError_nonneg (f : UnitAddCircle → ℝ) (t : UnitAddCircle) :
    0 ≤ translationError f t := integral_nonneg fun _ => abs_nonneg _

theorem translationError_le_one {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (t : UnitAddCircle) :
    translationError f t ≤ 1 := by
  have hb : ∀ x, |f (x - t) - f x| ≤ 1 := by
    intro x
    rw [abs_sub_le_iff]
    constructor <;> linarith [hf0 x, hf0 (x - t), hf1 x, hf1 (x - t)]
  have hi : Integrable (fun x => |f (x - t) - f x|) volume := by
    apply Integrable.of_bound
      (((hf.comp (measurable_id.sub measurable_const)).sub hf).abs).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x
  have h := integral_mono hi (integrable_const (1 : ℝ)) hb
  simpa [translationError] using h

theorem convolution_eq_shift (k : C(UnitAddCircle, ℝ)) (f : UnitAddCircle → ℝ)
    (x : UnitAddCircle) : convolution k f x = ∫ t, k t * f (x - t) := by
  have h := integral_sub_left_eq_self (fun y => k (x - y) * f y) volume x
  simpa [convolution, sub_sub_cancel] using h.symm

theorem convolution_error_pointwise_le (k : C(UnitAddCircle, ℝ))
    (hk0 : ∀ t, 0 ≤ k t) (hkmass : ∫ t, k t = 1)
    {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (x : UnitAddCircle) :
    |convolution k f x - f x| ≤ ∫ t, k t * |f (x - t) - f x| := by
  have hi : Integrable (fun t => k t * f (x - t)) volume := by
    apply Integrable.of_bound
      (k.measurable.mul (hf.comp (measurable_const.sub measurable_id))).aestronglyMeasurable ‖k‖
    filter_upwards with t
    change ‖k t * f (x - t)‖ ≤ ‖k‖
    rw [norm_mul, Real.norm_eq_abs (f (x - t)), abs_of_nonneg (hf0 _)]
    calc
      ‖k t‖ * f (x - t) ≤ ‖k t‖ * 1 := mul_le_mul_of_nonneg_left (hf1 _) (norm_nonneg _)
      _ ≤ ‖k‖ := by simpa using k.norm_coe_le_norm t
  have he : convolution k f x - f x = ∫ t, k t * (f (x - t) - f x) := by
    rw [convolution_eq_shift]
    have hc : (∫ t, k t * f x) = f x := by rw [integral_mul_const, hkmass, one_mul]
    calc
      (∫ t, k t * f (x - t)) - f x =
          (∫ t, k t * f (x - t)) - ∫ t, k t * f x := by rw [hc]
      _ = ∫ t, k t * f (x - t) - k t * f x :=
        (integral_sub hi ((integrable_kernel k).mul_const _)).symm
      _ = _ := by congr 1; funext t; ring
  rw [he]
  have h := norm_integral_le_integral_norm (μ := (volume : Measure UnitAddCircle)) (fun t => k t * (f (x - t) - f x))
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 _)] using h

theorem integrable_joint_error (k : C(UnitAddCircle, ℝ))
    {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    Integrable (fun p : UnitAddCircle × UnitAddCircle =>
      k p.2 * |f (p.1 - p.2) - f p.1|) (volume.prod volume) := by
  apply Integrable.of_bound ((k.measurable.comp measurable_snd).mul
    (((hf.comp (measurable_fst.sub measurable_snd)).sub (hf.comp measurable_fst)).abs)).aestronglyMeasurable ‖k‖
  filter_upwards with p
  change ‖k p.2 * |f (p.1 - p.2) - f p.1|‖ ≤ ‖k‖
  have hb : |f (p.1 - p.2) - f p.1| ≤ 1 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hf0 p.1, hf0 (p.1 - p.2), hf1 p.1, hf1 (p.1 - p.2)]
  simp only [norm_mul, Real.norm_eq_abs, abs_abs]
  calc
    ‖k p.2‖ * |f (p.1 - p.2) - f p.1| ≤ ‖k p.2‖ * 1 :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ ≤ ‖k‖ := by simpa using k.norm_coe_le_norm p.2

theorem l1_error_le_translation_average (k : C(UnitAddCircle, ℝ))
    (hk0 : ∀ t, 0 ≤ k t) (hkmass : ∫ t, k t = 1)
    {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    (∫ x, |convolution k f x - f x|) ≤ ∫ t, k t * translationError f t := by
  calc
    _ ≤ ∫ x, ∫ t, k t * |f (x - t) - f x| := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (integrable_joint_error k hf hf0 hf1).integral_prod_left
      exact Filter.Eventually.of_forall (convolution_error_pointwise_le k hk0 hkmass hf hf0 hf1)
    _ = ∫ t, ∫ x, k t * |f (x - t) - f x| :=
      integral_integral_swap (integrable_joint_error k hf hf0 hf1)
    _ = _ := by simp_rw [integral_const_mul, translationError]

theorem l1_error_le_small_translation_and_tail (k : C(UnitAddCircle, ℝ))
    (hk0 : ∀ t, 0 ≤ k t) (hkmass : ∫ t, k t = 1)
    {f : UnitAddCircle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    {B : Set UnitAddCircle} (hB : MeasurableSet B) {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hsmall : ∀ t ∈ B, translationError f t ≤ δ)
    (htail : (∫ t in Bᶜ, k t) ≤ ε) :
    (∫ x, |convolution k f x - f x|) ≤ δ + ε := by
  apply (l1_error_le_translation_average k hk0 hkmass hf hf0 hf1).trans
  calc
    (∫ t, k t * translationError f t) ≤ ∫ t, δ * k t + Bᶜ.indicator k t := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun t => mul_nonneg (hk0 t) (translationError_nonneg f t))
        (((integrable_kernel k).const_mul δ).add ((integrable_kernel k).indicator hB.compl))
      filter_upwards with t
      change k t * translationError f t ≤ δ * k t + Bᶜ.indicator k t
      by_cases ht : t ∈ B
      · rw [Set.indicator_of_notMem (show t ∉ Bᶜ from fun h => h ht), add_zero]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left (hsmall t ht) (hk0 t)
      · rw [Set.indicator_of_mem (Set.mem_compl ht)]
        have h₁ := mul_le_mul_of_nonneg_left (translationError_le_one hf hf0 hf1 t) (hk0 t)
        have h₂ := mul_nonneg hδ (hk0 t)
        nlinarith
    _ = δ + ∫ t in Bᶜ, k t := by
      rw [integral_add ((integrable_kernel k).const_mul δ)
        ((integrable_kernel k).indicator hB.compl), integral_const_mul,
        hkmass, mul_one, integral_indicator hB.compl]
    _ ≤ δ + ε := add_le_add le_rfl htail

end Invariant233.CircleKernelConvolution

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FejerApproximation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.Fejer

theorem approximation_bounds (H : ℕ) (hH : H ≠ 0)
    {f : Circle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (x : Circle) :
    0 ≤ approximation H f x ∧ approximation H f x ≤ 1 :=
  CircleKernelConvolution.convolution_bounds (bundledKernel H)
    (kernel_nonneg H) (integral_kernel_volume H hH) hf hf0 hf1 x

theorem approximation_eq_polynomial (H : ℕ)
    {f : Circle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (x : Circle) :
    (approximation H f x : ℂ) = FourierSampling.polynomial (frequencies H)
      (approximationCoefficient H f) x :=
  CircleKernelConvolution.convolution_eq_polynomial (bundledKernel H)
    (frequencies H) (coefficient H) (kernel_eq_finite_fourier_sum H) hf hf0 hf1 x

theorem approximationCoefficient_norm_le_one (H : ℕ) (hH : H ≠ 0)
    {f : Circle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (v : ℤ) :
    ‖approximationCoefficient H f v‖ ≤ 1 := by
  rw [approximationCoefficient, norm_mul]
  have h₁ := coefficient_norm_le_one H hH v
  have h₂ := CircleKernelConvolution.norm_testCoefficient_le_one hf hf0 hf1 v
  change ‖coefficient H v‖ * ‖CircleKernelConvolution.testCoefficient f v‖ ≤ 1
  nlinarith [norm_nonneg (coefficient H v), norm_nonneg (CircleKernelConvolution.testCoefficient f v)]

@[simp] theorem approximationCoefficient_zero (H : ℕ) (hH : H ≠ 0) (f : Circle → ℝ) :
    approximationCoefficient H f 0 = (∫ x, f x : ℝ) := by
  simp [approximationCoefficient, coefficient_zero H hH, integral_complex_ofReal]

theorem continuous_approximation (H : ℕ)
    {f : Circle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    Continuous (approximation H f) := by
  have hpoly : Continuous (fun x : Circle =>
      FourierSampling.polynomial (frequencies H) (approximationCoefficient H f) x) := by
    unfold FourierSampling.polynomial
    exact continuous_finsetSum _ (fun v hv => continuous_const.mul (fourier v).continuous)
  have heq : approximation H f = fun x =>
      (FourierSampling.polynomial (frequencies H) (approximationCoefficient H f) x).re := by
    funext x
    rw [← approximation_eq_polynomial H hf hf0 hf1 x]
    rfl
  rw [heq]
  exact Complex.continuous_re.comp hpoly

theorem approximation_l1_error_le (H : ℕ) (hH : H ≠ 0)
    {f : Circle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    {B : Set Circle} (hB : MeasurableSet B) {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hsmall : ∀ t ∈ B, CircleKernelConvolution.translationError f t ≤ δ)
    (htail : (∫ t in Bᶜ, kernel H t) ≤ ε) :
    (∫ x, |approximation H f x - f x|) ≤ δ + ε :=
  CircleKernelConvolution.l1_error_le_small_translation_and_tail (bundledKernel H)
    (kernel_nonneg H) (integral_kernel_volume H hH) hf hf0 hf1 hB hδ hsmall htail

end Invariant233.Fejer

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_IntervalIndicatorTranslation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory

namespace Invariant233.IntervalIndicatorTranslation

theorem differing_membership_subset_strips {a b t η : ℝ} (hη : 0 ≤ η)
    (ht : |t| ≤ η) :
    {x : ℝ | x ∈ Ico 0 1 ∧
        ¬ (Int.fract (x - t) ∈ Icc a b ↔ x ∈ Icc a b)} ⊆
      Icc 0 η ∪ Icc (1 - η) 1 ∪ Icc (a - η) (a + η) ∪ Icc (b - η) (b + η) := by
  intro x hx
  by_contra hn
  have ht' := abs_le.mp ht
  have hx0 := hx.1.1
  have hx1 := hx.1.2
  have hn0 : x ∉ Icc 0 η := by exact fun h => hn (Or.inl (Or.inl (Or.inl h)))
  have hn1 : x ∉ Icc (1 - η) 1 := by exact fun h => hn (Or.inl (Or.inl (Or.inr h)))
  have hna : x ∉ Icc (a - η) (a + η) := by exact fun h => hn (Or.inl (Or.inr h))
  have hnb : x ∉ Icc (b - η) (b + η) := by exact fun h => hn (Or.inr h)
  have hxη : η < x := by
    by_contra h
    exact hn0 ⟨hx0, le_of_not_gt h⟩
  have hxη' : x < 1 - η := by
    by_contra h
    exact hn1 ⟨le_of_not_gt h, hx1.le⟩
  have hfract : Int.fract (x - t) = x - t := by
    apply Int.fract_eq_self.mpr
    constructor <;> linarith
  apply hx.2
  rw [hfract]
  constructor
  · intro hxt
    constructor
    · by_contra h
      apply hna
      constructor <;> linarith [hxt.1]
    · by_contra h
      apply hnb
      constructor <;> linarith [hxt.2]
  · intro hxI
    constructor
    · by_contra h
      apply hna
      constructor <;> linarith [hxI.1]
    · by_contra h
      apply hnb
      constructor <;> linarith [hxI.2]

theorem measure_differing_membership_le {a b t η : ℝ} (hη : 0 ≤ η) (ht : |t| ≤ η) :
    volume.real {x : ℝ | x ∈ Ico 0 1 ∧
      ¬ (Int.fract (x - t) ∈ Icc a b ↔ x ∈ Icc a b)} ≤ 6 * η := by
  have hfinite : volume (Icc (0 : ℝ) η ∪ Icc (1 - η) 1 ∪
      Icc (a - η) (a + η) ∪ Icc (b - η) (b + η)) ≠ ⊤ :=
    (((isCompact_Icc.union isCompact_Icc).union isCompact_Icc).union isCompact_Icc).measure_ne_top
  calc
    _ ≤ volume.real (Icc (0 : ℝ) η ∪ Icc (1 - η) 1 ∪
        Icc (a - η) (a + η) ∪ Icc (b - η) (b + η)) :=
      measureReal_mono (differing_membership_subset_strips hη ht) hfinite
    _ ≤ (volume.real (Icc (0 : ℝ) η) + volume.real (Icc (1 - η) 1)) +
        volume.real (Icc (a - η) (a + η)) + volume.real (Icc (b - η) (b + η)) := by
      calc
        _ ≤ volume.real (Icc (0 : ℝ) η ∪ Icc (1 - η) 1 ∪ Icc (a - η) (a + η)) +
            volume.real (Icc (b - η) (b + η)) := measureReal_union_le _ _
        _ ≤ (volume.real (Icc (0 : ℝ) η ∪ Icc (1 - η) 1) +
            volume.real (Icc (a - η) (a + η))) + volume.real (Icc (b - η) (b + η)) :=
          by
            have h := measureReal_union_le (μ := volume)
              (Icc (0 : ℝ) η ∪ Icc (1 - η) 1) (Icc (a - η) (a + η))
            linarith
        _ ≤ _ := by
          have h := measureReal_union_le (μ := volume) (Icc (0 : ℝ) η) (Icc (1 - η) 1)
          linarith
    _ = 6 * η := by
      rw [Real.volume_real_Icc_of_le hη,
        Real.volume_real_Icc_of_le (show 1 - η ≤ (1 : ℝ) by linarith),
        Real.volume_real_Icc_of_le (show a - η ≤ a + η by linarith),
        Real.volume_real_Icc_of_le (show b - η ≤ b + η by linarith)]
      ring

theorem integral_indicator_translation_le {a b t η : ℝ} (hη : 0 ≤ η) (ht : |t| ≤ η) :
    (∫ x in (0 : ℝ)..1,
      |(Icc a b).indicator (fun _ => (1 : ℝ)) (Int.fract (x - t)) -
       (Icc a b).indicator (fun _ => (1 : ℝ)) (Int.fract x)|) ≤ 6 * η := by
  classical
  let s : Set ℝ := {x | ¬ (Int.fract (x - t) ∈ Icc a b ↔ x ∈ Icc a b)}
  have hs : MeasurableSet s := by
    apply MeasurableSet.compl
    exact (measurableSet_Icc.preimage (measurable_fract.comp (measurable_id.sub_const t))).iff
      measurableSet_Icc
  have heq : (∫ x in (0 : ℝ)..1,
      |(Icc a b).indicator (fun _ => (1 : ℝ)) (Int.fract (x - t)) -
       (Icc a b).indicator (fun _ => (1 : ℝ)) (Int.fract x)|) =
      ∫ x in (0 : ℝ)..1, s.indicator (fun _ => (1 : ℝ)) x := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    dsimp only
    rw [Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩]
    simp only [Set.indicator_apply, s, Set.mem_ofPred_eq]
    by_cases h1 : Int.fract (x - t) ∈ Icc a b <;>
      by_cases h2 : x ∈ Icc a b <;> simp [h1, h2]
  rw [heq, intervalIntegral.integral_of_le (by norm_num),
    ← integral_Ico_eq_integral_Ioc, integral_indicator_const 1 hs, measureReal_restrict_apply hs]
  simp only [smul_eq_mul, mul_one]
  have hset : s ∩ Ico 0 1 = {x : ℝ | x ∈ Ico 0 1 ∧
      ¬ (Int.fract (x - t) ∈ Icc a b ↔ x ∈ Icc a b)} := by
    ext x
    exact and_comm
  rw [hset]
  exact measure_differing_membership_le hη ht

theorem circle_integral_indicator_translation_le {a b t η : ℝ}
    (hη : 0 ≤ η) (ht : |t| ≤ η) :
    (∫ x : UnitAddCircle,
      |(Icc a b).indicator (fun _ => (1 : ℝ))
          (AddCircle.equivIco (1 : ℝ) 0 (x - (t : UnitAddCircle)) : ℝ) -
       (Icc a b).indicator (fun _ => (1 : ℝ))
          (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)|) ≤ 6 * η := by
  have h := UnitAddCircle.intervalIntegral_preimage 0 (fun x : UnitAddCircle =>
      |(Icc a b).indicator (fun _ => (1 : ℝ))
          (AddCircle.equivIco (1 : ℝ) 0 (x - (t : UnitAddCircle)) : ℝ) -
       (Icc a b).indicator (fun _ => (1 : ℝ))
          (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)|)
  rw [← h]
  have heq (x : ℝ) :
      (AddCircle.equivIco (1 : ℝ) 0 ((x : UnitAddCircle) - (t : UnitAddCircle)) : ℝ) =
        Int.fract (x - t) := by
    rw [← AddCircle.coe_sub]
    simpa using AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) (x - t)
  have heq' (x : ℝ) : (AddCircle.equivIco (1 : ℝ) 0 (x : UnitAddCircle) : ℝ) =
      Int.fract x := by
    simp
  simpa only [zero_add, heq, heq'] using integral_indicator_translation_le hη ht

end Invariant233.IntervalIndicatorTranslation

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ModuloIntervalMeasure
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

theorem cond_Icc_eq_cond_Ioc (a b : ℝ) :
    ProbabilityTheory.cond volume (Icc a b) = ProbabilityTheory.cond volume (Ioc a b) := by
  simp only [ProbabilityTheory.cond, Real.volume_Icc, Real.volume_Ioc]
  rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume)).symm]

end Invariant233.ModuloIntervalMeasure

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_PeriodicIntervalDiscrepancy
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.PeriodicIntervalDiscrepancy

open Set MeasureTheory
open scoped ENNReal

theorem length_sub_one_mul_integral_le {f : ℝ → ℝ}
    (hperiod : Function.Periodic f 1) (hf : ∀ x, 0 ≤ f x)
    (hint : IntervalIntegrable f volume 0 1) {a b : ℝ} (hab : a ≤ b) :
    (b - a - 1) * (∫ x in (0 : ℝ)..1, f x) ≤ ∫ x in a..b, f x := by
  let n : ℕ := ⌊b - a⌋₊
  have hn : a + n ≤ b := by
    have := Nat.floor_le (sub_nonneg.mpr hab)
    dsimp [n]
    linarith
  have hn' : b - a - 1 ≤ (n : ℝ) := (Nat.sub_one_lt_floor (b - a)).le
  have hint' := hperiod.intervalIntegrable₀ (by norm_num : (1 : ℝ) ≠ 0) hint
  have hmass : 0 ≤ ∫ x in (0 : ℝ)..1, f x :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) hf
  calc
    (b - a - 1) * (∫ x in (0 : ℝ)..1, f x) ≤
        (n : ℝ) * (∫ x in (0 : ℝ)..1, f x) :=
      mul_le_mul_of_nonneg_right hn' hmass
    _ = ∫ x in a..a + n, f x := by
      have h := hperiod.intervalIntegral_add_zsmul_eq (n : ℤ) a hint'
      simpa only [zsmul_eq_mul, Int.cast_natCast, mul_one,
        hperiod.intervalIntegral_add_eq a 0, zero_add] using h.symm
    _ ≤ ∫ x in a..b, f x :=
      intervalIntegral.integral_mono_interval le_rfl (le_add_of_nonneg_right (Nat.cast_nonneg n)) hn
        (Filter.Eventually.of_forall hf) (hint' _ _)

theorem abs_integral_sub_length_mul_integral_le {f : ℝ → ℝ}
    (hperiod : Function.Periodic f 1) (hint : IntervalIntegrable f volume 0 1)
    {a b : ℝ} (hab : a ≤ b) :
    |(∫ x in a..b, f x) - (b - a) * (∫ x in (0 : ℝ)..1, f x)| ≤
      ∫ x in (0 : ℝ)..1, |f x| := by
  have hperiodAbs : Function.Periodic (fun x => |f x|) 1 := by
    intro x
    change |f (x + 1)| = |f x|
    rw [hperiod x]
  have hp : ∀ x, 0 ≤ |f x| + f x := fun x => by linarith [neg_abs_le (f x)]
  have hm : ∀ x, 0 ≤ |f x| - f x := fun x => sub_nonneg.mpr (le_abs_self (f x))
  have hint' := hperiod.intervalIntegrable₀ (by norm_num : (1 : ℝ) ≠ 0) hint
  have hpu := ModuloIntervalMeasure.integral_periodic_le_length_add_one
    (hperiodAbs.add hperiod) hp (hint.abs.add hint) hab
  have hpl := length_sub_one_mul_integral_le
    (hperiodAbs.add hperiod) hp (hint.abs.add hint) hab
  have hmu := ModuloIntervalMeasure.integral_periodic_le_length_add_one
    (hperiodAbs.sub hperiod) hm (hint.abs.sub hint) hab
  have hml := length_sub_one_mul_integral_le
    (hperiodAbs.sub hperiod) hm (hint.abs.sub hint) hab
  simp only [Pi.add_apply, Pi.sub_apply] at hpu hpl hmu hml
  rw [intervalIntegral.integral_add (hint' a b).abs (hint' a b),
    intervalIntegral.integral_add hint.abs hint] at hpu hpl
  rw [intervalIntegral.integral_sub (hint' a b).abs (hint' a b),
    intervalIntegral.integral_sub hint.abs hint] at hmu hml
  apply abs_le.mpr
  constructor <;> nlinarith

theorem integral_cond_Ioc {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) :
    (∫ x, f x ∂ProbabilityTheory.cond volume (Ioc a b)) =
      (b - a)⁻¹ * ∫ x in a..b, f x := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
    Real.volume_Ioc, ENNReal.toReal_ofReal (sub_pos.mpr hab).le,
    intervalIntegral.integral_of_le hab.le, smul_eq_mul]

theorem abs_integral_cond_sub_integral_le {f : ℝ → ℝ}
    (hperiod : Function.Periodic f 1) (hint : IntervalIntegrable f volume 0 1)
    {a b : ℝ} (hab : a < b) :
    |(∫ x, f x ∂ProbabilityTheory.cond volume (Ioc a b)) -
        (∫ x in (0 : ℝ)..1, f x)| ≤
      (b - a)⁻¹ * ∫ x in (0 : ℝ)..1, |f x| := by
  have hlen : 0 < b - a := sub_pos.mpr hab
  rw [integral_cond_Ioc hab]
  calc
    |(b - a)⁻¹ * (∫ x in a..b, f x) - (∫ x in (0 : ℝ)..1, f x)| =
        (b - a)⁻¹ * |(∫ x in a..b, f x) -
          (b - a) * (∫ x in (0 : ℝ)..1, f x)| := by
      have heq : (b - a)⁻¹ * (∫ x in a..b, f x) - (∫ x in (0 : ℝ)..1, f x) =
          (b - a)⁻¹ * ((∫ x in a..b, f x) -
            (b - a) * (∫ x in (0 : ℝ)..1, f x)) := by
        rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hlen.ne', one_mul]
      rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hlen)]
    _ ≤ (b - a)⁻¹ * ∫ x in (0 : ℝ)..1, |f x| :=
      mul_le_mul_of_nonneg_left
        (abs_integral_sub_length_mul_integral_le hperiod hint hab.le)
        (inv_nonneg.mpr hlen.le)

theorem fract_comp_eqOn {E : Type*} (g : ℝ → E) :
    EqOn (fun x => g (Int.fract x)) g (Ioo 0 1) := by
  intro x hx
  change g (Int.fract x) = g x
  rw [Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩]

theorem intervalIntegrable_fract_comp {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 1) :
    IntervalIntegrable (fun x => g (Int.fract x)) volume 0 1 := by
  apply hg.congr_uIoo
  simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using (fract_comp_eqOn g).symm

theorem integral_cond_Ioc_mul {f : ℝ → ℝ} {a b k : ℝ}
    (hab : a < b) (hk : 0 < k) :
    (∫ x, f (k * x) ∂ProbabilityTheory.cond volume (Ioc a b)) =
      ∫ x, f x ∂ProbabilityTheory.cond volume (Ioc (k * a) (k * b)) := by
  rw [integral_cond_Ioc hab, integral_cond_Ioc (mul_lt_mul_of_pos_left hab hk),
    intervalIntegral.integral_comp_mul_left f hk.ne', smul_eq_mul]
  rw [← mul_sub, mul_inv_rev, mul_assoc]

theorem uniform_angle_test_le {N n : ℝ} (hN : 0 < N) (hn : 0 < n)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 1) :
    |(∫ θ, g (Int.fract (n * θ))
        ∂ProbabilityTheory.cond volume (Icc (1 / N) (2 / N))) -
      (∫ t in (0 : ℝ)..1, g t)| ≤ (N / n) * ∫ t in (0 : ℝ)..1, |g t| := by
  have hab : (1 : ℝ) / N < 2 / N :=
    (div_lt_div_iff_of_pos_right hN).mpr (by norm_num)
  have hperiod : Function.Periodic (fun x => g (Int.fract x)) 1 := by
    intro x
    simp only [Int.fract_add_one]
  have h := abs_integral_cond_sub_integral_le hperiod
    (intervalIntegrable_fract_comp hg) (mul_lt_mul_of_pos_left hab hn)
  have hmean : (∫ t in (0 : ℝ)..1, g (Int.fract t)) = ∫ t in (0 : ℝ)..1, g t :=
    intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fract_comp_eqOn g)
  have habs : (∫ t in (0 : ℝ)..1, |g (Int.fract t)|) =
      ∫ t in (0 : ℝ)..1, |g t| :=
    intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fract_comp_eqOn (fun t => |g t|))
  have hlen : (n * (2 / N) - n * (1 / N))⁻¹ = N / n := by
    rw [← mul_sub, ← sub_div, show (2 : ℝ) - 1 = 1 by norm_num]
    field_simp
  rw [hmean, habs, hlen] at h
  rw [ModuloIntervalMeasure.cond_Icc_eq_cond_Ioc,
    integral_cond_Ioc_mul (f := fun x => g (Int.fract x)) hab hn]
  exact h

end Invariant233.PeriodicIntervalDiscrepancy

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_UniformIntervalFourier
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Invariant233.UniformIntervalFourier

theorem norm_integral_exp_mul_I_le {ξ : ℝ} (hξ : ξ ≠ 0) (a b : ℝ) :
    ‖∫ t in a..b, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I)‖ ≤ 2 / |ξ| := by
  have hc : (ξ : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hξ) Complex.I_ne_zero
  have heq : (fun t : ℝ => Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I)) =
      (fun t : ℝ => Complex.exp (((ξ : ℂ) * Complex.I) * t)) := by
    funext t
    congr 1
    push_cast
    ring
  have hn (t : ℝ) : ‖Complex.exp (((ξ : ℂ) * Complex.I) * t)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  rw [heq, integral_exp_mul_complex hc, norm_div]
  have hnum : ‖Complex.exp (((ξ : ℂ) * Complex.I) * b) -
      Complex.exp (((ξ : ℂ) * Complex.I) * a)‖ ≤ 2 := by
    simpa only [hn, one_add_one_eq_two] using norm_sub_le
      (Complex.exp (((ξ : ℂ) * Complex.I) * b))
      (Complex.exp (((ξ : ℂ) * Complex.I) * a))
  simpa only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs] using
    div_le_div_of_nonneg_right hnum (norm_nonneg ((ξ : ℂ) * Complex.I))

theorem norm_normalized_integral_exp_mul_I_le {ξ a b : ℝ}
    (hξ : ξ ≠ 0) (hab : a < b) :
    ‖(b - a)⁻¹ • (∫ t in a..b, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I))‖ ≤
      2 / (|ξ| * (b - a)) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (sub_pos.mpr hab))]
  calc
    (b - a)⁻¹ * ‖∫ t in a..b, Complex.exp (((ξ * t : ℝ) : ℂ) * Complex.I)‖ ≤
        (b - a)⁻¹ * (2 / |ξ|) :=
      mul_le_mul_of_nonneg_left (norm_integral_exp_mul_I_le hξ a b)
        (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
    _ = 2 / (|ξ| * (b - a)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem norm_normalized_circle_character_le {ξ a b : ℝ}
    (hξ : ξ ≠ 0) (hab : a < b) :
    ‖(b - a)⁻¹ • (∫ t in a..b,
      Complex.exp ((((2 * Real.pi * ξ) * t : ℝ) : ℂ) * Complex.I))‖ ≤
      1 / (Real.pi * |ξ| * (b - a)) := by
  have hfreq : 2 * Real.pi * ξ ≠ 0 := mul_ne_zero (by positivity) hξ
  have h := norm_normalized_integral_exp_mul_I_le hfreq hab
  have ha : |2 * Real.pi * ξ| = 2 * Real.pi * |ξ| := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  rw [ha] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem integral_uniform_interval_eq {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℂ) :
    (∫ t, f t ∂ProbabilityTheory.cond volume (Set.Icc a b)) =
      (b - a)⁻¹ • (∫ t in a..b, f t) := by
  rw [ProbabilityTheory.cond, integral_smul_measure, Real.volume_Icc,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

theorem norm_uniform_interval_circle_character_le {ξ a b : ℝ}
    (hξ : ξ ≠ 0) (hab : a < b) :
    ‖∫ t, Complex.exp ((((2 * Real.pi * ξ) * t : ℝ) : ℂ) * Complex.I)
      ∂ProbabilityTheory.cond volume (Set.Icc a b)‖ ≤
        1 / (Real.pi * |ξ| * (b - a)) := by
  rw [integral_uniform_interval_eq hab.le]
  exact norm_normalized_circle_character_le hξ hab

theorem norm_sampling_interval_character_le {ξ N₀ : ℝ}
    (hξ : ξ ≠ 0) (hN₀ : 0 < N₀) :
    ‖∫ t, Complex.exp ((((2 * Real.pi * ξ) * t : ℝ) : ℂ) * Complex.I)
      ∂ProbabilityTheory.cond volume (Set.Icc (1 / N₀) (2 / N₀))‖ ≤
        N₀ / (Real.pi * |ξ|) := by
  have hab : 1 / N₀ < 2 / N₀ := (div_lt_div_iff_of_pos_right hN₀).2 (by norm_num)
  have h := norm_uniform_interval_circle_character_le hξ hab
  have hlen : 2 / N₀ - 1 / N₀ = 1 / N₀ := by ring
  rw [hlen] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]

theorem norm_sampling_interval_character_le_of_separation {ξ N₀ N m : ℝ}
    (hN₀ : 0 < N₀) (hN : N₀ ≤ N) (hm : 0 < m)
    (hsep : N * m ^ 1000 < |ξ|) :
    ‖∫ t, Complex.exp ((((2 * Real.pi * ξ) * t : ℝ) : ℂ) * Complex.I)
      ∂ProbabilityTheory.cond volume (Set.Icc (1 / N₀) (2 / N₀))‖ ≤
        1 / (Real.pi * m ^ 1000) := by
  have hNpos : 0 < N := lt_of_lt_of_le hN₀ hN
  have hξpos : 0 < |ξ| := lt_trans (mul_pos hNpos (pow_pos hm _)) hsep
  have hξ : ξ ≠ 0 := abs_pos.mp hξpos
  calc
    _ ≤ N₀ / (Real.pi * |ξ|) := norm_sampling_interval_character_le hξ hN₀
    _ ≤ N / (Real.pi * |ξ|) :=
      div_le_div_of_nonneg_right hN (mul_nonneg Real.pi_pos.le (abs_nonneg _))
    _ ≤ 1 / (Real.pi * m ^ 1000) := by
      apply (div_le_div_iff₀ (mul_pos Real.pi_pos hξpos)
        (mul_pos Real.pi_pos (pow_pos hm _))).2
      have hh := mul_le_mul_of_nonneg_left hsep.le Real.pi_pos.le
      nlinarith only [hh]

end Invariant233.UniformIntervalFourier

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_UniformIntervalPhase
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.UniformIntervalPhase

theorem map_interval_nat (a : ℝ) (n : ℕ) :
    (volume.restrict (Ioc a (a + n))).map (fun x : ℝ => (x : UnitAddCircle)) =
      (n : ℝ≥0∞) • (volume : Measure UnitAddCircle) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : Ioc a (a + (n + 1 : ℕ)) =
        Ioc a (a + n) ∪ Ioc (a + n) (a + n + 1) := by
      rw [Ioc_union_Ioc_eq_Ioc (by linarith [Nat.cast_nonneg (α := ℝ) n] : a ≤ a + (n : ℝ)) (by linarith)]
      congr 1
      push_cast
      ring
    rw [hsplit, Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Measure.map_add _ _ AddCircle.measurable_mk', ih]
    rw [(UnitAddCircle.measurePreserving_mk (a + n)).map_eq]
    simp [Nat.cast_add, add_smul]

theorem map_interval_sandwich (a L : ℝ) (hL : 0 ≤ L) :
    (⌊L⌋₊ : ℝ≥0∞) • (volume : Measure UnitAddCircle) ≤
        (volume.restrict (Ioc a (a + L))).map (fun x : ℝ => (x : UnitAddCircle)) ∧
      (volume.restrict (Ioc a (a + L))).map (fun x : ℝ => (x : UnitAddCircle)) ≤
        ((⌊L⌋₊ : ℝ≥0∞) + 1) • (volume : Measure UnitAddCircle) := by
  constructor
  · rw [← map_interval_nat a ⌊L⌋₊]
    apply Measure.map_mono _ AddCircle.measurable_mk'
    apply Measure.restrict_mono _ le_rfl
    exact Ioc_subset_Ioc_right (by linarith [Nat.floor_le hL])
  · calc
      _ ≤ (volume.restrict (Ioc a (a + (⌊L⌋₊ + 1 : ℕ)))).map
          (fun x : ℝ => (x : UnitAddCircle)) := by
        apply Measure.map_mono _ AddCircle.measurable_mk'
        apply Measure.restrict_mono _ le_rfl
        apply Ioc_subset_Ioc_right
        have h := (Nat.lt_floor_add_one L).le
        push_cast
        linarith
      _ = _ := by rw [map_interval_nat]; simp

theorem rnDeriv_le_const_of_le_smul
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X} [SigmaFinite ν]
    {c : ℝ≥0∞} (h : μ ≤ c • ν) :
    ∀ᵐ x ∂ν, μ.rnDeriv ν x ≤ c := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν)
  intro s hs hfinite
  calc
    (∫⁻ x in s, μ.rnDeriv ν x ∂ν) ≤ μ s := Measure.setLIntegral_rnDeriv_le s
    _ ≤ (c • ν) s := h s
    _ = ∫⁻ _ in s, c ∂ν := by simp

theorem const_le_rnDeriv_of_smul_le
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    [Measure.HaveLebesgueDecomposition μ ν] [SigmaFinite ν]
    {c : ℝ≥0∞} (hac : μ ≪ ν) (h : c • ν ≤ μ) :
    ∀ᵐ x ∂ν, c ≤ μ.rnDeriv ν x := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_const
  intro s hs hfinite
  calc
    (∫⁻ _ in s, c ∂ν) = (c • ν) s := by simp
    _ ≤ μ s := h s
    _ = ∫⁻ x in s, μ.rnDeriv ν x ∂ν := (Measure.setLIntegral_rnDeriv' hac hs).symm

theorem phaseLaw_sandwich (a L : ℝ) (hL : 0 < L) :
    ENNReal.ofReal ((⌊L⌋₊ : ℝ) / L) • (volume : Measure UnitAddCircle) ≤ phaseLaw a L ∧
      phaseLaw a L ≤ ENNReal.ofReal (((⌊L⌋₊ : ℝ) + 1) / L) •
        (volume : Measure UnitAddCircle) := by
  have h := map_interval_sandwich a L hL.le
  have hlow := smul_le_smul_left (ENNReal.ofReal (1 / L)) h.1
  have hupp := smul_le_smul_left (ENNReal.ofReal (1 / L)) h.2
  have hc0 : 0 ≤ 1 / L := by positivity
  have hlo : ENNReal.ofReal (1 / L) * (⌊L⌋₊ : ℝ≥0∞) =
      ENNReal.ofReal ((⌊L⌋₊ : ℝ) / L) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hc0]
    congr 1
    ring
  have hup : ENNReal.ofReal (1 / L) * ((⌊L⌋₊ : ℝ≥0∞) + 1) =
      ENNReal.ofReal (((⌊L⌋₊ : ℝ) + 1) / L) := by
    have hn : (⌊L⌋₊ : ℝ≥0∞) + 1 = ENNReal.ofReal ((⌊L⌋₊ : ℝ) + 1) := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num)]
      simp
    rw [hn, ← ENNReal.ofReal_mul hc0]
    congr 1
    ring
  constructor
  · simpa only [phaseLaw, intervalLaw,
      Measure.map_smul, smul_smul, hlo] using hlow
  · simpa only [phaseLaw, intervalLaw,
      Measure.map_smul, smul_smul, hup] using hupp

theorem real_density_spec_of_sandwich {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure ν] (L : ℝ) (hL : 0 < L)
    (hlow : ENNReal.ofReal ((⌊L⌋₊ : ℝ) / L) • ν ≤ μ)
    (hupp : μ ≤ ENNReal.ofReal (((⌊L⌋₊ : ℝ) + 1) / L) • ν) :
    Measurable (fun x => (μ.rnDeriv ν x).toReal) ∧
      (∀ᵐ x ∂ν, 0 ≤ (μ.rnDeriv ν x).toReal ∧
        |(μ.rnDeriv ν x).toReal - 1| ≤ 1 / L) ∧
      ν.withDensity (fun x => ENNReal.ofReal (μ.rnDeriv ν x).toReal) = μ := by
  let : IsFiniteMeasure (ENNReal.ofReal (((⌊L⌋₊ : ℝ) + 1) / L) •
      ν) := ν.smul_finite ENNReal.ofReal_ne_top
  let : IsFiniteMeasure μ :=
    isFiniteMeasure_of_le (ENNReal.ofReal (((⌊L⌋₊ : ℝ) + 1) / L) • ν) hupp
  have hac : μ ≪ ν :=
    Measure.absolutelyContinuous_of_le_smul hupp
  have hlo := const_le_rnDeriv_of_smul_le hac hlow
  have hup := rnDeriv_le_const_of_le_smul hupp
  have hfinite : ∀ᵐ x ∂ν,
      μ.rnDeriv ν x ≠ ⊤ := by
    filter_upwards [hup] with x hx
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
  refine ⟨(μ.measurable_rnDeriv ν).ennreal_toReal, ?_, ?_⟩
  · filter_upwards [hlo, hup, hfinite] with x hxlo hxup hxfin
    have hrlo : (⌊L⌋₊ : ℝ) / L ≤ (μ.rnDeriv ν x).toReal := by
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (⌊L⌋₊ : ℝ) / L)]
        using ENNReal.toReal_mono hxfin hxlo
    have hrup : (μ.rnDeriv ν x).toReal ≤ ((⌊L⌋₊ : ℝ) + 1) / L := by
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ ((⌊L⌋₊ : ℝ) + 1) / L)]
        using ENNReal.toReal_mono ENNReal.ofReal_ne_top hxup
    have hfloor := Nat.floor_le hL.le
    have hceil := Nat.lt_floor_add_one L
    have hrlo' := (div_le_iff₀ hL).mp hrlo
    have hrup' := (le_div_iff₀ hL).mp hrup
    have hinv : (1 / L) * L = 1 := by field_simp
    refine ⟨ENNReal.toReal_nonneg, abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith
  · calc
      _ = ν.withDensity (μ.rnDeriv ν) := by
        apply withDensity_congr_ae
        filter_upwards [hfinite] with x hx
        exact ENNReal.ofReal_toReal hx
      _ = μ := Measure.withDensity_rnDeriv_eq _ _ hac

theorem intervalLaw_map_mul (a L c : ℝ) (hL : 0 < L) (hc : 0 < c) :
    (intervalLaw a L).map (fun x => c * x) = intervalLaw (c * a) (c * L) := by
  have hpre : (fun x : ℝ => c * x) ⁻¹' Ioc (c * a) (c * (a + L)) =
      Ioc a (a + L) := by
    ext x
    simp only [mem_preimage, mem_Ioc, mul_lt_mul_iff_of_pos_left hc, mul_le_mul_iff_of_pos_left hc]
  have hm := (measurableEmbedding_mulLeft₀ hc.ne').restrict_map
    (volume : Measure ℝ) (Ioc (c * a) (c * (a + L)))
  rw [hpre, Real.map_volume_mul_left hc.ne', Measure.restrict_smul] at hm
  have hscale : ENNReal.ofReal (1 / L) * ENNReal.ofReal |c⁻¹| =
      ENNReal.ofReal (1 / (c * L)) := by
    rw [abs_of_pos (inv_pos.mpr hc), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  simp only [intervalLaw, Measure.map_smul]
  rw [← hm, smul_smul, hscale, mul_add]

theorem sampled_phaseLaw (N₀ n : ℝ) (hN : 0 < N₀) (hn : 0 < n) :
    (intervalLaw (1 / N₀) (1 / N₀)).map
      (fun x : ℝ => ((n * x : ℝ) : UnitAddCircle)) =
      phaseLaw (n / N₀) (n / N₀) := by
  have heq : n / N₀ = n * (1 / N₀) := by ring
  rw [phaseLaw, heq, ← intervalLaw_map_mul (1 / N₀) (1 / N₀) n (by positivity) hn]
  rw [Measure.map_map AddCircle.measurable_mk' (measurable_const_mul n)]
  rfl

theorem lambdaLaw_eq_intervalLaw (N₀ : ℝ) :
    lambdaLaw N₀ = intervalLaw (1 / N₀) (1 / N₀) := by
  have heq : 1 / N₀ + 1 / N₀ = 2 / N₀ := by ring
  simp only [lambdaLaw, intervalLaw, one_div_one_div, heq,
    restrict_Ioc_eq_restrict_Icc]

theorem measurable_representative : Measurable representative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

theorem map_representative_haar :
    (volume : Measure UnitAddCircle).map representative =
      volume.restrict (Ico (0 : ℝ) 1) := by
  have hmk : (volume.restrict (Ico (0 : ℝ) 1)).map
      (fun x : ℝ => (x : UnitAddCircle)) = volume := by
    rw [restrict_Ico_eq_restrict_Ioc]
    simpa using (UnitAddCircle.measurePreserving_mk 0).map_eq
  rw [← hmk, Measure.map_map measurable_representative AddCircle.measurable_mk']
  have heq : (representative ∘ fun x : ℝ => (x : UnitAddCircle)) =ᵐ[
      volume.restrict (Ico (0 : ℝ) 1)] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    change representative (x : UnitAddCircle) = x
    unfold representative
    rw [AddCircle.equivIco_coe_eq (by simpa using hx)]
  rw [Measure.map_congr heq, Measure.map_id]

theorem fractionLaw_eq_map_phaseLaw (N₀ n : ℝ) (hN : 0 < N₀) (hn : 0 < n) :
    fractionLaw N₀ n = (phaseLaw (n / N₀) (n / N₀)).map representative := by
  have hnm : Measurable (fun x : ℝ => ((n * x : ℝ) : UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp (measurable_const_mul n)
  rw [← sampled_phaseLaw N₀ n hN hn, Measure.map_map measurable_representative hnm]
  simp only [fractionLaw, lambdaLaw_eq_intervalLaw, Function.comp_def, representative_coe]

theorem scalar_marginal (N₀ n : ℝ) (hN : 0 < N₀) (hn : 0 < n) :
    Measurable (fractionDensity N₀ n) ∧
      (∀ᵐ x ∂volume.restrict (Ico (0 : ℝ) 1),
        0 ≤ fractionDensity N₀ n x ∧ |fractionDensity N₀ n x - 1| ≤ N₀ / n) ∧
      (volume.restrict (Ico (0 : ℝ) 1)).withDensity
        (fun x => ENNReal.ofReal (fractionDensity N₀ n x)) = fractionLaw N₀ n := by
  obtain ⟨hlow, hupp⟩ := phaseLaw_sandwich (n / N₀) (n / N₀) (div_pos hn hN)
  have hlo := Measure.map_mono hlow measurable_representative
  have hup := Measure.map_mono hupp measurable_representative
  rw [Measure.map_smul, map_representative_haar,
    ← fractionLaw_eq_map_phaseLaw N₀ n hN hn] at hlo hup
  have heq : 1 / (n / N₀) = N₀ / n := by field_simp
  unfold fractionDensity
  simpa only [heq] using
    real_density_spec_of_sandwich (fractionLaw N₀ n)
      (volume.restrict (Ico (0 : ℝ) 1)) (n / N₀) (div_pos hn hN) hlo hup

theorem lambdaLaw_probability (N₀ : ℝ) (hN : 0 < N₀) :
    IsProbabilityMeasure (lambdaLaw N₀) := by
  constructor
  have heq : 2 / N₀ - 1 / N₀ = 1 / N₀ := by ring
  simp only [lambdaLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Icc, heq, smul_eq_mul]
  rw [← ENNReal.ofReal_mul hN.le]
  have heq' : N₀ * (1 / N₀) = 1 := by field_simp
  rw [heq', ENNReal.ofReal_one]

theorem fractionDensity_le_two (N₀ n : ℝ) (hN : 0 < N₀) (hn : N₀ ≤ n) :
    ∀ᵐ x ∂volume.restrict (Ico (0 : ℝ) 1), fractionDensity N₀ n x ≤ 2 := by
  have hn0 : 0 < n := hN.trans_le hn
  filter_upwards [(scalar_marginal N₀ n hN hn0).2.1] with x hx
  have hratio : N₀ / n ≤ 1 := (div_le_one hn0).mpr hn
  have hupper := (abs_le.mp hx.2).2
  linarith

theorem lambdaLaw_eq_cond (N₀ : ℝ) (hN : 0 < N₀) :
    lambdaLaw N₀ = ProbabilityTheory.cond volume (Icc (1 / N₀) (2 / N₀)) := by
  have heq : 2 / N₀ - 1 / N₀ = 1 / N₀ := by ring
  simp only [lambdaLaw, ProbabilityTheory.cond, Real.volume_Icc]
  rw [heq, one_div, ENNReal.ofReal_inv_of_pos hN, inv_inv]

theorem sampled_circle_le_two (N₀ n : ℝ) (hN : 0 < N₀) (hn : N₀ ≤ n) :
    (lambdaLaw N₀).map (fun x : ℝ => ((n * x : ℝ) : UnitAddCircle)) ≤
      (2 : ℝ≥0∞) • (volume : Measure UnitAddCircle) := by
  have hn0 : 0 < n := hN.trans_le hn
  have hL : 0 < n / N₀ := div_pos hn0 hN
  have hone : 1 ≤ n / N₀ := (le_div_iff₀ hN).mpr (by simpa using hn)
  rw [lambdaLaw_eq_intervalLaw, sampled_phaseLaw N₀ n hN hn0]
  refine (phaseLaw_sandwich (n / N₀) (n / N₀) hL).2.trans ?_
  have hc : ENNReal.ofReal (((⌊n / N₀⌋₊ : ℝ) + 1) / (n / N₀)) ≤ (2 : ℝ≥0∞) := by
    have hr : ((⌊n / N₀⌋₊ : ℝ) + 1) / (n / N₀) ≤ 2 := by
      apply (div_le_iff₀ hL).mpr
      linarith [Nat.floor_le hL.le]
    exact_mod_cast ENNReal.ofReal_le_ofReal hr
  intro s
  change ENNReal.ofReal (((⌊n / N₀⌋₊ : ℝ) + 1) / (n / N₀)) * volume s ≤
    (2 : ℝ≥0∞) * volume s
  exact mul_le_mul_left hc _

end Invariant233.UniformIntervalPhase

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarRectangleDiscrepancy
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.ScalarRectangles

local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  norm_num
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem measurable_intervalTest (a b : ℝ) : Measurable (intervalTest a b) :=
  (measurable_const.indicator measurableSet_Icc).comp
    UniformIntervalPhase.measurable_representative

theorem intervalTest_bounds (a b : ℝ) (x : UnitAddCircle) :
    0 ≤ intervalTest a b x ∧ intervalTest a b x ≤ 1 := by
  unfold intervalTest
  by_cases h : UniformIntervalPhase.representative x ∈ Icc a b <;> simp [h]

theorem intervalTest_translation (a b : ℝ) {η : ℝ} (hη : 0 ≤ η)
    (t : UnitAddCircle) (ht : dist t 0 ≤ η) :
    CircleKernelConvolution.translationError (intervalTest a b) t ≤ 6 * η := by
  induction t using QuotientAddGroup.induction_on with
  | H u =>
    have hround : (((round u : ℤ) : ℝ) : UnitAddCircle) = 0 := by
      have hc := AddCircle.coe_zsmul (p := (1 : ℝ)) (n := round u) (x := (1 : ℝ))
      simpa only [zsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using hc
    have hcoe : ((u - round u : ℝ) : UnitAddCircle) = (u : UnitAddCircle) := by
      rw [QuotientAddGroup.mk_sub, hround, sub_zero]
    have hu : |u - round u| ≤ η := by
      simpa only [dist_zero_right, UnitAddCircle.norm_eq] using ht
    have h := IntervalIndicatorTranslation.circle_integral_indicator_translation_le
      (a := a) (b := b) hη hu
    rw [hcoe] at h
    exact h

theorem kernel_tail_le (H : ℕ) (hH : H ≠ 0) {η : ℝ} (hη : 0 < η) :
    (∫ t in {x : UnitAddCircle | dist x 0 ≤ η}ᶜ, Fejer.kernel H t) ≤
      1 / (4 * (H : ℝ) * η ^ 2) := by
  have hB : MeasurableSet {x : UnitAddCircle | dist x 0 ≤ η} :=
    isClosed_le (continuous_id.dist continuous_const) continuous_const |>.measurableSet
  have hk : Integrable (Fejer.kernel H) (volume : Measure UnitAddCircle) :=
    (Fejer.continuous_kernel H).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_indicator hB.compl]
  have hbound : ∀ t : UnitAddCircle,
      {x : UnitAddCircle | dist x 0 ≤ η}ᶜ.indicator (Fejer.kernel H) t ≤
        1 / (4 * (H : ℝ) * η ^ 2) := by
    intro t
    by_cases ht : t ∈ {x : UnitAddCircle | dist x 0 ≤ η}ᶜ
    · rw [Set.indicator_of_mem ht]
      exact Fejer.kernel_le_of_distance_ge H hH hη t (le_of_lt (not_le.mp ht))
    · rw [Set.indicator_of_notMem ht]
      positivity
  have hi := integral_mono (hk.indicator hB.compl) (integrable_const
    (1 / (4 * (H : ℝ) * η ^ 2))) hbound
  simpa using hi

theorem interval_approximation_error (H : ℕ) (hH : H ≠ 0)
    (a b : ℝ) {η : ℝ} (hη : 0 < η) :
    (∫ x : UnitAddCircle, |Fejer.approximation H (intervalTest a b) x -
      intervalTest a b x|) ≤ 6 * η + 1 / (4 * (H : ℝ) * η ^ 2) := by
  apply Fejer.approximation_l1_error_le H hH (measurable_intervalTest a b)
    (fun x => (intervalTest_bounds a b x).1) (fun x => (intervalTest_bounds a b x).2)
    (B := {x : UnitAddCircle | dist x 0 ≤ η})
  · exact (isClosed_le (continuous_id.dist continuous_const) continuous_const).measurableSet
  · positivity
  · exact fun t ht => intervalTest_translation a b hη.le t ht
  · exact kernel_tail_le H hH hη

private theorem integrable_unit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℂ}
    (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ 1) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable 1 (Filter.Eventually.of_forall hb)

theorem rectangle_error_of_character_bounds
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → UnitAddCircle) (hX : Measurable X) (hY : Measurable Y)
    (hmapX : μ.map X ≤ (2 : ℝ≥0∞) • volume)
    (hmapY : μ.map Y ≤ (2 : ℝ≥0∞) • volume)
    (H : ℕ) (hH : H ≠ 0) (a b c d : ℝ) {η ε : ℝ}
    (hη : 0 < η) (hε : 0 ≤ ε)
    (hchar : ∀ i ∈ Fejer.frequencies H, ∀ j ∈ Fejer.frequencies H,
      (i, j) ≠ (0, 0) →
      ‖∫ ω, fourier i (X ω) * fourier j (Y ω) ∂μ‖ ≤ ε) :
    ‖(∫ ω, (intervalTest a b (X ω) : ℂ) * (intervalTest c d (Y ω) : ℂ) ∂μ) -
      (∫ x : UnitAddCircle, intervalTest a b x : ℝ) *
      (∫ x : UnitAddCircle, intervalTest c d x : ℝ)‖ ≤
      4 * (6 * η + 1 / (4 * (H : ℝ) * η ^ 2)) + (2 * (H : ℝ)) ^ 2 * ε := by
  let f := intervalTest a b
  let g := intervalTest c d
  let p := Fejer.approximation H f
  let q := Fejer.approximation H g
  have hf := measurable_intervalTest a b
  have hg := measurable_intervalTest c d
  have hf0 := fun x => (intervalTest_bounds a b x).1
  have hf1 := fun x => (intervalTest_bounds a b x).2
  have hg0 := fun x => (intervalTest_bounds c d x).1
  have hg1 := fun x => (intervalTest_bounds c d x).2
  have hpcont : Continuous p := Fejer.continuous_approximation H hf hf0 hf1
  have hqcont : Continuous q := Fejer.continuous_approximation H hg hg0 hg1
  have hpb : ∀ x, 0 ≤ p x ∧ p x ≤ 1 := Fejer.approximation_bounds H hH hf hf0 hf1
  have hqb : ∀ x, 0 ≤ q x ∧ q x ≤ 1 := Fejer.approximation_bounds H hH hg hg0 hg1
  have hfn : ∀ x, ‖(f x : ℂ)‖ ≤ 1 := fun x => by
    simpa only [f, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hf1 x
  have hgn : ∀ x, ‖(g x : ℂ)‖ ≤ 1 := fun x => by
    simpa only [g, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 x)] using hg1 x
  have hpn : ∀ x, ‖(p x : ℂ)‖ ≤ 1 := fun x => by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpb x).1] using (hpb x).2
  have hqn : ∀ x, ‖(q x : ℂ)‖ ≤ 1 := fun x => by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hqb x).1] using (hqb x).2
  have hfX := (Complex.measurable_ofReal.comp hf).comp hX
  have hgY := (Complex.measurable_ofReal.comp hg).comp hY
  have hpX := (Complex.measurable_ofReal.comp hpcont.measurable).comp hX
  have hqY := (Complex.measurable_ofReal.comp hqcont.measurable).comp hY
  have hfi := integrable_unit μ hfX (fun ω => hfn (X ω))
  have hgi := integrable_unit μ hgY (fun ω => hgn (Y ω))
  have hpi := integrable_unit μ hpX (fun ω => hpn (X ω))
  have hqi := integrable_unit μ hqY (fun ω => hqn (Y ω))
  have hfg := hgi.bdd_mul hfX.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => hfn (X ω))
  have hpq := hqi.bdd_mul hpX.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => hpn (X ω))
  have hfvol := integrable_unit (volume : Measure UnitAddCircle)
    (Complex.measurable_ofReal.comp hf) hfn
  have hgvol := integrable_unit (volume : Measure UnitAddCircle)
    (Complex.measurable_ofReal.comp hg) hgn
  have hpvol := integrable_unit (volume : Measure UnitAddCircle)
    (Complex.measurable_ofReal.comp hpcont.measurable) hpn
  have hqvol := integrable_unit (volume : Measure UnitAddCircle)
    (Complex.measurable_ofReal.comp hqcont.measurable) hqn
  have herrX := FourierSampling.marginal_l1_error_le hX (by norm_num : (0 : ℝ) ≤ 2)
    (by simpa using hmapX) (hfvol.sub hpvol)
  have herrY := FourierSampling.marginal_l1_error_le hY (by norm_num : (0 : ℝ) ≤ 2)
    (by simpa using hmapY) (hgvol.sub hqvol)
  have herrf : (∫ x : UnitAddCircle, ‖(f x : ℂ) - (p x : ℂ)‖) ≤
      6 * η + 1 / (4 * (H : ℝ) * η ^ 2) := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      using interval_approximation_error H hH a b hη
  have herrg : (∫ x : UnitAddCircle, ‖(g x : ℂ) - (q x : ℂ)‖) ≤
      6 * η + 1 / (4 * (H : ℝ) * η ^ 2) := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      using interval_approximation_error H hH c d hη
  have hzero : 0 ∈ Fejer.frequencies H := by
    simp only [Fejer.frequencies, Finset.mem_Ioo]
    have hpos := Nat.pos_of_ne_zero hH
    constructor <;> omega
  have heqp (x : UnitAddCircle) : FourierSampling.polynomial (Fejer.frequencies H)
      (Fejer.approximationCoefficient H f) x = (p x : ℂ) :=
    (Fejer.approximation_eq_polynomial H hf hf0 hf1 x).symm
  have heqq (x : UnitAddCircle) : FourierSampling.polynomial (Fejer.frequencies H)
      (Fejer.approximationCoefficient H g) x = (q x : ℂ) :=
    (Fejer.approximation_eq_polynomial H hg hg0 hg1 x).symm
  have hmain := FourierSampling.test_error_le hX hY
    (Fejer.frequencies H) (Fejer.frequencies H) hzero hzero
    (Fejer.approximationCoefficient H f) (Fejer.approximationCoefficient H g)
    hfg (by simpa only [heqp, heqq, Function.comp_apply] using hpq)
    (by simp only [heqp]; exact hfi.sub hpi)
    (by simp only [heqq]; exact hgi.sub hqi)
    (Filter.Eventually.of_forall fun ω => hgn (Y ω))
    (by simpa only [heqp] using Filter.Eventually.of_forall fun ω => hpn (X ω))
    (fun i _ => Fejer.approximationCoefficient_norm_le_one H hH hf hf0 hf1 i)
    (fun j _ => Fejer.approximationCoefficient_norm_le_one H hH hg hg0 hg1 j)
    hε hchar
  simp only [Fejer.approximationCoefficient_zero H hH, heqp, heqq] at hmain
  have hcard : ((Fejer.frequencies H).card : ℝ) ≤ 2 * (H : ℝ) := by
    exact_mod_cast Fejer.card_frequencies_le H
  have hcard2 : ((Fejer.frequencies H).card : ℝ) * (Fejer.frequencies H).card * ε ≤
      (2 * (H : ℝ)) ^ 2 * ε := by
    apply mul_le_mul_of_nonneg_right _ hε
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fejer.frequencies H).card]
  dsimp only [Function.comp_apply, f, g] at herrX herrY herrf herrg hmain ⊢
  exact hmain.trans (by nlinarith only [herrX, herrY, herrf, herrg, hcard2])

theorem sampled_character_pair (i j : ℤ) (n n' t : ℝ) :
    fourier i ((n * t : ℝ) : UnitAddCircle) *
      fourier j ((n' * t : ℝ) : UnitAddCircle) =
      Complex.exp ((((2 * Real.pi * ((i : ℝ) * n + (j : ℝ) * n')) * t : ℝ) : ℂ) *
        Complex.I) := by
  rw [fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem sampling_rectangle_error
    {N₀ N m n n' : ℝ} (hN₀ : 0 < N₀) (hN : N₀ ≤ N) (hm : 0 < m)
    (hn : N₀ ≤ n) (hn' : N₀ ≤ n') (H : ℕ) (hH : H ≠ 0)
    (hsep : ∀ i j : ℤ, |i| ≤ (H : ℤ) → |j| ≤ (H : ℤ) →
      (i, j) ≠ (0, 0) → N * m ^ 1000 < |(i : ℝ) * n + (j : ℝ) * n'|)
    (a b c d : ℝ) {η : ℝ} (hη : 0 < η) :
    ‖(∫ t, (intervalTest a b ((n * t : ℝ) : UnitAddCircle) : ℂ) *
        (intervalTest c d ((n' * t : ℝ) : UnitAddCircle) : ℂ)
        ∂UniformIntervalPhase.lambdaLaw N₀) -
      (∫ x : UnitAddCircle, intervalTest a b x : ℝ) *
      (∫ x : UnitAddCircle, intervalTest c d x : ℝ)‖ ≤
      4 * (6 * η + 1 / (4 * (H : ℝ) * η ^ 2)) +
        (2 * (H : ℝ)) ^ 2 / m ^ 1000 := by
  let := UniformIntervalPhase.lambdaLaw_probability N₀ hN₀
  have hX : Measurable (fun t : ℝ => ((n * t : ℝ) : UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp (measurable_const_mul n)
  have hY : Measurable (fun t : ℝ => ((n' * t : ℝ) : UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp (measurable_const_mul n')
  have hchar : ∀ i ∈ Fejer.frequencies H, ∀ j ∈ Fejer.frequencies H,
      (i, j) ≠ (0, 0) →
      ‖∫ t, fourier i ((n * t : ℝ) : UnitAddCircle) *
        fourier j ((n' * t : ℝ) : UnitAddCircle)
        ∂UniformIntervalPhase.lambdaLaw N₀‖ ≤ 1 / m ^ 1000 := by
    intro i hi j hj hij
    have hi' : |i| ≤ (H : ℤ) := by
      simp only [Fejer.frequencies, Finset.mem_Ioo] at hi
      exact abs_le.mpr ⟨hi.1.le, hi.2.le⟩
    have hj' : |j| ≤ (H : ℤ) := by
      simp only [Fejer.frequencies, Finset.mem_Ioo] at hj
      exact abs_le.mpr ⟨hj.1.le, hj.2.le⟩
    simp_rw [sampled_character_pair]
    rw [UniformIntervalPhase.lambdaLaw_eq_cond N₀ hN₀]
    apply (UniformIntervalFourier.norm_sampling_interval_character_le_of_separation
      hN₀ hN hm (hsep i j hi' hj' hij)).trans
    apply one_div_le_one_div_of_le (pow_pos hm _)
    nlinarith [Real.pi_gt_three, pow_pos hm 1000]
  have h := rectangle_error_of_character_bounds (UniformIntervalPhase.lambdaLaw N₀)
    _ _ hX hY (UniformIntervalPhase.sampled_circle_le_two N₀ n hN₀ hn)
    (UniformIntervalPhase.sampled_circle_le_two N₀ n' hN₀ hn')
    H hH a b c d hη (by positivity : 0 ≤ 1 / m ^ 1000) hchar
  simpa only [mul_one_div] using h

theorem integral_intervalTest (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ x : UnitAddCircle, intervalTest a b x) = b - a := by
  have hf : Measurable ((Icc a b).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator measurableSet_Icc
  have h := integral_map (μ := (volume : Measure UnitAddCircle))
    UniformIntervalPhase.measurable_representative.aemeasurable
    hf.aestronglyMeasurable
  rw [UniformIntervalPhase.map_representative_haar] at h
  change (∫ x : UnitAddCircle, (Icc a b).indicator (fun _ => (1 : ℝ))
    (UniformIntervalPhase.representative x)) = b - a
  rw [← h, integral_indicator_const 1 measurableSet_Icc,
    measureReal_restrict_apply measurableSet_Icc, smul_eq_mul, mul_one]
  have heq : (Icc a b ∩ Ico (0 : ℝ) 1 : Set ℝ) =ᵐ[volume]
      (Icc a b ∩ Icc (0 : ℝ) 1 : Set ℝ) :=
    Filter.EventuallyEq.inter Filter.EventuallyEq.rfl Ico_ae_eq_Icc
  rw [measureReal_congr heq, Set.inter_eq_left.mpr (Icc_subset_Icc ha hb)]
  exact Real.volume_real_Icc_of_le hab

theorem integral_sample_interval_product (N₀ n n' a b c d : ℝ) :
    (∫ t, (intervalTest a b ((n * t : ℝ) : UnitAddCircle) : ℂ) *
      (intervalTest c d ((n' * t : ℝ) : UnitAddCircle) : ℂ)
      ∂UniformIntervalPhase.lambdaLaw N₀) =
      ((UniformIntervalPhase.lambdaLaw N₀).real
        {t : ℝ | Int.fract (n * t) ∈ Icc a b ∧ Int.fract (n' * t) ∈ Icc c d} : ℂ) := by
  have hs : MeasurableSet
      {t : ℝ | Int.fract (n * t) ∈ Icc a b ∧ Int.fract (n' * t) ∈ Icc c d} :=
    (measurableSet_Icc.preimage (measurable_fract.comp (measurable_const_mul n))).inter
      (measurableSet_Icc.preimage (measurable_fract.comp (measurable_const_mul n')))
  have heq : (fun t => (intervalTest a b ((n * t : ℝ) : UnitAddCircle) : ℂ) *
      (intervalTest c d ((n' * t : ℝ) : UnitAddCircle) : ℂ)) =
      {t : ℝ | Int.fract (n * t) ∈ Icc a b ∧ Int.fract (n' * t) ∈ Icc c d}.indicator
        (fun _ => (1 : ℂ)) := by
    funext t
    simp only [intervalTest, UniformIntervalPhase.representative_coe, Set.indicator_apply,
      Set.mem_ofPred_eq]
    by_cases hi : Int.fract (n * t) ∈ Icc a b <;>
      by_cases hj : Int.fract (n' * t) ∈ Icc c d <;> simp [hi, hj]
  rw [heq, integral_indicator_const 1 hs]
  simp

theorem sampling_rectangle_probability_error
    {N₀ N m n n' : ℝ} (hN₀ : 0 < N₀) (hN : N₀ ≤ N) (hm : 0 < m)
    (hn : N₀ ≤ n) (hn' : N₀ ≤ n') (H : ℕ) (hH : H ≠ 0)
    (hsep : ∀ i j : ℤ, |i| ≤ (H : ℤ) → |j| ≤ (H : ℤ) →
      (i, j) ≠ (0, 0) → N * m ^ 1000 < |(i : ℝ) * n + (j : ℝ) * n'|)
    (a b c d : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) {η : ℝ} (hη : 0 < η) :
    |(UniformIntervalPhase.lambdaLaw N₀).real
        {t : ℝ | Int.fract (n * t) ∈ Icc a b ∧ Int.fract (n' * t) ∈ Icc c d} -
      (b - a) * (d - c)| ≤
      4 * (6 * η + 1 / (4 * (H : ℝ) * η ^ 2)) +
        (2 * (H : ℝ)) ^ 2 / m ^ 1000 := by
  have h := sampling_rectangle_error hN₀ hN hm hn hn' H hH hsep a b c d hη
  rw [integral_sample_interval_product, integral_intervalTest a b ha hab hb,
    integral_intervalTest c d hc hcd hd] at h
  simpa only [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] using h

theorem horizon_ge_twice_square {m : ℝ} (hm : 200 ≤ m) :
    2 * m ^ 2 ≤ m ^ ((7 / 10 : ℝ) * m) := by
  have hm1 : 1 ≤ m := by linarith
  calc
    2 * m ^ 2 ≤ m ^ 3 := by nlinarith [sq_nonneg m]
    _ = m ^ (3 : ℝ) := (Real.rpow_natCast m 3).symm
    _ ≤ m ^ ((7 / 10 : ℝ) * m) :=
      Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)

theorem numerical_rectangle_error {m : ℝ} (hm : 1 ≤ m) :
    4 * (6 * (1 / m ^ 80) + 1 / (4 * m ^ 300 * (1 / m ^ 80) ^ 2)) +
      (2 * m ^ 300) ^ 2 / m ^ 1000 ≤ 29 / m ^ 80 := by
  have hm0 : 0 < m := by linarith
  have heq :
      4 * (6 * (1 / m ^ 80) + 1 / (4 * m ^ 300 * (1 / m ^ 80) ^ 2)) +
        (2 * m ^ 300) ^ 2 / m ^ 1000 =
          24 / m ^ 80 + 1 / m ^ 140 + 4 / m ^ 400 := by
    field_simp
    ring
  rw [heq]
  have h140 : 1 / m ^ 140 ≤ 1 / m ^ 80 :=
    one_div_le_one_div_of_le (pow_pos hm0 _) (pow_le_pow_right₀ hm (by norm_num))
  have h400 : 4 / m ^ 400 ≤ 4 / m ^ 80 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hm0 _)
      (pow_le_pow_right₀ hm (by norm_num))
  calc
    _ ≤ 24 / m ^ 80 + 1 / m ^ 80 + 4 / m ^ 80 :=
      add_le_add (add_le_add le_rfl h140) h400
    _ = 29 / m ^ 80 := by ring

theorem scalar_rectangles (m : ℕ) (hm : 200 ≤ m)
    (N₀ N : ℝ) (hN₀ : 0 < N₀) (hN : N₀ ≤ N) (hNm : N ≤ (m : ℝ) ^ 2)
    (n n' : ℕ)
    (hn : (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n)
    (hn' : (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n')
    (hsep : ∀ i j : ℤ, |i| ≤ (m ^ 300 : ℕ) → |j| ≤ (m ^ 300 : ℕ) →
      (i, j) ≠ (0, 0) →
      N * (m : ℝ) ^ 1000 < |(i : ℝ) * n + (j : ℝ) * n'|)
    (a b c d : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    |(UniformIntervalPhase.lambdaLaw N₀).real
        {t : ℝ | Int.fract ((n : ℝ) * t) ∈ Icc a b ∧
          Int.fract ((n' : ℝ) * t) ∈ Icc c d} - (b - a) * (d - c)| ≤
      29 / (m : ℝ) ^ 80 := by
  have hmr : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hmn : m ≠ 0 := by omega
  have hhor := horizon_ge_twice_square hmr
  have hnN : N₀ ≤ (n : ℝ) := by linarith
  have hn'N : N₀ ≤ (n' : ℝ) := by linarith
  have h := sampling_rectangle_probability_error hN₀ hN hm0 hnN hn'N
    (m ^ 300) (pow_ne_zero _ hmn) hsep a b c d ha hab hb hc hcd hd
    (η := 1 / (m : ℝ) ^ 80) (by positivity)
  simp only [Nat.cast_pow] at h
  exact h.trans (numerical_rectangle_error (by linarith))

theorem sampled_fraction_absolutelyContinuous (N₀ n : ℝ) (hN₀ : 0 < N₀) (hn : 0 < n) :
    (UniformIntervalPhase.lambdaLaw N₀).map (fun t => Int.fract (n * t)) ≪
      volume.restrict (Icc (0 : ℝ) 1) := by
  have hac : UniformIntervalPhase.fractionLaw N₀ n ≪ volume.restrict (Ico (0 : ℝ) 1) := by
    rw [← (UniformIntervalPhase.scalar_marginal N₀ n hN₀ hn).2.2]
    exact withDensity_absolutelyContinuous _ _
  simpa only [UniformIntervalPhase.fractionLaw, restrict_Ico_eq_restrict_Icc] using hac

theorem scalar_tail_rectangles_integral (m : ℕ) (hm : 200 ≤ m)
    (N₀ N : ℝ) (hN₀ : 0 < N₀) (hN : N₀ ≤ N) (hNm : N ≤ (m : ℝ) ^ 2)
    (n n' : ℕ)
    (hn : (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n)
    (hn' : (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n')
    (hsep : ∀ i j : ℤ, |i| ≤ (m ^ 300 : ℕ) → |j| ≤ (m ^ 300 : ℕ) →
      (i, j) ≠ (0, 0) →
      N * (m : ℝ) ^ 1000 < |(i : ℝ) * n + (j : ℝ) * n'|)
    (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    ‖(∫ t, (Icc a 1).indicator (fun _ => (1 : ℂ)) (Int.fract ((n : ℝ) * t)) *
        (Icc b 1).indicator (fun _ => (1 : ℂ)) (Int.fract ((n' : ℝ) * t))
        ∂UniformIntervalPhase.lambdaLaw N₀) - ((1 - a) * (1 - b) : ℝ)‖ ≤
      29 / (m : ℝ) ^ 80 := by
  have h := scalar_rectangles m hm N₀ N hN₀ hN hNm n n' hn hn' hsep
    a 1 b 1 ha.1 ha.2 le_rfl hb.1 hb.2 le_rfl
  have heq (u v z : ℝ) :
      (intervalTest u v (z : UnitAddCircle) : ℂ) =
        (Icc u v).indicator (fun _ => (1 : ℂ)) (Int.fract z) := by
    simp only [intervalTest, UniformIntervalPhase.representative_coe, Set.indicator_apply]
    split_ifs <;> simp
  have hid := integral_sample_interval_product N₀ n n' a 1 b 1
  simp_rw [heq] at hid
  rw [hid, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact h

end Invariant233.ScalarRectangles

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarBVDiscrepancy
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.ScalarRectangles

theorem scalar_bv_discrepancy (m : ℕ) (hm : 200 ≤ m)
    (N₀ N : ℝ) (hN₀ : 0 < N₀) (hN : N₀ ≤ N) (hNm : N ≤ (m : ℝ) ^ 2)
    (n n' : ℕ)
    (hn : (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n)
    (hn' : (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n')
    (hsep : ∀ i j : ℤ, |i| ≤ (m ^ 300 : ℕ) → |j| ≤ (m ^ 300 : ℕ) →
      (i, j) ≠ (0, 0) →
      N * (m : ℝ) ^ 1000 < |(i : ℝ) * n + (j : ℝ) * n'|)
    (f g : ℝ → ℂ)
    (hf : BoundedVariationOn f (Icc (0 : ℝ) 1))
    (hg : BoundedVariationOn g (Icc (0 : ℝ) 1)) :
    ‖(∫ t, f (Int.fract ((n : ℝ) * t)) * g (Int.fract ((n' : ℝ) * t))
        ∂UniformIntervalPhase.lambdaLaw N₀) -
      (∫ x in (0 : ℝ)..1, f x) * (∫ y in (0 : ℝ)..1, g y)‖ ≤
      (29 / (m : ℝ) ^ 80) *
        (sSup ((fun x => ‖f x‖) '' Icc (0 : ℝ) 1) +
          (eVariationOn f (Icc (0 : ℝ) 1)).toReal) *
        (sSup ((fun x => ‖g x‖) '' Icc (0 : ℝ) 1) +
          (eVariationOn g (Icc (0 : ℝ) 1)).toReal) := by
  let := UniformIntervalPhase.lambdaLaw_probability N₀ hN₀
  have hmr : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : 0 < (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 :=
    div_pos (Real.rpow_pos_of_pos (by linarith) _) (by norm_num)
  have hX : Measurable (fun t => Int.fract ((n : ℝ) * t)) :=
    measurable_fract.comp (measurable_const_mul (n : ℝ))
  have hY : Measurable (fun t => Int.fract ((n' : ℝ) * t)) :=
    measurable_fract.comp (measurable_const_mul (n' : ℝ))
  have hrect : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      ‖(∫ t, BVDiscrepancy.tail a (Int.fract ((n : ℝ) * t)) *
        BVDiscrepancy.tail b (Int.fract ((n' : ℝ) * t))
        ∂UniformIntervalPhase.lambdaLaw N₀) -
        ((1 - a : ℝ) : ℂ) * ((1 - b : ℝ) : ℂ)‖ ≤ 29 / (m : ℝ) ^ 80 := by
    intro a ha b hb
    simpa only [BVDiscrepancy.tail, Complex.ofReal_mul] using
      scalar_tail_rectangles_integral m hm N₀ N hN₀ hN hNm n n' hn hn' hsep a b ha hb
  have h := BVDiscrepancy.boundedVariation_discrepancy
    (UniformIntervalPhase.lambdaLaw N₀) hX hY
    (sampled_fraction_absolutelyContinuous N₀ n hN₀ (hmp.trans_le hn))
    (sampled_fraction_absolutelyContinuous N₀ n' hN₀ (hmp.trans_le hn'))
    (by positivity : (0 : ℝ) ≤ 29 / (m : ℝ) ^ 80) hrect f g hf hg
  simpa only [BVDiscrepancy.unitMeasure, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using h

end Invariant233.ScalarRectangles

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarEndpointKernelBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem manuscript_width_le_half {m : ℕ} (hm : 200 ≤ m) :
    (m : ℝ) ^ (-(3 / 5 : ℝ)) ≤ 1 / 2 := by
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast (by omega : 4 ≤ m)
  calc
    _ ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ ≤ (4 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hm4 (by norm_num)
    _ = _ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), ← Real.sqrt_eq_rpow]
      norm_num

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarKernelMomentNumerics
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem kernel_average_square_remainder_le {m : ℕ} (hm : 200 ≤ m) :
    ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 ≤
      4 * (m : ℝ)^(-(6 / 5 : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hhalf := manuscript_width_le_half hm
  have hwidth : 0 < (m : ℝ)^(-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos hm0 _
  have hden : (1 / 4 : ℝ) ≤ (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by nlinarith
  have hsquare : ((m : ℝ)^(-(3 / 5 : ℝ)))^2 = (m : ℝ)^(-(6 / 5 : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hm0.le]
    congr 1
    norm_num
  calc
    _ ≤ ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 / 4) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hden
    _ = _ := by rw [hsquare]; ring

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductScaleConsequences
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Invariant233.ProductScaleLaws

variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem N_le_square (n : ℕ) : p.N n ≤ (p.m n : ℝ) ^ 2 := by
  have h : (p.K n : ℝ) ≤ p.m n := by exact_mod_cast hp.m_ge_K n
  dsimp [ProductScaleData.N]
  nlinarith [show (0 : ℝ) ≤ p.m n by positivity]

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingEstimates
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Invariant233.ProductSampling

theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (ha : ∀ i ∈ s, |a i| ≤ B) (hb : ∀ i ∈ s, |b i| ≤ B)
    (hab : ∀ i ∈ s, |a i - b i| ≤ ε) :
    |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| ≤
      (s.card : ℝ) * ε * B ^ (s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hai : |a i| ≤ B := ha i (Finset.mem_insert_self _ _)
      have habi : |a i - b i| ≤ ε := hab i (Finset.mem_insert_self _ _)
      have has : ∀ j ∈ s, |a j| ≤ B := fun j hj => ha j (Finset.mem_insert_of_mem hj)
      have hbs : ∀ j ∈ s, |b j| ≤ B := fun j hj => hb j (Finset.mem_insert_of_mem hj)
      have habs : ∀ j ∈ s, |a j - b j| ≤ ε :=
        fun j hj => hab j (Finset.mem_insert_of_mem hj)
      rcases s.eq_empty_or_nonempty with rfl | hs
      · simpa using habi
      have hprod : |∏ j ∈ s, b j| ≤ B ^ s.card := by
        rw [Finset.abs_prod]
        calc
          ∏ j ∈ s, |b j| ≤ ∏ _j ∈ s, B :=
            Finset.prod_le_prod (fun index _ => abs_nonneg (b index)) hbs
          _ = B ^ s.card := by simp
      have hpow : B * B ^ (s.card - 1) = B ^ s.card := by
        rw [← pow_succ', Nat.sub_add_cancel (Finset.card_pos.mpr hs)]
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
      calc
        |a i * (∏ j ∈ s, a j) - b i * ∏ j ∈ s, b j| =
            |a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) +
              (a i - b i) * ∏ j ∈ s, b j| := by congr 1; ring
        _ ≤ |a i| * |(∏ j ∈ s, a j) - ∏ j ∈ s, b j| +
              |a i - b i| * |∏ j ∈ s, b j| := by
          simpa only [abs_mul] using abs_add_le
            (a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j))
            ((a i - b i) * ∏ j ∈ s, b j)
        _ ≤ B * ((s.card : ℝ) * ε * B ^ (s.card - 1)) + ε * B ^ s.card := by
          exact add_le_add
            (mul_le_mul hai (ih has hbs habs) (abs_nonneg _) hB)
            (mul_le_mul habi hprod (abs_nonneg _) hε)
        _ = (s.card : ℝ) * ε * (B * B ^ (s.card - 1)) + ε * B ^ s.card := by ring
        _ = ((s.card + 1 : ℕ) : ℝ) * ε * B ^ ((s.card + 1) - 1) := by
          rw [hpow, Nat.add_sub_cancel]
          push_cast
          ring

theorem abs_prod_add_error_sub_prod_le {ι : Type*} (s : Finset ι)
    (A e : ι → ℝ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hA : ∀ i ∈ s, 0 ≤ A i ∧ A i ≤ B)
    (he : ∀ i ∈ s, |e i| ≤ ε) :
    |(∏ i ∈ s, (A i + e i)) - ∏ i ∈ s, A i| ≤
      (s.card : ℝ) * ε * (B + ε) ^ (s.card - 1) := by
  apply abs_prod_sub_prod_le s (fun i => A i + e i) A (add_nonneg hB hε) hε
  · intro i hi
    calc
      |A i + e i| ≤ |A i| + |e i| := abs_add_le _ _
      _ ≤ B + ε := add_le_add (by simpa [abs_of_nonneg (hA i hi).1] using (hA i hi).2)
        (he i hi)
  · intro i hi
    rw [abs_of_nonneg (hA i hi).1]
    exact le_trans (hA i hi).2 (le_add_of_nonneg_right hε)
  · intro i hi
    simpa using he i hi

end Invariant233.ProductSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingMomentBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace InvariantRotation.SamplingMomentBounds

theorem product_perturbation_bound {ι : Type*} (s : Finset ι) (A e : ι → ℝ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hAB : ∀ i ∈ s, A i ≤ B)
    (he : ∀ i ∈ s, |e i| ≤ ε) :
    |(∏ i ∈ s, (A i + e i)) - ∏ i ∈ s, A i| ≤
      (s.card : ℝ) * ε * (B + ε) ^ (s.card - 1) := by
  exact Invariant233.ProductSampling.abs_prod_add_error_sub_prod_le s A e hB hε
    (fun i hi => ⟨hA i hi, hAB i hi⟩) he

theorem averaged_moment_bound {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (Q : ι → ι → ℝ) (C : ι → ℝ) {A D ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hdiag : ∀ i ∈ s, Q i i ≤ D)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Q i j ≤ A + ε)
    (hcross : ∀ i ∈ s, A - ε ≤ C i) :
    ((s.card : ℝ)⁻¹) ^ 2 * (∑ i ∈ s, ∑ j ∈ s, Q i j) -
        2 * (s.card : ℝ)⁻¹ * (∑ i ∈ s, C i) + A ≤
      D / (s.card : ℝ) + 3 * ε := by
  classical
  let P : ℝ := s.card
  have hn : 0 < s.card := Finset.card_pos.mpr hs
  have hP : 0 < P := by
    dsimp [P]
    exact_mod_cast hn
  have hP0 : P ≠ 0 := ne_of_gt hP
  have hrow (i : ι) (hi : i ∈ s) :
      (∑ j ∈ s, Q i j) ≤ D + (P - 1) * (A + ε) := by
    calc
      (∑ j ∈ s, Q i j) = Q i i + ∑ j ∈ s.erase i, Q i j := by
        rw [← Finset.sum_erase_add s (Q i) hi, add_comm]
      _ ≤ D + ∑ _j ∈ s.erase i, (A + ε) := by
        apply add_le_add (hdiag i hi)
        apply Finset.sum_le_sum
        intro j hj
        exact hoff i hi j (Finset.mem_of_mem_erase hj)
          (Ne.symm (Finset.ne_of_mem_erase hj))
      _ = D + (P - 1) * (A + ε) := by
        simp [P, Finset.card_erase_of_mem hi, Nat.cast_sub (Nat.succ_le_of_lt hn)]
        ring
  have hsum : (∑ i ∈ s, ∑ j ∈ s, Q i j) ≤
      P * D + P * (P - 1) * (A + ε) := by
    calc
      (∑ i ∈ s, ∑ j ∈ s, Q i j) ≤ ∑ _i ∈ s, (D + (P - 1) * (A + ε)) :=
        Finset.sum_le_sum hrow
      _ = P * D + P * (P - 1) * (A + ε) := by simp [P] <;> ring
  have hc : P * (A - ε) ≤ ∑ i ∈ s, C i := by
    calc
      P * (A - ε) = ∑ _i ∈ s, (A - ε) := by simp [P] <;> ring
      _ ≤ ∑ i ∈ s, C i := Finset.sum_le_sum hcross
  change (P⁻¹) ^ 2 * (∑ i ∈ s, ∑ j ∈ s, Q i j) -
    2 * P⁻¹ * (∑ i ∈ s, C i) + A ≤ D / P + 3 * ε
  calc
    _ ≤ (P⁻¹) ^ 2 * (P * D + P * (P - 1) * (A + ε)) -
        2 * P⁻¹ * (P * (A - ε)) + A := by
      have h1 := mul_le_mul_of_nonneg_left hsum (sq_nonneg (P⁻¹))
      have h2 := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * P⁻¹ by positivity)
      linarith
    _ = D / P + 3 * ε - (A + ε) / P := by field_simp <;> ring
    _ ≤ D / P + 3 * ε := sub_le_self _ (div_nonneg (add_nonneg hA hε) hP.le)

theorem norm_average_sub_sq_le {ι E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : Finset ι) (hs : s.Nonempty)
    (v : ι → E) (z : E) {D ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ i ∈ s, ‖v i‖ ^ 2 ≤ D)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) ≤ ‖z‖ ^ 2 + ε)
    (hcross : ∀ i ∈ s, ‖z‖ ^ 2 - ε ≤ inner ℝ (v i) z) :
    ‖(s.card : ℝ)⁻¹ • (∑ i ∈ s, v i) - z‖ ^ 2 ≤
      D / (s.card : ℝ) + 3 * ε := by
  have h := averaged_moment_bound s hs (fun i j => inner ℝ (v i) (v j))
    (fun i => inner ℝ (v i) z) (sq_nonneg ‖z‖) hε
    (by simpa only [real_inner_self_eq_norm_sq] using hdiag) hoff hcross
  have hn : ‖(s.card : ℝ)⁻¹ • (∑ i ∈ s, v i)‖ ^ 2 =
      ((s.card : ℝ)⁻¹) ^ 2 * (∑ i ∈ s, ∑ j ∈ s, inner ℝ (v i) (v j)) := by
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [real_inner_smul_left, real_inner_smul_right, sum_inner, inner_sum]
    ring
  rw [norm_sub_sq_real, hn, real_inner_smul_left, sum_inner]
  nlinarith [h]

open MeasureTheory

theorem l2_norm_sq_eq_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp [pow_two]

theorem l2_coe_finset_sum {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (s : Finset ι) (v : ι → Lp ℝ 2 μ) :
    (fun x => (∑ i ∈ s, v i) x) =ᵐ[μ] (fun x => ∑ i ∈ s, v i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    simpa using hx
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (v a) (∑ i ∈ s, v i), ih] with x hx hx'
    simpa only [Pi.add_apply, hx'] using hx

theorem integral_average_sub_sq_le {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (s : Finset ι) (hs : s.Nonempty)
    (v : ι → Lp ℝ 2 μ) (z : Lp ℝ 2 μ) {D ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ i ∈ s, (∫ x, (v i x) ^ 2 ∂μ) ≤ D)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (∫ x, v i x * v j x ∂μ) ≤ (∫ x, (z x) ^ 2 ∂μ) + ε)
    (hcross : ∀ i ∈ s, (∫ x, (z x) ^ 2 ∂μ) - ε ≤ ∫ x, v i x * z x ∂μ) :
    (∫ x, ((s.card : ℝ)⁻¹ * (∑ i ∈ s, v i x) - z x) ^ 2 ∂μ) ≤
      D / (s.card : ℝ) + 3 * ε := by
  have h := norm_average_sub_sq_le s hs v z hε
    (by simpa only [l2_norm_sq_eq_integral_sq] using hdiag)
    (by simpa only [L2.inner_def, RCLike.inner_apply, starRingEnd_apply,
      star_trivial, mul_comm, l2_norm_sq_eq_integral_sq] using hoff)
    (by simpa only [L2.inner_def, RCLike.inner_apply, starRingEnd_apply,
      star_trivial, mul_comm, l2_norm_sq_eq_integral_sq] using hcross)
  rw [l2_norm_sq_eq_integral_sq] at h
  have heq : (fun x => ((s.card : ℝ)⁻¹ • (∑ i ∈ s, v i) - z) x ^ 2) =ᵐ[μ]
      (fun x => ((s.card : ℝ)⁻¹ * (∑ i ∈ s, v i x) - z x) ^ 2) := by
    filter_upwards [Lp.coeFn_sub ((s.card : ℝ)⁻¹ • (∑ i ∈ s, v i)) z,
      Lp.coeFn_smul (s.card : ℝ)⁻¹ (∑ i ∈ s, v i), l2_coe_finset_sum s v]
      with x hsub hsmul hsum
    simp only [Pi.sub_apply] at hsub
    simp only [Pi.smul_apply, smul_eq_mul] at hsmul
    rw [hsub, hsmul, hsum]
  rwa [integral_congr_ae heq] at h

theorem integral_average_sub_sq_le_of_memLp {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (s : Finset ι) (hs : s.Nonempty)
    (v : ι → Ω → ℝ) (z : Ω → ℝ)
    (hv : ∀ i, MemLp (v i) 2 μ) (hz : MemLp z 2 μ)
    {D ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ i ∈ s, (∫ x, (v i x) ^ 2 ∂μ) ≤ D)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (∫ x, v i x * v j x ∂μ) ≤ (∫ x, (z x) ^ 2 ∂μ) + ε)
    (hcross : ∀ i ∈ s, (∫ x, (z x) ^ 2 ∂μ) - ε ≤ ∫ x, v i x * z x ∂μ) :
    (∫ x, ((s.card : ℝ)⁻¹ * (∑ i ∈ s, v i x) - z x) ^ 2 ∂μ) ≤
      D / (s.card : ℝ) + 3 * ε := by
  let V : ι → Lp ℝ 2 μ := fun i => (hv i).toLp (v i)
  let Z : Lp ℝ 2 μ := hz.toLp z
  have hV (i : ι) : (fun x => V i x) =ᵐ[μ] v i := (hv i).coeFn_toLp
  have hZ : (fun x => Z x) =ᵐ[μ] z := hz.coeFn_toLp
  have hVsq (i : ι) : (∫ x, (V i x) ^ 2 ∂μ) = ∫ x, (v i x) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hV i] with x hx using congrArg (fun t : ℝ => t ^ 2) hx
  have hZsq : (∫ x, (Z x) ^ 2 ∂μ) = ∫ x, (z x) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hZ] with x hx using congrArg (fun t : ℝ => t ^ 2) hx
  have hVV (i j : ι) : (∫ x, V i x * V j x ∂μ) = ∫ x, v i x * v j x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hV i, hV j] with x hi hj
    rw [hi, hj]
  have hVZ (i : ι) : (∫ x, V i x * Z x ∂μ) = ∫ x, v i x * z x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hV i, hZ] with x hi hz'
    rw [hi, hz']
  have h := integral_average_sub_sq_le s hs V Z hε
    (by simpa only [hVsq] using hdiag)
    (by simpa only [hVV, hZsq] using hoff)
    (by simpa only [hVZ, hZsq] using hcross)
  have hall : ∀ᵐ x ∂μ, ∀ i ∈ s, V i x = v i x :=
    (Finset.eventually_all s).2 (fun i _ => hV i)
  have heq : (fun x => ((s.card : ℝ)⁻¹ * (∑ i ∈ s, V i x) - Z x) ^ 2) =ᵐ[μ]
      (fun x => ((s.card : ℝ)⁻¹ * (∑ i ∈ s, v i x) - z x) ^ 2) := by
    filter_upwards [hall, hZ] with x hx hz'
    rw [Finset.sum_congr rfl hx, hz']
  rwa [integral_congr_ae heq] at h

end InvariantRotation.SamplingMomentBounds

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingMoments
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace InvariantRotation.SamplingMomentBounds

theorem memLp_coordinate_prod {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] (f : (i : κ) → Ω i → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) :
    MemLp (fun x => ∏ i, f i (x i)) 2 (Measure.pi μ) := by
  have hm : AEStronglyMeasurable (fun x => ∏ i, f i (x i)) (Measure.pi μ) := by
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (hf i).aestronglyMeasurable.comp_measurePreserving (measurePreserving_eval μ i)
  apply (memLp_two_iff_integrable_sq hm).2
  simpa only [Finset.prod_pow] using
    Integrable.fintype_prod_dep (fun i => (hf i).integrable_sq)

theorem integral_coordinate_prod_mul {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, SigmaFinite (μ i)] (f g : (i : κ) → Ω i → ℝ) :
    (∫ x, (∏ i, f i (x i)) * (∏ i, g i (x i)) ∂Measure.pi μ) =
      ∏ i, ∫ x, f i x * g i x ∂μ i := by
  simp_rw [← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (fun i x => f i x * g i x)

theorem integral_coordinate_prod_sq {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : κ) → Ω i → ℝ) :
    (∫ x, (∏ i, f i (x i)) ^ 2 ∂Measure.pi μ) =
      ∏ i, ∫ x, (f i x) ^ 2 ∂μ i := by
  simpa only [pow_two] using integral_coordinate_prod_mul f f (μ := μ)

theorem coordinate_product_pair_error_le
    {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, SigmaFinite (μ i)] (f g z : (i : κ) → Ω i → ℝ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hbase : ∀ i, (∫ x, (z i x) ^ 2 ∂μ i) ≤ B)
    (herror : ∀ i, |(∫ x, f i x * g i x ∂μ i) - (∫ x, (z i x) ^ 2 ∂μ i)| ≤ ε) :
    |(∫ x, (∏ i, f i (x i)) * (∏ i, g i (x i)) ∂Measure.pi μ) -
        (∫ x, (∏ i, z i (x i)) ^ 2 ∂Measure.pi μ)| ≤
      (Fintype.card κ : ℝ) * ε * (B + ε) ^ (Fintype.card κ - 1) := by
  rw [integral_coordinate_prod_mul, integral_coordinate_prod_sq]
  let A : κ → ℝ := fun i => ∫ x, (z i x) ^ 2 ∂μ i
  have he := product_perturbation_bound (Finset.univ : Finset κ) A
    (fun i => (∫ x, f i x * g i x ∂μ i) - A i) hB hε
    (fun i _ => integral_nonneg (fun _ => sq_nonneg _)) (fun i _ => hbase i)
    (fun i _ => herror i)
  simpa only [add_sub_cancel, Finset.card_univ] using he

theorem coordinate_product_sq_le_pow
    {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : κ) → Ω i → ℝ)
    {D : ℝ} (h : ∀ i, (∫ x, (f i x) ^ 2 ∂μ i) ≤ D) :
    (∫ x, (∏ i, f i (x i)) ^ 2 ∂Measure.pi μ) ≤ D ^ Fintype.card κ := by
  rw [integral_coordinate_prod_sq]
  calc
    (∏ i, ∫ x, (f i x) ^ 2 ∂μ i) ≤ ∏ _i : κ, D :=
      Finset.prod_le_prod (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
        (fun index _ => h index)
    _ = D ^ Fintype.card κ := by simp

theorem integral_average_coordinate_products_sub_sq_le
    {κ ι : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset ι) (hs : s.Nonempty)
    (v : ι → (i : κ) → Ω i → ℝ) (z : (i : κ) → Ω i → ℝ)
    (hv : ∀ n i, MemLp (v n i) 2 (μ i)) (hz : ∀ i, MemLp (z i) 2 (μ i))
    {B D ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hbase : ∀ i, (∫ x, (z i x) ^ 2 ∂μ i) ≤ B)
    (hdiag : ∀ n ∈ s, ∀ i, (∫ x, (v n i x) ^ 2 ∂μ i) ≤ D)
    (hoff : ∀ n ∈ s, ∀ m ∈ s, n ≠ m → ∀ i,
      |(∫ x, v n i x * v m i x ∂μ i) - (∫ x, (z i x) ^ 2 ∂μ i)| ≤ ε)
    (hcross : ∀ n ∈ s, ∀ i,
      |(∫ x, v n i x * z i x ∂μ i) - (∫ x, (z i x) ^ 2 ∂μ i)| ≤ ε) :
    (∫ x, ((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)) -
        ∏ i, z i (x i)) ^ 2 ∂Measure.pi μ) ≤
      D ^ Fintype.card κ / (s.card : ℝ) +
        3 * ((Fintype.card κ : ℝ) * ε * (B + ε) ^ (Fintype.card κ - 1)) := by
  let E : ℝ := (Fintype.card κ : ℝ) * ε * (B + ε) ^ (Fintype.card κ - 1)
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hd (n : ι) (hn : n ∈ s) :
      (∫ x, (∏ i, v n i (x i)) ^ 2 ∂Measure.pi μ) ≤ D ^ Fintype.card κ :=
    coordinate_product_sq_le_pow (v n) (hdiag n hn)
  have ho (n : ι) (hn : n ∈ s) (m : ι) (hm : m ∈ s) (hnm : n ≠ m) :
      (∫ x, (∏ i, v n i (x i)) * (∏ i, v m i (x i)) ∂Measure.pi μ) ≤
        (∫ x, (∏ i, z i (x i)) ^ 2 ∂Measure.pi μ) + E := by
    have he := coordinate_product_pair_error_le (v n) (v m) z hB hε hbase (hoff n hn m hm hnm)
    have hu := (abs_le.mp he).2
    change _ ≤ _ + E
    linarith
  have hc (n : ι) (hn : n ∈ s) :
      (∫ x, (∏ i, z i (x i)) ^ 2 ∂Measure.pi μ) - E ≤
        (∫ x, (∏ i, v n i (x i)) * (∏ i, z i (x i)) ∂Measure.pi μ) := by
    have he := coordinate_product_pair_error_le (v n) z z hB hε hbase (hcross n hn)
    have hl := (abs_le.mp he).1
    change _ - E ≤ _
    linarith
  exact integral_average_sub_sq_le_of_memLp (μ := Measure.pi μ) s hs
    (fun n x => ∏ i, v n i (x i)) (fun x => ∏ i, z i (x i))
    (fun n => memLp_coordinate_prod (v n) (hv n)) (memLp_coordinate_prod z hz)
    hE hd ho hc

theorem integral_iterated_eq_coordinate_prod {κ α β : Type*} [Fintype κ]
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : κ → Measure α) (ν : κ → Measure β)
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (F : (κ → α) → (κ → β) → ℝ)
    (hF : Integrable (fun q : κ → α × β => F (fun i => (q i).1) (fun i => (q i).2))
      (Measure.pi (fun i => (μ i).prod (ν i)))) :
    (∫ a, ∫ b, F a b ∂Measure.pi ν ∂Measure.pi μ) =
      ∫ q : κ → α × β, F (fun i => (q i).1) (fun i => (q i).2)
        ∂Measure.pi (fun i => (μ i).prod (ν i)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow α β κ
  have he := measurePreserving_arrowProdEquivProdArrow α β κ μ ν
  have hgroup : Integrable (fun p : (κ → α) × (κ → β) => F p.1 p.2)
      ((Measure.pi μ).prod (Measure.pi ν)) := by
    apply (he.integrable_comp_emb e.measurableEmbedding).1
    exact hF
  rw [← integral_prod _ hgroup]
  exact (he.integral_comp' (fun p => F p.1 p.2)).symm

theorem memLp_average_coordinate_products {κ ι : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] (s : Finset ι)
    (v : ι → (i : κ) → Ω i → ℝ) (z : (i : κ) → Ω i → ℝ)
    (hv : ∀ n i, MemLp (v n i) 2 (μ i)) (hz : ∀ i, MemLp (z i) 2 (μ i)) :
    MemLp (fun x => (s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)) -
      ∏ i, z i (x i)) 2 (Measure.pi μ) := by
  exact ((memLp_finsetSum s (fun n _ => memLp_coordinate_prod (v n) (hv n))).const_mul
    (s.card : ℝ)⁻¹).sub (memLp_coordinate_prod z hz)

theorem expected_integral_average_products_sub_sq_le
    {κ ι α β : Type*} [Fintype κ] [MeasurableSpace α] [MeasurableSpace β]
    (μ : κ → Measure α) (ν : κ → Measure β)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (s : Finset ι) (hs : s.Nonempty) (v : ι → κ → α → β → ℝ) (z : κ → β → ℝ)
    (hv : ∀ n i, MemLp (fun p : α × β => v n i p.1 p.2) 2 ((μ i).prod (ν i)))
    (hz : ∀ i, MemLp (z i) 2 (ν i))
    {B D ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hbase : ∀ i, (∫ x, (z i x) ^ 2 ∂ν i) ≤ B)
    (hdiag : ∀ n ∈ s, ∀ i, (∫ p : α × β, (v n i p.1 p.2) ^ 2 ∂(μ i).prod (ν i)) ≤ D)
    (hoff : ∀ n ∈ s, ∀ m ∈ s, n ≠ m → ∀ i,
      |(∫ p : α × β, v n i p.1 p.2 * v m i p.1 p.2 ∂(μ i).prod (ν i)) -
        (∫ x, (z i x) ^ 2 ∂ν i)| ≤ ε)
    (hcross : ∀ n ∈ s, ∀ i,
      |(∫ p : α × β, v n i p.1 p.2 * z i p.2 ∂(μ i).prod (ν i)) -
        (∫ x, (z i x) ^ 2 ∂ν i)| ≤ ε) :
    (∫ a, ∫ b, ((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (a i) (b i)) -
        ∏ i, z i (b i)) ^ 2 ∂Measure.pi ν ∂Measure.pi μ) ≤
      D ^ Fintype.card κ / (s.card : ℝ) +
        3 * ((Fintype.card κ : ℝ) * ε * (B + ε) ^ (Fintype.card κ - 1)) := by
  let V : ι → κ → α × β → ℝ := fun n i p => v n i p.1 p.2
  let Z : κ → α × β → ℝ := fun i p => z i p.2
  have hZ (i : κ) : MemLp (Z i) 2 ((μ i).prod (ν i)) := (hz i).comp_snd (μ i)
  have hZsq (i : κ) : (∫ p : α × β, (Z i p) ^ 2 ∂(μ i).prod (ν i)) =
      ∫ x, (z i x) ^ 2 ∂ν i := by
    simpa [Z] using (integral_fun_snd (μ := μ i) (ν := ν i) (fun x => (z i x) ^ 2))
  have hb : ∀ i, (∫ p : α × β, (Z i p) ^ 2 ∂(μ i).prod (ν i)) ≤ B := by
    simpa only [hZsq] using hbase
  have ho : ∀ n ∈ s, ∀ m ∈ s, n ≠ m → ∀ i,
      |(∫ p, V n i p * V m i p ∂(μ i).prod (ν i)) -
        (∫ p, (Z i p) ^ 2 ∂(μ i).prod (ν i))| ≤ ε := by
    simpa only [hZsq] using hoff
  have hc : ∀ n ∈ s, ∀ i,
      |(∫ p, V n i p * Z i p ∂(μ i).prod (ν i)) -
        (∫ p, (Z i p) ^ 2 ∂(μ i).prod (ν i))| ≤ ε := by
    simpa only [hZsq] using hcross
  have h := integral_average_coordinate_products_sub_sq_le
    (μ := fun i => (μ i).prod (ν i)) s hs V Z hv hZ hB hε hb hdiag ho hc
  have hi := (memLp_average_coordinate_products s V Z hv hZ).integrable_sq
  rw [integral_iterated_eq_coordinate_prod μ ν _ hi]
  exact h

end InvariantRotation.SamplingMomentBounds

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingPhaseMoments
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductSamplingPhaseMoments

theorem eVariationOn_ofReal (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => (f x : ℂ)) s = eVariationOn f s := by
  simp only [eVariationOn, Complex.isometry_ofReal.edist_eq]

theorem real_bv_discrepancy {m : ℕ} (hm : 200 ≤ m)
    {N₀ N : ℝ} {n n' : ℕ} (hp : ScalarSampling.SamplingPair m N₀ N n n')
    (f g : ℝ → ℝ) (hf : BoundedVariationOn f (Icc (0 : ℝ) 1))
    (hg : BoundedVariationOn g (Icc (0 : ℝ) 1)) :
    |(∫ a, f (Int.fract ((n : ℝ) * a)) * g (Int.fract ((n' : ℝ) * a))
        ∂UniformIntervalPhase.lambdaLaw N₀) -
      (∫ t in (0 : ℝ)..1, f t) * (∫ t in (0 : ℝ)..1, g t)| ≤
      (29 / (m : ℝ)^80) *
        (sSup ((fun t => |f t|) '' Icc (0 : ℝ) 1) +
          (eVariationOn f (Icc (0 : ℝ) 1)).toReal) *
        (sSup ((fun t => |g t|) '' Icc (0 : ℝ) 1) +
          (eVariationOn g (Icc (0 : ℝ) 1)).toReal) := by
  have hfc : BoundedVariationOn (fun t => (f t : ℂ)) (Icc (0 : ℝ) 1) := by
    simpa only [BoundedVariationOn, eVariationOn_ofReal] using hf
  have hgc : BoundedVariationOn (fun t => (g t : ℂ)) (Icc (0 : ℝ) 1) := by
    simpa only [BoundedVariationOn, eVariationOn_ofReal] using hg
  have hsep : ∀ i j : ℤ, |i| ≤ (m ^ 300 : ℕ) → |j| ≤ (m ^ 300 : ℕ) →
      (i, j) ≠ (0, 0) → N * (m : ℝ)^1000 < |(i : ℝ) * n + (j : ℝ) * n'| := by
    intro i j hi hj hij
    apply hp.separated i j hi hj
    by_contra h
    push Not at h
    exact hij (by simp [h.1, h.2])
  have h := ScalarRectangles.scalar_bv_discrepancy m hm N₀ N hp.N₀_pos hp.N₀_le
    hp.N_le n n' hp.first_range.1 hp.second_range.1 hsep
    (fun t => (f t : ℂ)) (fun t => (g t : ℂ)) hfc hgc
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal,
    intervalIntegral.integral_ofReal, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, eVariationOn_ofReal] using h

theorem real_one_phase_error {N₀ n : ℝ} (hN : 0 < N₀) (hn : 0 < n)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t) :
    |(∫ a, f (Int.fract (n * a)) ∂UniformIntervalPhase.lambdaLaw N₀) -
      (∫ t in (0 : ℝ)..1, f t)| ≤
        (N₀ / n) * ∫ t in (0 : ℝ)..1, f t := by
  rw [UniformIntervalPhase.lambdaLaw_eq_cond N₀ hN]
  have h := PeriodicIntervalDiscrepancy.uniform_angle_test_le hN hn hf
  have heq : (∫ t in (0 : ℝ)..1, |f t|) = ∫ t in (0 : ℝ)..1, f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact abs_of_nonneg (hf0 t (by simpa using ht))
  simpa only [heq] using h

theorem integral_unitInterval (f : ℝ → ℝ) :
    (∫ t, f t ∂unitInterval) = ∫ t in (0 : ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [unitInterval, restrict_Ico_eq_restrict_Ioc]

theorem fractionLaw_le_two {N₀ n : ℝ} (hN : 0 < N₀) (hn : N₀ ≤ n) :
    UniformIntervalPhase.fractionLaw N₀ n ≤ (2 : ℝ≥0∞) • unitInterval := by
  rw [← (UniformIntervalPhase.scalar_marginal N₀ n hN (hN.trans_le hn)).2.2]
  have hb := UniformIntervalPhase.fractionDensity_le_two N₀ n hN hn
  have h := withDensity_mono (μ := unitInterval) (f := fun t =>
    ENNReal.ofReal (UniformIntervalPhase.fractionDensity N₀ n t))
    (g := fun _ => (2 : ℝ≥0∞)) (hb.mono fun t ht => by
      simpa using ENNReal.ofReal_le_ofReal ht)
  simpa only [withDensity_const, unitInterval] using h

theorem integral_sample_le_two {N₀ n : ℝ} (hN : 0 < N₀) (hn : N₀ ≤ n)
    (f : ℝ → ℝ) (hf : Integrable f unitInterval)
    (hf0 : ∀ᵐ t ∂unitInterval, 0 ≤ f t) :
    Integrable (fun a => f (Int.fract (n * a))) (UniformIntervalPhase.lambdaLaw N₀) ∧
      (∫ a, f (Int.fract (n * a)) ∂UniformIntervalPhase.lambdaLaw N₀) ≤
        2 * ∫ t, f t ∂unitInterval := by
  have hdom := fractionLaw_le_two hN hn
  have hfi := (hf.smul_measure (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mono_measure hdom
  have hm : Measurable (fun a : ℝ => Int.fract (n * a)) :=
    (measurable_const_mul n).fract
  refine ⟨hfi.comp_measurable hm, ?_⟩
  rw [← integral_map hm.aemeasurable hfi.aestronglyMeasurable]
  have hb := integral_mono_measure hdom (Measure.ae_smul_measure hf0 (2 : ℝ≥0∞))
    (hf.smul_measure (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  simpa [integral_smul_measure, UniformIntervalPhase.fractionLaw] using hb

theorem realBVSize_nonneg (f : ℝ → ℝ) : 0 ≤ realBVSize f := by
  apply add_nonneg _ ENNReal.toReal_nonneg
  apply Real.sSup_nonneg
  rintro _ ⟨t, _, rfl⟩
  exact abs_nonneg _

theorem sample_memLp {u : ℝ → ℝ → ℝ} {N₀ C : ℝ} (hN : 0 < N₀)
    (hu : Measurable (Function.uncurry u))
    (hbound : ∀ s t, |u s t| ≤ C) (n : ℕ) :
    MemLp (sample u n) 2 ((UniformIntervalPhase.lambdaLaw N₀).prod unitInterval) := by
  let := UniformIntervalPhase.lambdaLaw_probability N₀ hN
  apply MemLp.of_bound (measurable_sample hu n).aestronglyMeasurable C
  exact Filter.Eventually.of_forall (fun p => by simpa [sample, Real.norm_eq_abs] using hbound p.2 _)

theorem mean_memLp {u : ℝ → ℝ → ℝ} {C : ℝ}
    (hu : Measurable (Function.uncurry u)) (hbound : ∀ s t, |u s t| ≤ C) :
    MemLp (mean u) 2 unitInterval := by
  apply MemLp.of_bound (measurable_mean hu).aestronglyMeasurable C
  apply Filter.Eventually.of_forall
  intro s
  have h := norm_integral_le_of_norm_le_const (μ := unitInterval)
    (f := u s) (Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs] using hbound s t))
  simpa [mean] using h

theorem coordinate_pair_error_le {m : ℕ} (hm : 200 ≤ m)
    {N₀ N C V : ℝ} {n n' : ℕ} (hp : ScalarSampling.SamplingPair m N₀ N n n')
    (u : ℝ → ℝ → ℝ) (hu : Measurable (Function.uncurry u))
    (hbound : ∀ s t, |u s t| ≤ C)
    (hBV : ∀ s ∈ Ico (0 : ℝ) 1, BoundedVariationOn (u s) (Icc (0 : ℝ) 1))
    (hV : ∀ s ∈ Ico (0 : ℝ) 1, realBVSize (u s) ≤ V) :
    |(∫ p, sample u n p * sample u n' p ∂(UniformIntervalPhase.lambdaLaw N₀).prod unitInterval) -
      (∫ s, (mean u s)^2 ∂unitInterval)| ≤ (29 / (m : ℝ)^80) * V^2 := by
  let := UniformIntervalPhase.lambdaLaw_probability N₀ hp.N₀_pos
  have hv := sample_memLp hp.N₀_pos hu hbound n
  have hv' := sample_memLp hp.N₀_pos hu hbound n'
  have hz := mean_memLp hu hbound
  have hi : Integrable (fun p => sample u n p * sample u n' p)
      ((UniformIntervalPhase.lambdaLaw N₀).prod unitInterval) := hv.integrable_mul hv'
  rw [integral_prod_symm _ hi, ← integral_sub hi.integral_prod_right hz.integrable_sq]
  have hb : ∀ s ∈ Ico (0 : ℝ) 1,
      |(∫ a, sample u n (a, s) * sample u n' (a, s)
          ∂UniformIntervalPhase.lambdaLaw N₀) - (mean u s)^2| ≤
        (29 / (m : ℝ)^80) * V^2 := by
    intro s hs
    have h := real_bv_discrepancy hm hp (u s) (u s) (hBV s hs) (hBV s hs)
    have hV0 : 0 ≤ V := (realBVSize_nonneg (u s)).trans (hV s hs)
    have hsquare : realBVSize (u s) * realBVSize (u s) ≤ V * V :=
      mul_le_mul (hV s hs) (hV s hs) (realBVSize_nonneg _) hV0
    calc
      _ ≤ (29 / (m : ℝ)^80) * realBVSize (u s) * realBVSize (u s) := by
        simpa only [sample, mean, integral_unitInterval, pow_two, realBVSize] using h
      _ ≤ _ := by
        rw [mul_assoc, pow_two]
        exact mul_le_mul_of_nonneg_left hsquare (by positivity)
  have h := norm_integral_le_of_norm_le_const (μ := unitInterval)
    (f := fun s => (∫ a, sample u n (a, s) * sample u n' (a, s)
      ∂UniformIntervalPhase.lambdaLaw N₀) - (mean u s)^2)
    (C := (29 / (m : ℝ)^80) * V^2)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
      simpa only [Real.norm_eq_abs] using hb s hs)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

theorem section_intervalIntegrable {u : ℝ → ℝ → ℝ} {C : ℝ}
    (hu : Measurable (Function.uncurry u)) (hbound : ∀ s t, |u s t| ≤ C) (s : ℝ) :
    IntervalIntegrable (u s) volume 0 1 := by
  have hm : Measurable (u s) := hu.comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (u s) unitInterval :=
    (MemLp.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs] using hbound s t)) : MemLp (u s) 1 unitInterval).integrable le_rfl
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).2
  simpa only [unitInterval, IntegrableOn, restrict_Ico_eq_restrict_Ioc] using hi

theorem coordinate_cross_error_le {N₀ C : ℝ} (hN : 0 < N₀)
    {n : ℕ} (hn : 0 < n)
    (u : ℝ → ℝ → ℝ) (hu : Measurable (Function.uncurry u))
    (hbound : ∀ s t, |u s t| ≤ C) (hzero : ∀ s t, 0 ≤ u s t) :
    |(∫ p, sample u n p * mean u p.2 ∂(UniformIntervalPhase.lambdaLaw N₀).prod unitInterval) -
      (∫ s, (mean u s)^2 ∂unitInterval)| ≤
        (N₀ / (n : ℝ)) * ∫ s, (mean u s)^2 ∂unitInterval := by
  let := UniformIntervalPhase.lambdaLaw_probability N₀ hN
  have hv := sample_memLp hN hu hbound n
  have hz := mean_memLp hu hbound
  have hi : Integrable (fun p : ℝ × ℝ => sample u n p * mean u p.2)
      ((UniformIntervalPhase.lambdaLaw N₀).prod unitInterval) :=
    hv.integrable_mul (hz.comp_snd (UniformIntervalPhase.lambdaLaw N₀))
  rw [integral_prod_symm _ hi, ← integral_sub hi.integral_prod_right hz.integrable_sq]
  have hdiff := hi.integral_prod_right.sub hz.integrable_sq
  have hb (s : ℝ) :
      |(∫ a, sample u n (a, s) * mean u s ∂UniformIntervalPhase.lambdaLaw N₀) -
        (mean u s)^2| ≤ (N₀ / (n : ℝ)) * (mean u s)^2 := by
    have hz0 : 0 ≤ mean u s := integral_nonneg (hzero s)
    have he := real_one_phase_error (n := (n : ℝ)) hN (by exact_mod_cast hn)
      (section_intervalIntegrable hu hbound s) (fun t _ => hzero s t)
    rw [← integral_unitInterval] at he
    change |(∫ a, sample u n (a, s) ∂UniformIntervalPhase.lambdaLaw N₀) - mean u s| ≤
      (N₀ / (n : ℝ)) * mean u s at he
    rw [integral_mul_const]
    calc
      _ = |((∫ a, sample u n (a, s) ∂UniformIntervalPhase.lambdaLaw N₀) -
          mean u s) * mean u s| := by congr 1; ring
      _ = |(∫ a, sample u n (a, s) ∂UniformIntervalPhase.lambdaLaw N₀) -
          mean u s| * mean u s := by rw [abs_mul, abs_of_nonneg hz0]
      _ ≤ ((N₀ / (n : ℝ)) * mean u s) * mean u s :=
        mul_le_mul_of_nonneg_right he hz0
      _ = _ := by ring
  calc
    _ ≤ ∫ s, |(∫ a, sample u n (a, s) * mean u s
          ∂UniformIntervalPhase.lambdaLaw N₀) - (mean u s)^2| ∂unitInterval :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s, (N₀ / (n : ℝ)) * (mean u s)^2 ∂unitInterval :=
      integral_mono_ae hdiff.abs (hz.integrable_sq.const_mul _)
        (Filter.Eventually.of_forall hb)
    _ = _ := integral_const_mul _ _

theorem coordinate_square_le_two {N₀ C : ℝ} (hN : 0 < N₀)
    {n : ℕ} (hn : N₀ ≤ (n : ℝ))
    (u : ℝ → ℝ → ℝ) (hu : Measurable (Function.uncurry u))
    (hbound : ∀ s t, |u s t| ≤ C) :
    (∫ p, (sample u n p)^2 ∂(UniformIntervalPhase.lambdaLaw N₀).prod unitInterval) ≤
      2 * ∫ s, ∫ t, (u s t)^2 ∂unitInterval ∂unitInterval := by
  let := UniformIntervalPhase.lambdaLaw_probability N₀ hN
  have hv := sample_memLp hN hu hbound n
  have hkernel : MemLp (Function.uncurry u) 2 (unitInterval.prod unitInterval) := by
    apply MemLp.of_bound hu.aestronglyMeasurable C
    exact Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs, Function.uncurry] using hbound p.1 p.2)
  have hi : Integrable (fun p => (sample u n p)^2)
      ((UniformIntervalPhase.lambdaLaw N₀).prod unitInterval) := hv.integrable_sq
  rw [integral_prod_symm _ hi, ← integral_const_mul]
  apply integral_mono_ae hi.integral_prod_right
    (hkernel.integrable_sq.integral_prod_left.const_mul 2)
  apply Filter.Eventually.of_forall
  intro s
  have hm : Measurable (u s) := hu.comp (measurable_const.prodMk measurable_id)
  have hs : MemLp (u s) 2 unitInterval := by
    apply MemLp.of_bound hm.aestronglyMeasurable C
    exact Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hbound s t)
  exact (integral_sample_le_two hN hn (fun t => (u s t)^2) hs.integrable_sq
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).2

theorem coordinate_cross_error_le_four {N₀ C : ℝ} (hN : 0 < N₀)
    {n : ℕ} (hn : 0 < n)
    (u : ℝ → ℝ → ℝ) (hu : Measurable (Function.uncurry u))
    (hbound : ∀ s t, |u s t| ≤ C) (hzero : ∀ s t, 0 ≤ u s t)
    (hmean : ∀ s, mean u s ≤ 2) :
    |(∫ p, sample u n p * mean u p.2 ∂(UniformIntervalPhase.lambdaLaw N₀).prod unitInterval) -
      (∫ s, (mean u s)^2 ∂unitInterval)| ≤ 4 * N₀ / (n : ℝ) := by
  have hA : (∫ s, (mean u s)^2 ∂unitInterval) ≤ 4 := by
    have hb (s : ℝ) : (mean u s)^2 ≤ 4 := by
      have h0 : 0 ≤ mean u s := integral_nonneg (hzero s)
      nlinarith [hmean s]
    simpa using integral_mono_ae (mean_memLp hu hbound).integrable_sq
      (integrable_const (4 : ℝ)) (Filter.Eventually.of_forall hb)
  calc
    _ ≤ (N₀ / (n : ℝ)) * ∫ s, (mean u s)^2 ∂unitInterval :=
      coordinate_cross_error_le hN hn u hu hbound hzero
    _ ≤ (N₀ / (n : ℝ)) * 4 := mul_le_mul_of_nonneg_left hA (by positivity)
    _ = _ := by ring

theorem expected_average_error_le {κ : Type*} [Fintype κ]
    {m : ℕ} (hm : 200 ≤ m) (N₀ : κ → ℝ) (hN : ∀ i, 0 < N₀ i)
    (N : ℝ) (powers : Finset ℕ) (hpowers : powers.Nonempty)
    (hpositive : ∀ n ∈ powers, 0 < n)
    (hlarge : ∀ n ∈ powers, ∀ i, N₀ i ≤ (n : ℝ))
    (hseparated : ∀ n ∈ powers, ∀ n' ∈ powers, n ≠ n' → ∀ i,
      ScalarSampling.SamplingPair m (N₀ i) N n n')
    (u : κ → ℝ → ℝ → ℝ) (C : κ → ℝ)
    (hu : ∀ i, Measurable (Function.uncurry (u i)))
    (hbound : ∀ i s t, |u i s t| ≤ C i)
    (hzero : ∀ i s t, 0 ≤ u i s t)
    (hmean : ∀ i s, mean (u i) s ≤ 2)
    {B D V ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hBV : ∀ i s, s ∈ Ico (0 : ℝ) 1 → BoundedVariationOn (u i s) (Icc (0 : ℝ) 1))
    (hV : ∀ i s, s ∈ Ico (0 : ℝ) 1 → realBVSize (u i s) ≤ V)
    (hbase : ∀ i, (∫ s, (mean (u i) s)^2 ∂unitInterval) ≤ B)
    (hsquare : ∀ i, (∫ s, ∫ t, (u i s t)^2 ∂unitInterval ∂unitInterval) ≤ D)
    (hpairBudget : (29 / (m : ℝ)^80) * V^2 ≤ ε)
    (hcrossBudget : ∀ n ∈ powers, ∀ i, 4 * N₀ i / (n : ℝ) ≤ ε) :
    (∫ a, ∫ x, ((powers.card : ℝ)⁻¹ *
        (∑ n ∈ powers, ∏ i, u i (x i) (Int.fract ((n : ℝ) * a i))) -
        ∏ i, mean (u i) (x i))^2
      ∂Measure.pi (fun _ : κ => unitInterval)
      ∂Measure.pi (fun i => UniformIntervalPhase.lambdaLaw (N₀ i))) ≤
      (2 * D)^Fintype.card κ / (powers.card : ℝ) +
        3 * ((Fintype.card κ : ℝ) * ε * (B + ε)^(Fintype.card κ - 1)) := by
  let (i : κ) : IsProbabilityMeasure (UniformIntervalPhase.lambdaLaw (N₀ i)) :=
    UniformIntervalPhase.lambdaLaw_probability (N₀ i) (hN i)
  apply InvariantRotation.SamplingMomentBounds.expected_integral_average_products_sub_sq_le
    (fun i => UniformIntervalPhase.lambdaLaw (N₀ i)) (fun _ : κ => unitInterval)
    powers hpowers (fun n i a x => u i x (Int.fract ((n : ℝ) * a)))
    (fun i => mean (u i))
  · intro n i
    exact sample_memLp (hN i) (hu i) (hbound i) n
  · intro i
    exact mean_memLp (hu i) (hbound i)
  · exact hB
  · exact hε
  · exact hbase
  · intro n hn i
    exact (coordinate_square_le_two (hN i) (hlarge n hn i) (u i) (hu i) (hbound i)).trans
      (mul_le_mul_of_nonneg_left (hsquare i) (by norm_num))
  · intro n hn n' hn' hnn' i
    exact (coordinate_pair_error_le hm (hseparated n hn n' hn' hnn' i)
      (u i) (hu i) (hbound i) (hBV i) (hV i)).trans hpairBudget
  · intro n hn i
    exact (coordinate_cross_error_le_four (hN i) (hpositive n hn)
      (u i) (hu i) (hbound i) (hzero i) (hmean i)).trans (hcrossBudget n hn i)

end Invariant233.ProductSamplingPhaseMoments

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingPhaseScale
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductSamplingPhaseMoments

theorem samplingPair_of_product_powers {p : ProductScaleData} (hp : ProductScaleLaws p)
    {j : ℕ} {powers : Finset ℕ} (hs : ProductSamplingPowersAt p j powers)
    {N₀ : ℝ} (hN₀ : 0 < N₀) (hN : N₀ ≤ p.N j)
    {n n' : ℕ} (hn : n ∈ powers) (hn' : n' ∈ powers) (hne : n ≠ n') :
    ScalarSampling.SamplingPair (p.m j) N₀ (p.N j) n n' := by
  refine ⟨hN₀, hN, ?_, hs.positive n hn, hs.positive n' hn', hne,
    hs.range n hn, hs.range n' hn', ?_⟩
  · have hK : (p.K j : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_K j
    dsimp [ProductScaleData.N]
    nlinarith [Nat.cast_nonneg (α := ℝ) (p.m j)]
  · intro v v' hv hv' hnonzero
    have h := hs.separation n hn n' hn' hne v v' hv hv' hnonzero
    have hr : ((p.m j * p.K j * p.m j ^ 1000 : ℕ) : ℝ) <
        |(v : ℝ) * n + (v' : ℝ) * n'| := by exact_mod_cast h
    simpa only [ProductScaleData.N, Nat.cast_mul, Nat.cast_pow] using hr

theorem coordinate_scale_le_power {p : ProductScaleData} (hp : ProductScaleLaws p)
    {j : ℕ} (hm : 200 ≤ p.m j) {powers : Finset ℕ}
    (hs : ProductSamplingPowersAt p j powers) {N₀ : ℝ} (hN : N₀ ≤ p.N j)
    {n : ℕ} (hn : n ∈ powers) : N₀ ≤ (n : ℝ) := by
  have hK : (p.K j : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_K j
  have hNm : p.N j ≤ (p.m j : ℝ)^2 := by
    dsimp [ProductScaleData.N]
    nlinarith [Nat.cast_nonneg (α := ℝ) (p.m j)]
  have hh := ScalarRectangles.horizon_ge_twice_square (m := (p.m j : ℝ)) (by exact_mod_cast hm)
  have hr := (hs.range n hn).1
  linarith

end Invariant233.ProductSamplingPhaseMoments

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingNumericalBudget
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductSamplingPhaseMoments

theorem pair_budget_of_power_ten {m : ℝ} (hm : 200 ≤ m) :
    (29 / m^80) * (16 * m^10)^2 ≤ m^(-50 : ℝ) := by
  have hm0 : 0 < m := by linarith
  have hm1 : 1 ≤ m := by linarith
  have hsmall : (7424 : ℝ) ≤ m^2 := by nlinarith
  have hsize : (7424 : ℝ) ≤ m^10 := hsmall.trans
    (pow_le_pow_right₀ hm1 (by norm_num : 2 ≤ 10))
  rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hm0 80)]
  have hpow : m^(-50 : ℝ) * m^80 = m^30 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hm0]
    norm_num
  rw [hpow]
  calc
    29 * (16 * m^10)^2 = 7424 * m^20 := by ring
    _ ≤ m^10 * m^20 := mul_le_mul_of_nonneg_right hsize (by positivity)
    _ = m^30 := by ring

theorem cross_budget_of_horizon {m N₀ n : ℝ} (hm : 200 ≤ m)
    (hN : N₀ ≤ m^2)
    (hn : m^((7 / 10 : ℝ) * m) / 2 ≤ n) :
    4 * N₀ / n ≤ m^(-50 : ℝ) := by
  have hm0 : 0 < m := by linarith
  have hm1 : 1 ≤ m := by linarith
  have hQ : 0 < m^((7 / 10 : ℝ) * m) := Real.rpow_pos_of_pos hm0 _
  have hpow : m^(140 : ℝ) ≤ m^((7 / 10 : ℝ) * m) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  have hgap : (8 : ℝ) ≤ m^(88 : ℝ) := by
    calc
      (8 : ℝ) ≤ m := by linarith
      _ = m^(1 : ℝ) := (Real.rpow_one m).symm
      _ ≤ m^(88 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  calc
    4 * N₀ / n ≤ 4 * m^2 / n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by norm_num))
        ((div_pos hQ (by norm_num)).trans_le hn).le
    _ ≤ 4 * m^2 / (m^((7 / 10 : ℝ) * m) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (div_pos hQ (by norm_num)) hn
    _ = 8 * (m^(2 : ℝ) / m^((7 / 10 : ℝ) * m)) := by rw [Real.rpow_two]; ring
    _ ≤ 8 * (m^(2 : ℝ) / m^(140 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_left (by positivity)
        (Real.rpow_pos_of_pos hm0 _) hpow
    _ = 8 * m^(-138 : ℝ) := by rw [← Real.rpow_sub hm0]; norm_num
    _ ≤ m^(88 : ℝ) * m^(-138 : ℝ) :=
      mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hm0.le _)
    _ = m^(-50 : ℝ) := by rw [← Real.rpow_add hm0]; norm_num

theorem averaged_square_budget {m : ℕ} (hm : 200 ≤ m) :
    1 + ((m : ℝ)^(-(3 / 5 : ℝ)))^2 /
        (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 ≤
      1 + 4 * (m : ℝ)^(-6 / 5 : ℝ) := by
  simpa only [neg_div] using add_le_add (le_rfl : (1 : ℝ) ≤ 1)
    (ScalarSampling.kernel_average_square_remainder_le hm)

theorem product_sampling_nonempty {p : ProductScaleData} (hp : ProductScaleLaws p)
    {j : ℕ} {powers : Finset ℕ} (hs : ProductSamplingPowersAt p j powers) :
    powers.Nonempty := by
  have hpos : 0 < (p.m j : ℝ)^((69 / 100 : ℝ) * p.m j) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp.m_pos j) _
  exact Finset.card_pos.mp (by exact_mod_cast hpos.trans_le hs.cardinality)

theorem expected_average_error_le_source_scale_oai {κ : Type*} [Fintype κ]
    {p : ProductScaleData} (hp : ProductScaleLaws p) {j : ℕ} (hm : 200 ≤ p.m j)
    (N₀ : κ → ℝ) (hN : ∀ i, 0 < N₀ i) (hNle : ∀ i, N₀ i ≤ p.N j)
    (powers : Finset ℕ) (hs : ProductSamplingPowersAt p j powers)
    (u : κ → ℝ → ℝ → ℝ) (C : κ → ℝ)
    (hu : ∀ i, Measurable (Function.uncurry (u i)))
    (hbound : ∀ i s t, |u i s t| ≤ C i)
    (hzero : ∀ i s t, 0 ≤ u i s t)
    (hmean : ∀ i s, mean (u i) s ≤ 2)
    (hBV : ∀ i s, s ∈ Ico (0 : ℝ) 1 → BoundedVariationOn (u i s) (Icc (0 : ℝ) 1))
    (hV : ∀ i s, s ∈ Ico (0 : ℝ) 1 → realBVSize (u i s) ≤ 16 * (p.m j : ℝ)^10)
    (hbase : ∀ i, (∫ s, (mean (u i) s)^2 ∂unitInterval) ≤
      1 + ((p.m j : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (p.m j : ℝ)^(-(3 / 5 : ℝ)))^2)
    {D : ℝ}
    (hsquare : ∀ i, (∫ s, ∫ t, (u i s t)^2 ∂unitInterval ∂unitInterval) ≤ D) :
    (∫ a, ∫ x, ((powers.card : ℝ)⁻¹ *
        (∑ n ∈ powers, ∏ i, u i (x i) (Int.fract ((n : ℝ) * a i))) -
        ∏ i, mean (u i) (x i))^2
      ∂Measure.pi (fun _ : κ => unitInterval)
      ∂Measure.pi (fun i => UniformIntervalPhase.lambdaLaw (N₀ i))) ≤
      (2 * D)^Fintype.card κ / (powers.card : ℝ) +
        3 * ((Fintype.card κ : ℝ) * (p.m j : ℝ)^(-50 : ℝ) *
          (1 + 4 * (p.m j : ℝ)^(-6 / 5 : ℝ) +
            (p.m j : ℝ)^(-50 : ℝ))^(Fintype.card κ - 1)) := by
  apply expected_average_error_le hm N₀ hN (p.N j) powers
    (product_sampling_nonempty hp hs) hs.positive
  · intro n hn i
    exact coordinate_scale_le_power hp hm hs (hNle i) hn
  · intro n hn n' hn' hne i
    exact samplingPair_of_product_powers hp hs (hN i) (hNle i) hn hn' hne
  · exact hu
  · exact hbound
  · exact hzero
  · exact hmean
  · positivity
  · positivity
  · exact hBV
  · exact hV
  · intro i
    exact (hbase i).trans (averaged_square_budget hm)
  · exact hsquare
  · exact pair_budget_of_power_ten (by exact_mod_cast hm)
  · intro n hn i
    exact cross_budget_of_horizon (by exact_mod_cast hm)
      ((hNle i).trans (hp.N_le_square j)) (hs.range n hn).1

end Invariant233.ProductSamplingPhaseMoments

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Invariant233.ProductSamplingPhaseMoments.expected_average_error_le_source_scale_oai.{u_1} := @OAI.Invariant233.ProductSamplingPhaseMoments.expected_average_error_le_source_scale_oai.{u_1}
