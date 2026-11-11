-- Prove2me | solution 1 for OAI.Invariant233.TrialSampling.coordinateSample_offdiag_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:34:38.99501+00:00
-- url     : https://prove2.me/submissions/1ed2f90f-8059-4b01-89a3-db72168a54c9

import Mathlib
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
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
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarEndpointDensity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarEndpointDensity

theorem endpointMap_left (t : ℝ) {z : ℝ} (hz : z ≤ 1 / 2) :
    endpointMap t z = (1 + t) * z := by
  unfold endpointMap cutDistance
  rw [min_eq_left (by linarith)]
  ring

theorem endpointMap_right (t : ℝ) {z : ℝ} (hz : 1 / 2 ≤ z) :
    endpointMap t z = (1 - t) * z + t := by
  unfold endpointMap cutDistance
  rw [min_eq_right (by linarith)]
  ring

theorem continuous_endpointMap (t : ℝ) : Continuous (endpointMap t) := by
  unfold endpointMap cutDistance
  fun_prop

theorem midpoint_pos {t : ℝ} (ht0 : 0 ≤ t) : 0 < midpoint t := by
  unfold midpoint
  linarith

theorem midpoint_lt_one {t : ℝ} (ht1 : t < 1) : midpoint t < 1 := by
  unfold midpoint
  linarith

theorem slopeDensity_pos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (s : ℝ) :
    0 < slopeDensity t s := by
  unfold slopeDensity
  split_ifs <;> positivity

theorem slopeDensity_upper {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (s : ℝ) :
    slopeDensity t s ≤ (1 - t)⁻¹ := by
  unfold slopeDensity
  split_ifs
  · apply inv_anti₀ (by linarith)
    linarith
  · exact le_rfl

theorem slopeDensity_mul_intervalIntegrable {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    IntervalIntegrable (fun s => φ s * slopeDensity t s) volume 0 1 := by
  have hm0 := midpoint_pos ht0
  have hm1 := midpoint_lt_one ht1
  have hleft : IntervalIntegrable (fun s => φ s * slopeDensity t s)
      volume 0 (midpoint t) := by
    have hi : IntervalIntegrable (fun s => φ s * (1 + t)⁻¹)
        volume 0 (midpoint t) := (hφ.mul continuous_const).intervalIntegrable _ _
    apply hi.congr_uIoo
    intro s hs
    rw [uIoo_of_le hm0.le] at hs
    simp only [slopeDensity, ite_eq_left hs.2.le]
  have hright : IntervalIntegrable (fun s => φ s * slopeDensity t s)
      volume (midpoint t) 1 := by
    have hi : IntervalIntegrable (fun s => φ s * (1 - t)⁻¹)
        volume (midpoint t) 1 := (hφ.mul continuous_const).intervalIntegrable _ _
    apply hi.congr_uIoo
    intro s hs
    rw [uIoo_of_le hm1.le] at hs
    simp only [slopeDensity, ite_eq_right (not_le_of_gt hs.1)]
  exact hleft.trans hright

theorem endpointMap_integral {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    (∫ z in (0 : ℝ)..1, φ (endpointMap t z)) =
      ∫ s in (0 : ℝ)..1, φ s * slopeDensity t s := by
  have hp : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have hn : 1 - t ≠ 0 := ne_of_gt (by linarith)
  have hm0 := midpoint_pos ht0
  have hm1 := midpoint_lt_one ht1
  have hc : Continuous (fun z => φ (endpointMap t z)) :=
    hφ.comp (continuous_endpointMap t)
  have hleft : (∫ z in (0 : ℝ)..(1 / 2), φ (endpointMap t z)) =
      (1 + t)⁻¹ * ∫ s in (0 : ℝ)..midpoint t, φ s := by
    calc
      _ = ∫ z in (0 : ℝ)..(1 / 2), φ ((1 + t) * z) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro z hz
        dsimp
        rw [endpointMap_left t hz.2.le]
      _ = _ := by
        rw [intervalIntegral.integral_comp_mul_left φ hp]
        simp only [mul_zero, smul_eq_mul]
        congr 2
        unfold midpoint
        ring
  have hright : (∫ z in (1 / 2 : ℝ)..1, φ (endpointMap t z)) =
      (1 - t)⁻¹ * ∫ s in midpoint t..(1 : ℝ), φ s := by
    calc
      _ = ∫ z in (1 / 2 : ℝ)..1, φ ((1 - t) * z + t) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro z hz
        dsimp
        rw [endpointMap_right t hz.1.le]
      _ = _ := by
        rw [intervalIntegral.integral_comp_mul_add φ hn t]
        simp only [smul_eq_mul]
        congr 2
        · unfold midpoint
          ring
        · ring
  have hd := slopeDensity_mul_intervalIntegrable ht0 ht1 hφ
  have hdleft : (∫ s in (0 : ℝ)..midpoint t, φ s * slopeDensity t s) =
      (1 + t)⁻¹ * ∫ s in (0 : ℝ)..midpoint t, φ s := by
    calc
      _ = ∫ s in (0 : ℝ)..midpoint t, φ s * (1 + t)⁻¹ := by
        apply intervalIntegral.integral_congr_Ioo_of_le hm0.le
        intro s hs
        simp only [slopeDensity, ite_eq_left hs.2.le]
      _ = _ := by rw [intervalIntegral.integral_mul_const]; ring
  have hdright : (∫ s in midpoint t..(1 : ℝ), φ s * slopeDensity t s) =
      (1 - t)⁻¹ * ∫ s in midpoint t..(1 : ℝ), φ s := by
    calc
      _ = ∫ s in midpoint t..(1 : ℝ), φ s * (1 - t)⁻¹ := by
        apply intervalIntegral.integral_congr_Ioo_of_le hm1.le
        intro s hs
        simp only [slopeDensity, ite_eq_right (not_le_of_gt hs.1)]
      _ = _ := by rw [intervalIntegral.integral_mul_const]; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (1 / 2)) (hc.intervalIntegrable (1 / 2) 1), hleft, hright]
  have hdl : IntervalIntegrable (fun s => φ s * slopeDensity t s)
      volume 0 (midpoint t) := hd.mono_set (by
    rw [uIcc_of_le hm0.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hm1.le)
  have hdr : IntervalIntegrable (fun s => φ s * slopeDensity t s)
      volume (midpoint t) 1 := hd.mono_set (by
    rw [uIcc_of_le hm1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hm0.le le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hdl hdr]
  rw [hdleft, hdright]

theorem integral_slopeDensity {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (∫ s in (0 : ℝ)..1, slopeDensity t s) = 1 := by
  have h := endpointMap_integral ht0 ht1 (φ := fun _ => 1) continuous_const
  simpa using h.symm

theorem slopeDensity_deviation {t h : ℝ} (ht0 : 0 ≤ t) (hth : t ≤ h)
    (hh1 : h < 1) (s : ℝ) :
    |slopeDensity t s - 1| ≤ h / (1 - h) := by
  have ht1 : t < 1 := lt_of_le_of_lt hth hh1
  have hh0 : 0 ≤ h := le_trans ht0 hth
  have hp : 0 < 1 + t := by linarith
  have hn : 0 < 1 - t := by linarith
  have hd : 0 < 1 - h := by linarith
  unfold slopeDensity
  split_ifs
  · have heq : (1 + t)⁻¹ - 1 = -(t / (1 + t)) := by
      field_simp
      ring
    rw [heq, abs_neg, abs_of_nonneg (div_nonneg ht0 hp.le)]
    exact div_le_div₀ hh0 hth hd (by linarith)
  · have heq : (1 - t)⁻¹ - 1 = t / (1 - t) := by
      field_simp
      ring
    rw [heq, abs_of_nonneg (div_nonneg ht0 hn.le)]
    exact div_le_div₀ hh0 hth hd (by linarith)

theorem slopeDensity_uniform_upper {t h : ℝ} (ht0 : 0 ≤ t) (hth : t ≤ h)
    (hh1 : h < 1) (s : ℝ) : slopeDensity t s ≤ (1 - h)⁻¹ := by
  apply (slopeDensity_upper ht0 (lt_of_le_of_lt hth hh1) s).trans
  exact inv_anti₀ (by linarith) (by linarith)

theorem measurable_slopeDensity : Measurable (fun p : ℝ × ℝ => slopeDensity p.1 p.2) := by
  unfold slopeDensity midpoint
  apply Measurable.ite
  · exact measurableSet_le measurable_snd
      ((measurable_const.add measurable_fst).div_const 2)
  · exact (measurable_const.add measurable_fst).inv
  · exact (measurable_const.sub measurable_fst).inv

theorem slopeDensity_parameter_integrable {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1)
    (s : ℝ) : IntervalIntegrable (fun t => slopeDensity t s) volume 0 h := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound (by rw [uIoc_of_le hh0]; exact measure_Ioc_lt_top)
    ((measurable_slopeDensity.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    ((1 - h)⁻¹)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [uIoc_of_le hh0] at ht
  change ‖slopeDensity t s‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (slopeDensity_pos ht.1.le (lt_of_le_of_lt ht.2 hh1) s)]
  exact slopeDensity_uniform_upper ht.1.le ht.2 hh1 s

theorem averagedDensity_nonneg {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) (s : ℝ) :
    0 ≤ averagedDensity h s := by
  unfold averagedDensity
  apply mul_nonneg (inv_nonneg.mpr hh0.le)
  apply intervalIntegral.integral_nonneg hh0.le
  intro t ht
  exact (slopeDensity_pos ht.1 (lt_of_le_of_lt ht.2 hh1) s).le

theorem averagedDensity_upper {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) (s : ℝ) :
    averagedDensity h s ≤ (1 - h)⁻¹ := by
  have hint := slopeDensity_parameter_integrable hh0.le hh1 s
  have hb : (∫ t in (0 : ℝ)..h, slopeDensity t s) ≤ h * (1 - h)⁻¹ := by
    calc
      _ ≤ ∫ _t in (0 : ℝ)..h, (1 - h)⁻¹ :=
        intervalIntegral.integral_mono_on hh0.le hint intervalIntegrable_const
          (fun t ht => slopeDensity_uniform_upper ht.1 ht.2 hh1 s)
      _ = _ := by simp
  unfold averagedDensity
  calc
    _ ≤ h⁻¹ * (h * (1 - h)⁻¹) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh0.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hh0.ne', one_mul]

theorem averagedDensity_deviation {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) (s : ℝ) :
    |averagedDensity h s - 1| ≤ h / (1 - h) := by
  have hint := slopeDensity_parameter_integrable hh0.le hh1 s
  have heq : averagedDensity h s - 1 =
      h⁻¹ * ∫ t in (0 : ℝ)..h, (slopeDensity t s - 1) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    unfold averagedDensity
    rw [mul_sub, inv_mul_cancel₀ hh0.ne']
  rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hh0)]
  have hb : |∫ t in (0 : ℝ)..h, (slopeDensity t s - 1)| ≤
      (h / (1 - h)) * h := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := h) (C := h / (1 - h))
      (f := fun t => slopeDensity t s - 1) (by
        intro t ht
        rw [uIoc_of_le hh0.le] at ht
        simpa only [Real.norm_eq_abs] using slopeDensity_deviation ht.1.le ht.2 hh1 s)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hh0] using this
  calc
    _ ≤ h⁻¹ * ((h / (1 - h)) * h) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh0.le)
    _ = _ := by field_simp

theorem slopeDensity_rectangle_integrable {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1) :
    IntegrableOn (Function.uncurry slopeDensity)
      (uIoc (0 : ℝ) h ×ˢ uIoc (0 : ℝ) 1) := by
  have hfinite : volume (uIoc (0 : ℝ) h ×ˢ uIoc (0 : ℝ) 1) < ⊤ := by
    apply lt_of_le_of_lt (measure_mono (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc))
    exact (isCompact_uIcc.prod isCompact_uIcc).measure_lt_top
  apply IntegrableOn.of_bound hfinite measurable_slopeDensity.aestronglyMeasurable ((1 - h)⁻¹)
  filter_upwards [ae_restrict_mem (measurableSet_uIoc.prod measurableSet_uIoc)] with p hp
  have ht := hp.1
  rw [uIoc_of_le hh0] at ht
  change ‖slopeDensity p.1 p.2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (slopeDensity_pos ht.1.le (lt_of_le_of_lt ht.2 hh1) p.2)]
  exact slopeDensity_uniform_upper ht.1.le ht.2 hh1 p.2

theorem averagedDensity_intervalIntegrable {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    IntervalIntegrable (averagedDensity h) volume 0 1 := by
  have hr := slopeDensity_rectangle_integrable hh0.le hh1
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hr
  have hi := hr.integral_prod_right.const_mul h⁻¹
  rw [intervalIntegrable_iff]
  change Integrable (fun s => h⁻¹ * ∫ t in (0 : ℝ)..h, slopeDensity t s)
    (volume.restrict (uIoc (0 : ℝ) 1))
  simpa only [intervalIntegral.integral_of_le hh0.le,
    uIoc_of_le hh0.le, Function.uncurry] using hi

theorem integral_averagedDensity {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    (∫ s in (0 : ℝ)..1, averagedDensity h s) = 1 := by
  have hr := slopeDensity_rectangle_integrable hh0.le hh1
  have hi : (∫ t in (0 : ℝ)..h, ∫ s in (0 : ℝ)..1, slopeDensity t s) = h := by
    calc
      _ = ∫ _t in (0 : ℝ)..h, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hh0.le
        intro t ht
        exact integral_slopeDensity ht.1.le (lt_trans ht.2 hh1)
      _ = _ := by simp
  unfold averagedDensity
  rw [intervalIntegral.integral_const_mul,
    ← intervalIntegral_intervalIntegral_swap hr, hi, inv_mul_cancel₀ hh0.ne']

theorem unitMass_square_identity {f : ℝ → ℝ} {δ : ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hδ : 0 ≤ δ)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, |f s - 1| ≤ δ)
    (hmass : (∫ s in (0 : ℝ)..1, f s) = 1) :
    (∫ s in (0 : ℝ)..1, (f s) ^ 2) =
      1 + ∫ s in (0 : ℝ)..1, (f s - 1) ^ 2 := by
  have hdev : IntervalIntegrable (fun s => (f s - 1) ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff]
    apply IntegrableOn.of_bound (by simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
      ((hf.def'.aestronglyMeasurable.sub aestronglyMeasurable_const).pow 2) (δ ^ 2)
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hb := hbound s ⟨hs.1.le, hs.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (f s - 1) ^ 2 ≤ δ ^ 2
    exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hδ] using hb)
  have hfun : (fun s => (f s) ^ 2) =
      (fun s => (f s - 1) ^ 2 + 2 * f s - 1) := by
    funext s
    ring
  rw [hfun, intervalIntegral.integral_sub (hdev.add (hf.const_mul 2)) intervalIntegrable_const,
    intervalIntegral.integral_add hdev (hf.const_mul 2), intervalIntegral.integral_const_mul, hmass]
  simp
  ring

theorem unitMass_square_le {f : ℝ → ℝ} {δ : ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hδ : 0 ≤ δ)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, |f s - 1| ≤ δ)
    (hmass : (∫ s in (0 : ℝ)..1, f s) = 1) :
    (∫ s in (0 : ℝ)..1, (f s) ^ 2) ≤ 1 + δ ^ 2 := by
  rw [unitMass_square_identity hf hδ hbound hmass]
  apply add_le_add le_rfl
  have hint : IntervalIntegrable (fun s => (f s - 1) ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff]
    apply IntegrableOn.of_bound (by simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
      ((hf.def'.aestronglyMeasurable.sub aestronglyMeasurable_const).pow 2) (δ ^ 2)
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hb := hbound s ⟨hs.1.le, hs.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (f s - 1) ^ 2 ≤ δ ^ 2
    exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hδ] using hb)
  calc
    _ ≤ ∫ _s in (0 : ℝ)..1, δ ^ 2 :=
      intervalIntegral.integral_mono_on (by norm_num) hint intervalIntegrable_const
        (fun s hs => by
          have hb := hbound s hs
          exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hδ] using hb))
    _ = _ := by simp

theorem averagedDensity_second_moment {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    (∫ s in (0 : ℝ)..1, (averagedDensity h s) ^ 2) ≤
      1 + h ^ 2 / (1 - h) ^ 2 := by
  have hb := unitMass_square_le (averagedDensity_intervalIntegrable hh0 hh1)
    (show 0 ≤ h / (1 - h) by positivity)
    (fun s _ => averagedDensity_deviation hh0 hh1 s)
    (integral_averagedDensity hh0 hh1)
  simpa only [div_pow] using hb

end Invariant233.ScalarEndpointDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSampling
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

lemma delta_nonneg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 0 ≤ delta s := by
  exact le_min hs.1 (sub_nonneg.mpr hs.2)

lemma delta_le_half (s : ℝ) : delta s ≤ 1 / 2 := by
  unfold delta
  rcases le_total s (1 / 2) with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

lemma cutoff_iff {α s : ℝ} : α ≤ delta s ↔ s ∈ Icc α (1 - α) := by
  simp only [delta, le_min_iff, mem_Icc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma rawKernel_nonneg {h α s t : ℝ} (hh : 0 ≤ h)
    (hs : s ∈ Icc (0 : ℝ) 1) : 0 ≤ rawKernel h α s t := by
  unfold rawKernel
  split_ifs
  · exact Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr (mul_nonneg hh (delta_nonneg hs))) _
  · exact le_rfl

lemma integral_rawKernel (h α s : ℝ) (hh : 0 < h) (hα : 0 < α) :
    (∫ t : ℝ, rawKernel h α s t) = if α ≤ delta s then 1 else 0 := by
  unfold rawKernel
  split_ifs with hs
  · have hd : 0 < h * delta s := mul_pos hh (hα.trans_le hs)
    rw [integral_indicator_const _ measurableSet_Ioo,
      Real.volume_real_Ioo_of_le hd.le]
    simp only [sub_zero, smul_eq_mul]
    exact mul_inv_cancel₀ hd.ne'
  · simp

lemma integral_sq_rawKernel (h α s : ℝ) (hh : 0 < h) (hα : 0 < α) :
    (∫ t : ℝ, rawKernel h α s t ^ 2) =
      if α ≤ delta s then (h * delta s)⁻¹ else 0 := by
  unfold rawKernel
  split_ifs with hs
  · have hd : 0 < h * delta s := mul_pos hh (hα.trans_le hs)
    have heq : (fun t : ℝ => ((Ioo 0 (h * delta s)).indicator
        (fun _ => (h * delta s)⁻¹) t)^2) =
        (Ioo 0 (h * delta s)).indicator (fun _ => ((h * delta s)⁻¹)^2) := by
      funext t
      by_cases ht : t ∈ Ioo 0 (h * delta s) <;> simp [ht]
    rw [heq, integral_indicator_const _ measurableSet_Ioo,
      Real.volume_real_Ioo_of_le hd.le]
    simp only [sub_zero, smul_eq_mul]
    field_simp
  · simp

lemma rawKernel_eq_zero_of_not_mem_unit {h α s t : ℝ}
    (_hh : 0 ≤ h) (hhone : h ≤ 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∉ Ioc (0 : ℝ) 1) : rawKernel h α s t = 0 := by
  unfold rawKernel
  split_ifs
  · apply Set.indicator_of_notMem
    intro ht'
    apply ht
    refine ⟨ht'.1, ht'.2.le.trans ?_⟩
    calc
      h * delta s ≤ 1 * delta s := mul_le_mul_of_nonneg_right hhone (delta_nonneg hs)
      _ ≤ 1 := by nlinarith [delta_le_half s]
  · rfl

theorem interval_integral_rawKernel {h α s : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, rawKernel h α s t) =
      if α ≤ delta s then 1 else 0 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht => rawKernel_eq_zero_of_not_mem_unit hh.le hhone hs ht)]
  exact integral_rawKernel h α s hh hα

theorem interval_integral_sq_rawKernel {h α s : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, rawKernel h α s t ^ 2) =
      if α ≤ delta s then (h * delta s)⁻¹ else 0 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht => by rw [rawKernel_eq_zero_of_not_mem_unit hh.le hhone hs ht]; norm_num)]
  exact integral_sq_rawKernel h α s hh hα

theorem integral_integral_rawKernel {h α : ℝ} (hh : 0 < h)
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ s in Icc (0 : ℝ) 1, ∫ t : ℝ, rawKernel h α s t) = 1 - 2 * α := by
  have heq : (fun s : ℝ => ∫ t : ℝ, rawKernel h α s t) =
      (Icc α (1 - α)).indicator (fun _ => (1 : ℝ)) := by
    funext s
    rw [integral_rawKernel h α s hh hα]
    simp only [cutoff_iff, Set.indicator_apply]
  rw [heq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_indicator_const _ measurableSet_Icc,
      Real.volume_real_Icc_of_le (by linarith : α ≤ 1 - α)]
    simp only [smul_eq_mul, mul_one]
    ring
  · intro s hs
    apply Set.indicator_of_notMem
    intro hs'
    apply hs
    exact ⟨hα.le.trans hs'.1, hs'.2.trans (by linarith)⟩

theorem integral_inv_delta {α : ℝ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ s in α..(1 - α), (delta s)⁻¹) =
      2 * Real.log (1 / (2 * α)) := by
  have hab : α ≤ 1 - α := by linarith
  have hmid : (1 / 2 : ℝ) ≤ 1 - α := by linarith
  have hd : Continuous (fun s : ℝ => delta s) :=
    continuous_id.min (continuous_const.sub continuous_id)
  have hfi : IntervalIntegrable (fun s : ℝ => (delta s)⁻¹) volume α (1 - α) := by
    apply intervalIntegral.intervalIntegrable_inv _ hd.continuousOn
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact ne_of_gt (hα.trans_le (cutoff_iff.mpr hs))
  have hleft := hfi.mono_set (show uIcc α (1 / 2 : ℝ) ⊆ uIcc α (1 - α) by
    rw [uIcc_of_le hαhalf, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hmid)
  have hright := hfi.mono_set (show uIcc (1 / 2 : ℝ) (1 - α) ⊆ uIcc α (1 - α) by
    rw [uIcc_of_le hmid, uIcc_of_le hab]
    exact Icc_subset_Icc hαhalf le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  have hleftEq : (∫ s in α..(1 / 2 : ℝ), (delta s)⁻¹) =
      ∫ s in α..(1 / 2 : ℝ), s⁻¹ := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hαhalf] at hs
    change (min s (1 - s))⁻¹ = s⁻¹
    rw [min_eq_left (by linarith [hs.2] : s ≤ 1 - s)]
  have hrightEq : (∫ s in (1 / 2 : ℝ)..(1 - α), (delta s)⁻¹) =
      ∫ s in α..(1 / 2 : ℝ), s⁻¹ := by
    calc
      (∫ s in (1 / 2 : ℝ)..(1 - α), (delta s)⁻¹) =
          ∫ s in (1 / 2 : ℝ)..(1 - α), (1 - s)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hmid] at hs
        change (min s (1 - s))⁻¹ = (1 - s)⁻¹
        rw [min_eq_right (by linarith [hs.1] : 1 - s ≤ s)]
      _ = ∫ s in α..(1 / 2 : ℝ), s⁻¹ := by
        rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ => s⁻¹) 1]
        congr 1 <;> ring
  rw [hleftEq, hrightEq, integral_inv_of_pos hα (by norm_num : (0 : ℝ) < 1 / 2)]
  have heq : (1 / 2 : ℝ) / α = 1 / (2 * α) := by ring
  rw [heq]
  ring

theorem integral_integral_sq_rawKernel {h α : ℝ} (hh : 0 < h)
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ s in Icc (0 : ℝ) 1, ∫ t : ℝ, rawKernel h α s t ^ 2) =
      (2 / h) * Real.log (1 / (2 * α)) := by
  have heq : (fun s : ℝ => ∫ t : ℝ, rawKernel h α s t ^ 2) =
      (Icc α (1 - α)).indicator (fun s => (h * delta s)⁻¹) := by
    funext s
    rw [integral_sq_rawKernel h α s hh hα]
    simp only [cutoff_iff, Set.indicator_apply]
  rw [heq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : α ≤ 1 - α)]
    simp_rw [mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_delta hα hαhalf]
    ring
  · intro s hs
    apply Set.indicator_of_notMem
    intro hs'
    apply hs
    exact ⟨hα.le.trans hs'.1, hs'.2.trans (by linarith)⟩

theorem double_interval_integral_rawKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, rawKernel h α s t) = 1 - 2 * α := by
  calc
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, rawKernel h α s t) =
        ∫ s in Icc (0 : ℝ) 1, ∫ t : ℝ, rawKernel h α s t := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only
      rw [interval_integral_rawKernel hh hhone hα hs, integral_rawKernel h α s hh hα]
    _ = 1 - 2 * α := integral_integral_rawKernel hh hα hαhalf

theorem double_interval_integral_sq_rawKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, rawKernel h α s t ^ 2) =
      (2 / h) * Real.log (1 / (2 * α)) := by
  calc
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, rawKernel h α s t ^ 2) =
        ∫ s in Icc (0 : ℝ) 1, ∫ t : ℝ, rawKernel h α s t ^ 2 := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only
      rw [interval_integral_sq_rawKernel hh hhone hα hs,
        integral_sq_rawKernel h α s hh hα]
    _ = (2 / h) * Real.log (1 / (2 * α)) := integral_integral_sq_rawKernel hh hα hαhalf

theorem interval_integral_circleKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (z : ℝ) :
    (∫ v in (0 : ℝ)..1, circleKernel h α z v) =
      if α ≤ delta (Int.fract z) then 1 else 0 := by
  calc
    (∫ v in (0 : ℝ)..1, circleKernel h α z v) =
        ∫ v in (0 : ℝ)..1, rawKernel h α (Int.fract z) v := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro v hv
      simp only [circleKernel, Int.fract_eq_self.mpr ⟨hv.1.le, hv.2⟩]
    _ = if α ≤ delta (Int.fract z) then 1 else 0 :=
      interval_integral_rawKernel hh hhone hα
        ⟨Int.fract_nonneg z, (Int.fract_lt_one z).le⟩

theorem double_interval_integral_circleKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α z v) = 1 - 2 * α := by
  calc
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α z v) =
        ∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, rawKernel h α z v := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro z hz
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro v hv
      simp only [circleKernel, Int.fract_eq_self.mpr ⟨hz.1.le, hz.2⟩,
        Int.fract_eq_self.mpr ⟨hv.1.le, hv.2⟩]
    _ = 1 - 2 * α := double_interval_integral_rawKernel hh hhone hα hαhalf

theorem double_interval_integral_sq_circleKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α z v ^ 2) =
      (2 / h) * Real.log (1 / (2 * α)) := by
  calc
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α z v ^ 2) =
        ∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, rawKernel h α z v ^ 2 := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro z hz
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro v hv
      simp only [circleKernel, Int.fract_eq_self.mpr ⟨hz.1.le, hz.2⟩,
        Int.fract_eq_self.mpr ⟨hv.1.le, hv.2⟩]
    _ = (2 / h) * Real.log (1 / (2 * α)) :=
      double_interval_integral_sq_rawKernel hh hhone hα hαhalf

theorem averaged_circleKernel_bounds {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (z : ℝ) :
    0 ≤ (∫ v in (0 : ℝ)..1, circleKernel h α z v) ∧
      (∫ v in (0 : ℝ)..1, circleKernel h α z v) ≤ 1 := by
  rw [interval_integral_circleKernel hh hhone hα z]
  split_ifs <;> norm_num

theorem integral_sq_averaged_circleKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ z in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, circleKernel h α z v)^2) =
      1 - 2 * α := by
  calc
    (∫ z in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, circleKernel h α z v)^2) =
        ∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α z v := by
      apply intervalIntegral.integral_congr
      intro z _
      dsimp only
      rw [interval_integral_circleKernel hh hhone hα z]
      split_ifs <;> norm_num
    _ = 1 - 2 * α := double_interval_integral_circleKernel hh hhone hα hαhalf

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

theorem manuscriptKernel_mass {m : ℕ} (hm : 200 ≤ m) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, manuscriptKernel m z v) =
      1 - 2 / (m : ℝ)^2 := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  simpa only [manuscriptKernel, mul_one_div] using
    double_interval_integral_circleKernel hh hhone hα hαhalf

theorem manuscriptKernel_secondMoment {m : ℕ} (hm : 200 ≤ m) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, manuscriptKernel m z v ^ 2) =
      (2 / (m : ℝ) ^ (-(3 / 5 : ℝ))) * Real.log ((m : ℝ)^2 / 2) := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have heq : 1 / (2 * (1 / (m : ℝ)^2)) = (m : ℝ)^2 / 2 := by
    field_simp [hmR.ne']
  simpa only [manuscriptKernel, heq] using
    double_interval_integral_sq_circleKernel hh hhone hα hαhalf

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_EndpointKernelGeometry
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem rawKernel_uncut_zero_of_nonpos {h x v : ℝ} (hh : 0 ≤ h)
    (hx : x ≤ 0) (_hv : 0 ≤ v) : rawKernel h 0 x v = 0 := by
  unfold rawKernel
  split_ifs with hd
  · apply Set.indicator_of_notMem
    intro hmem
    have hdelta : delta x ≤ 0 := (min_le_left _ _).trans hx
    have : h * delta x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hh hdelta
    linarith [hmem.1, hmem.2]
  · rfl

theorem uncut_endpoint_no_wrap {h s v : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hs0 : 0 < s) (hs1 : s < 1) (hv0 : 0 < v) (hv1 : v < 1) :
    circleKernel h 0 (s - v) v = rawKernel h 0 (s - v) v := by
  unfold circleKernel
  rw [Int.fract_eq_self.mpr ⟨hv0.le, hv1⟩]
  by_cases hvs : v ≤ s
  · rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  · have hsv : s < v := lt_of_not_ge hvs
    rw [rawKernel_uncut_zero_of_nonpos (x := s - v) hh0 (by linarith) hv0.le]
    have hfloor : ⌊s - v⌋ = -1 := by
      apply Int.floor_eq_iff.mpr
      norm_num
      constructor <;> linarith
    have hfract : Int.fract (s - v) = s - v + 1 := by
      rw [Int.fract, hfloor]
      norm_num
    rw [hfract]
    unfold rawKernel
    split_ifs
    · apply Set.indicator_of_notMem
      intro hmem
      have hdelta0 : 0 ≤ delta (s - v + 1) := by
        apply delta_nonneg
        constructor <;> linarith
      have hdelta : delta (s - v + 1) ≤ v - s := by
        unfold delta
        exact (min_le_right _ _).trans (by linarith)
      have hmul : h * delta (s - v + 1) ≤ delta (s - v + 1) :=
        (mul_le_mul_of_nonneg_right hh1 hdelta0).trans_eq (one_mul _)
      linarith [hmem.2]
    · rfl

theorem rawKernel_le_uncut {h α s v : ℝ} (hh : 0 ≤ h)
    (hs : s ∈ Icc (0 : ℝ) 1) : rawKernel h α s v ≤ rawKernel h 0 s v := by
  have hd : 0 ≤ delta s := delta_nonneg hs
  unfold rawKernel
  rw [ite_eq_left hd]
  split_ifs
  · exact le_rfl
  · exact Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr (mul_nonneg hh hd)) _

theorem uncut_endpoint_left_formula {h s : ℝ} (hh0 : 0 < h)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) (v : ℝ) :
    rawKernel h 0 (s - v) v =
      (Ioo 0 (h * s / (1 + h))).indicator (fun v => (h * (s - v))⁻¹) v := by
  have hp : 0 < 1 + h := by linarith
  have heq : v < h * (s - v) ↔ v < h * s / (1 + h) := by
    rw [lt_div_iff₀ hp]
    constructor <;> intro hineq <;> nlinarith
  by_cases hv : 0 < v
  · have hd : delta (s - v) = s - v := by
      unfold delta
      rw [min_eq_left (by linarith)]
    unfold rawKernel
    rw [hd]
    by_cases hvs : v < h * s / (1 + h)
    · have hvbound : v < s := by
        have := heq.mpr hvs
        nlinarith
      simp only [ite_eq_left (show 0 ≤ s - v by linarith), Set.indicator_apply, mem_Ioo,
        hv, heq.mpr hvs, hvs, and_self, ite_true, if_true]
    · have hvnot : ¬ v < h * (s - v) := fun h => hvs (heq.mp h)
      simp only [Set.indicator_apply, mem_Ioo, hv, hvnot, hvs, and_false, ite_false, if_false,
        ite_self]
  · unfold rawKernel
    simp only [Set.indicator_apply, mem_Ioo, hv, false_and, ite_false, if_false, ite_self]

theorem integral_uncut_endpoint_left {h s : ℝ} (hh0 : 0 < h)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) :
    (∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v) = h⁻¹ * Real.log (1 + h) := by
  have hp : 0 < 1 + h := by linarith
  have hL0 : 0 < h * s / (1 + h) := div_pos (mul_pos hh0 hs0) hp
  have hLs : h * s / (1 + h) < s := by
    rw [div_lt_iff₀ hp]
    nlinarith
  have hL1 : h * s / (1 + h) < 1 := by linarith
  have hfun : (fun v => rawKernel h 0 (s - v) v) =
      (Ioo 0 (h * s / (1 + h))).indicator (fun v => (h * (s - v))⁻¹) := by
    funext v
    exact uncut_endpoint_left_formula hh0 hs0 hs1 v
  rw [hfun, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hL0.le]
    simp_rw [mul_inv]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun z : ℝ => z⁻¹) s]
    simp only [sub_zero]
    rw [integral_inv_of_pos (by linarith : 0 < s - h * s / (1 + h)) hs0]
    have hratio : s / (s - h * s / (1 + h)) = 1 + h := by
      field_simp
      ring
    rw [hratio]
  · intro v hv
    apply Set.indicator_of_notMem
    intro hmem
    exact hv ⟨hmem.1, hmem.2.le.trans hL1.le⟩

theorem averagedDensity_left_formula {h s : ℝ} (hh0 : 0 < h) (hs1 : s ≤ 1 / 2) :
    ScalarEndpointDensity.averagedDensity h s = h⁻¹ * Real.log (1 + h) := by
  have hp : 0 < 1 + h := by linarith
  unfold ScalarEndpointDensity.averagedDensity
  congr 1
  calc
    _ = ∫ t in (0 : ℝ)..h, (1 + t)⁻¹ := by
      apply intervalIntegral.integral_congr_Ioo_of_le hh0.le
      intro t ht
      simp only [ScalarEndpointDensity.slopeDensity,
        ite_eq_left (show s ≤ ScalarEndpointDensity.midpoint t by
          unfold ScalarEndpointDensity.midpoint
          linarith [ht.1])]
    _ = Real.log (1 + h) := by
      rw [intervalIntegral.integral_comp_add_left (fun t : ℝ => t⁻¹) 1]
      simp only [add_zero]
      rw [integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) hp]
      simp

theorem integral_uncut_circleEndpoint_left {h s : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) :
    (∫ v in (0 : ℝ)..1, circleKernel h 0 (s - v) v) =
      ScalarEndpointDensity.averagedDensity h s := by
  rw [averagedDensity_left_formula hh0 hs1]
  calc
    _ = ∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro v hv
      exact uncut_endpoint_no_wrap hh0.le hh1 hs0 (by linarith) hv.1 hv.2
    _ = _ := integral_uncut_endpoint_left hh0 hs0 hs1

theorem uncut_endpoint_right_formula {h s : ℝ} (hh0 : 0 < h) (_hh1 : h < 1)
    (hs0 : (1 + h) / 2 ≤ s) (hs1 : s < 1) (v : ℝ) :
    rawKernel h 0 (s - v) v =
      (Ioo 0 (h * (1 - s) / (1 - h))).indicator
        (fun v => (h * (1 - s + v))⁻¹) v := by
  have hp : 0 < 1 + h := by linarith
  have hn : 0 < 1 - h := by linarith
  have hR : h * (1 - s) / (1 - h) ≤ s - 1 / 2 := by
    rw [div_le_iff₀ hn]
    nlinarith
  have hL : h * s / (1 + h) ≤ s - 1 / 2 := by
    rw [div_le_iff₀ hp]
    nlinarith
  have heqR : v < h * (1 - s + v) ↔ v < h * (1 - s) / (1 - h) := by
    rw [lt_div_iff₀ hn]
    constructor <;> intro hh <;> nlinarith
  have heqL : v < h * (s - v) ↔ v < h * s / (1 + h) := by
    rw [lt_div_iff₀ hp]
    constructor <;> intro hh <;> nlinarith
  by_cases hv : 0 < v
  · by_cases hvb : v ≤ s - 1 / 2
    · have hd : delta (s - v) = 1 - s + v := by
        unfold delta
        rw [min_eq_right (by linarith)]
        ring
      unfold rawKernel
      rw [hd, ite_eq_left (by linarith)]
      simp only [Set.indicator_apply, mem_Ioo, heqR]
    · have hd : delta (s - v) = s - v := by
        unfold delta
        rw [min_eq_left (by linarith)]
      have hvR : ¬v < h * (1 - s) / (1 - h) := by linarith
      have hvL : ¬v < h * (s - v) := by
        rw [heqL]
        linarith
      unfold rawKernel
      rw [hd]
      simp only [Set.indicator_apply, mem_Ioo, hvR, hvL, and_false, ite_false, if_false, ite_self]
  · unfold rawKernel
    simp only [Set.indicator_apply, mem_Ioo, hv, false_and, ite_false, if_false, ite_self]

theorem integral_uncut_endpoint_right {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : (1 + h) / 2 ≤ s) (hs1 : s < 1) :
    (∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v) =
      h⁻¹ * Real.log ((1 - h)⁻¹) := by
  have hn : 0 < 1 - h := by linarith
  have hR0 : 0 < h * (1 - s) / (1 - h) := div_pos (mul_pos hh0 (by linarith)) hn
  have hR1 : h * (1 - s) / (1 - h) < 1 := by
    rw [div_lt_iff₀ hn]
    nlinarith
  have hfun : (fun v => rawKernel h 0 (s - v) v) =
      (Ioo 0 (h * (1 - s) / (1 - h))).indicator
        (fun v => (h * (1 - s + v))⁻¹) := by
    funext v
    exact uncut_endpoint_right_formula hh0 hh1 hs0 hs1 v
  rw [hfun, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hR0.le]
    simp_rw [mul_inv]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_left (fun z : ℝ => z⁻¹) (1 - s)]
    simp only [add_zero]
    rw [integral_inv_of_pos (by linarith : 0 < 1 - s)
      (by linarith : 0 < 1 - s + h * (1 - s) / (1 - h))]
    have hratio : (1 - s + h * (1 - s) / (1 - h)) / (1 - s) = (1 - h)⁻¹ := by
      field_simp [ne_of_gt (show 0 < 1 - s by linarith), hn.ne']
      ring
    rw [hratio]
  · intro v hv
    apply Set.indicator_of_notMem
    intro hmem
    exact hv ⟨hmem.1, hmem.2.le.trans hR1.le⟩

theorem averagedDensity_right_formula {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : (1 + h) / 2 ≤ s) :
    ScalarEndpointDensity.averagedDensity h s = h⁻¹ * Real.log ((1 - h)⁻¹) := by
  unfold ScalarEndpointDensity.averagedDensity
  congr 1
  calc
    _ = ∫ t in (0 : ℝ)..h, (1 - t)⁻¹ := by
      apply intervalIntegral.integral_congr_Ioo_of_le hh0.le
      intro t ht
      simp only [ScalarEndpointDensity.slopeDensity,
        ite_eq_right (show ¬s ≤ ScalarEndpointDensity.midpoint t by
          unfold ScalarEndpointDensity.midpoint
          linarith [ht.2])]
    _ = Real.log ((1 - h)⁻¹) := by
      rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹) 1]
      simp only [sub_zero]
      rw [integral_inv_of_pos (by linarith : 0 < 1 - h) (by norm_num : (0 : ℝ) < 1)]
      simp only [one_div]

theorem integral_uncut_circleEndpoint_right {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : (1 + h) / 2 ≤ s) (hs1 : s < 1) :
    (∫ v in (0 : ℝ)..1, circleKernel h 0 (s - v) v) =
      ScalarEndpointDensity.averagedDensity h s := by
  rw [averagedDensity_right_formula hh0 hh1 hs0]
  calc
    _ = ∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro v hv
      exact uncut_endpoint_no_wrap hh0.le hh1.le (by linarith) hs1 hv.1 hv.2
    _ = _ := integral_uncut_endpoint_right hh0 hh1 hs0 hs1

theorem uncut_endpoint_middle_formula {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : 1 / 2 < s) (hs1 : s < (1 + h) / 2) (v : ℝ) :
    rawKernel h 0 (s - v) v =
      (Ioc 0 (s - 1 / 2)).indicator (fun v => (h * (1 - s + v))⁻¹) v +
      (Ioo (s - 1 / 2) (h * s / (1 + h))).indicator
        (fun v => (h * (s - v))⁻¹) v := by
  have hp : 0 < 1 + h := by linarith
  have hn : 0 < 1 - h := by linarith
  have hsunit : s < 1 := by linarith
  have hR : s - 1 / 2 < h * (1 - s) / (1 - h) := by
    rw [lt_div_iff₀ hn]
    nlinarith
  have heqR : v < h * (1 - s + v) ↔ v < h * (1 - s) / (1 - h) := by
    rw [lt_div_iff₀ hn]
    constructor <;> intro hh <;> nlinarith
  have heqL : v < h * (s - v) ↔ v < h * s / (1 + h) := by
    rw [lt_div_iff₀ hp]
    constructor <;> intro hh <;> nlinarith
  by_cases hv : 0 < v
  · by_cases hvb : v ≤ s - 1 / 2
    · have hd : delta (s - v) = 1 - s + v := by
        unfold delta
        rw [min_eq_right (by linarith)]
        ring
      have hvR : v < h * (1 - s + v) := heqR.mpr (lt_of_le_of_lt hvb hR)
      have hvnot : ¬ s - 1 / 2 < v := not_lt_of_ge hvb
      unfold rawKernel
      rw [hd, ite_eq_left (by linarith)]
      simp only [Set.indicator_apply, mem_Ioc, mem_Ioo, hv, hvb, hvR, hvnot,
        and_self, false_and, ite_true, if_true, ite_false, if_false, add_zero]
    · have hvb' : s - 1 / 2 < v := lt_of_not_ge hvb
      have hd : delta (s - v) = s - v := by
        unfold delta
        rw [min_eq_left (by linarith)]
      unfold rawKernel
      rw [hd]
      by_cases hvL : v < h * s / (1 + h)
      · have hvs : v < s := by
          have := heqL.mpr hvL
          nlinarith
        simp only [ite_eq_left (show 0 ≤ s - v by linarith), Set.indicator_apply,
          mem_Ioc, mem_Ioo, hv, hvb, hvb', hvL, heqL.mpr hvL,
          and_self, and_false, ite_true, if_true, ite_false, if_false, zero_add]
      · have hvnot : ¬v < h * (s - v) := fun hh => hvL (heqL.mp hh)
        simp only [Set.indicator_apply, mem_Ioc, mem_Ioo, hv, hvb, hvL, hvnot,
          and_false, ite_false, if_false, ite_self, add_zero]
  · have hvb : ¬s - 1 / 2 < v := by linarith
    unfold rawKernel
    simp only [Set.indicator_apply, mem_Ioc, mem_Ioo, hv, hvb,
      false_and, ite_false, if_false, ite_self, add_zero]

theorem integral_uncut_endpoint_middle {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : 1 / 2 < s) (hs1 : s < (1 + h) / 2) :
    (∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v) =
      h⁻¹ * Real.log ((1 + h) / (4 * s * (1 - s))) := by
  have hp : 0 < 1 + h := by linarith
  have hspos : 0 < s := by linarith
  have hsunit : s < 1 := by linarith
  have hB0 : 0 < s - 1 / 2 := by linarith
  have hL : s - 1 / 2 < h * s / (1 + h) := by
    rw [lt_div_iff₀ hp]
    nlinarith
  have hLs : h * s / (1 + h) < s := by
    rw [div_lt_iff₀ hp]
    nlinarith
  have hB1 : s - 1 / 2 < 1 := by linarith
  have hL1 : h * s / (1 + h) < 1 := by linarith
  let fR : ℝ → ℝ := (Ioc 0 (s - 1 / 2)).indicator (fun v => (h * (1 - s + v))⁻¹)
  let fL : ℝ → ℝ := (Ioo (s - 1 / 2) (h * s / (1 + h))).indicator
    (fun v => (h * (s - v))⁻¹)
  have hfR : Integrable fR := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
    apply IntegrableOn.mono_set _ Ioc_subset_Icc_self
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.inv₀ (by fun_prop)
    intro v hv
    exact ne_of_gt (mul_pos hh0 (by linarith [hv.1]))
  have hfL : Integrable fL := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioo
    apply IntegrableOn.mono_set _ Ioo_subset_Icc_self
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.inv₀ (by fun_prop)
    intro v hv
    exact ne_of_gt (mul_pos hh0 (by linarith [hv.2]))
  have hfun : (fun v => rawKernel h 0 (s - v) v) = fun v => fR v + fL v := by
    funext v
    exact uncut_endpoint_middle_formula hh0 hh1 hs0 hs1 v
  have hRint : (∫ v, fR v) = h⁻¹ * Real.log ((1 / 2) / (1 - s)) := by
    dsimp only [fR]
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hB0.le]
    simp_rw [mul_inv]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_left (fun z : ℝ => z⁻¹) (1 - s)]
    have hb : 1 - s + (s - 1 / 2) = (1 / 2 : ℝ) := by ring
    rw [hb]
    simp only [add_zero]
    rw [integral_inv_of_pos (by linarith : 0 < 1 - s) (by norm_num : (0 : ℝ) < 1 / 2)]
  have hLint : (∫ v, fL v) = h⁻¹ * Real.log ((1 / 2) / (s - h * s / (1 + h))) := by
    dsimp only [fL]
    rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hL.le]
    simp_rw [mul_inv]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun z : ℝ => z⁻¹) s]
    have hb : s - (s - 1 / 2) = (1 / 2 : ℝ) := by ring
    rw [hb, integral_inv_of_pos (by linarith : 0 < s - h * s / (1 + h))
      (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [hfun, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_add hfR hfL, hRint, hLint, ← mul_add,
      ← Real.log_mul (by positivity) (by positivity)]
    congr 2
    field_simp [ne_of_gt (show 0 < 1 - s by linarith), hspos.ne', hp.ne']
    ring
  · intro v hv
    have hnotR : v ∉ Ioc 0 (s - 1 / 2) :=
      fun ht => hv ⟨ht.1, ht.2.trans hB1.le⟩
    have hnotL : v ∉ Ioo (s - 1 / 2) (h * s / (1 + h)) :=
      fun ht => hv ⟨lt_trans hB0 ht.1, ht.2.le.trans hL1.le⟩
    simp only [fR, fL, Set.indicator_of_notMem hnotR, Set.indicator_of_notMem hnotL, add_zero]

theorem averagedDensity_middle_formula {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : 1 / 2 < s) (hs1 : s < (1 + h) / 2) :
    ScalarEndpointDensity.averagedDensity h s =
      h⁻¹ * Real.log ((1 + h) / (4 * s * (1 - s))) := by
  have hp : 0 < 1 + h := by linarith
  have hspos : 0 < s := by linarith
  have hsunit : s < 1 := by linarith
  have hC0 : 0 < 2 * s - 1 := by linarith
  have hCh : 2 * s - 1 < h := by linarith
  have hC1 : 2 * s - 1 < 1 := by linarith
  have hd := ScalarEndpointDensity.slopeDensity_parameter_integrable hh0.le hh1 s
  have hdl : IntervalIntegrable (fun t => ScalarEndpointDensity.slopeDensity t s)
      volume 0 (2 * s - 1) := hd.mono_set (by
    rw [uIcc_of_le hC0.le, uIcc_of_le hh0.le]
    exact Icc_subset_Icc le_rfl hCh.le)
  have hdr : IntervalIntegrable (fun t => ScalarEndpointDensity.slopeDensity t s)
      volume (2 * s - 1) h := hd.mono_set (by
    rw [uIcc_of_le hCh.le, uIcc_of_le hh0.le]
    exact Icc_subset_Icc hC0.le le_rfl)
  have hleft : (∫ t in (0 : ℝ)..(2 * s - 1), ScalarEndpointDensity.slopeDensity t s) =
      Real.log (1 / (1 - (2 * s - 1))) := by
    calc
      _ = ∫ t in (0 : ℝ)..(2 * s - 1), (1 - t)⁻¹ := by
        apply intervalIntegral.integral_congr_Ioo_of_le hC0.le
        intro t ht
        simp only [ScalarEndpointDensity.slopeDensity,
          ite_eq_right (show ¬s ≤ ScalarEndpointDensity.midpoint t by
            unfold ScalarEndpointDensity.midpoint
            linarith [ht.2])]
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹) 1]
        simp only [sub_zero]
        rw [integral_inv_of_pos (by linarith : 0 < 1 - (2 * s - 1))
          (by norm_num : (0 : ℝ) < 1)]
  have hright : (∫ t in (2 * s - 1)..h, ScalarEndpointDensity.slopeDensity t s) =
      Real.log ((1 + h) / (1 + (2 * s - 1))) := by
    calc
      _ = ∫ t in (2 * s - 1)..h, (1 + t)⁻¹ := by
        apply intervalIntegral.integral_congr_Ioo_of_le hCh.le
        intro t ht
        simp only [ScalarEndpointDensity.slopeDensity,
          ite_eq_left (show s ≤ ScalarEndpointDensity.midpoint t by
            unfold ScalarEndpointDensity.midpoint
            linarith [ht.1])]
      _ = _ := by
        rw [intervalIntegral.integral_comp_add_left (fun t : ℝ => t⁻¹) 1]
        rw [integral_inv_of_pos (by linarith : 0 < 1 + (2 * s - 1)) hp]
  unfold ScalarEndpointDensity.averagedDensity
  rw [← intervalIntegral.integral_add_adjacent_intervals hdl hdr, hleft, hright,
    ← Real.log_mul (by positivity) (by positivity)]
  congr 2
  field_simp [hspos.ne', ne_of_gt (show 0 < 1 - s by linarith),
    ne_of_gt (show 0 < 1 - (2 * s - 1) by linarith),
    ne_of_gt (show 0 < 1 + (2 * s - 1) by linarith),
    show (2 : ℝ) - s * 2 ≠ 0 by linarith]
  ring

theorem integral_uncut_circleEndpoint_middle {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : 1 / 2 < s) (hs1 : s < (1 + h) / 2) :
    (∫ v in (0 : ℝ)..1, circleKernel h 0 (s - v) v) =
      ScalarEndpointDensity.averagedDensity h s := by
  rw [averagedDensity_middle_formula hh0 hh1 hs0 hs1]
  calc
    _ = ∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro v hv
      exact uncut_endpoint_no_wrap hh0.le hh1.le (by linarith) (by linarith) hv.1 hv.2
    _ = _ := integral_uncut_endpoint_middle hh0 hh1 hs0 hs1

theorem integral_uncut_circleEndpoint {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : 0 < s) (hs1 : s < 1) :
    (∫ v in (0 : ℝ)..1, circleKernel h 0 (s - v) v) =
      ScalarEndpointDensity.averagedDensity h s := by
  by_cases hleft : s ≤ 1 / 2
  · exact integral_uncut_circleEndpoint_left hh0 hh1.le hs0 hleft
  · by_cases hright : (1 + h) / 2 ≤ s
    · exact integral_uncut_circleEndpoint_right hh0 hh1 hright hs1
    · exact integral_uncut_circleEndpoint_middle hh0 hh1 (lt_of_not_ge hleft) (lt_of_not_ge hright)

end Invariant233.ScalarSampling

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
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem measurable_rawKernel_pair (h α : ℝ) :
    Measurable (fun p : ℝ × ℝ => rawKernel h α p.1 p.2) := by
  have hd : Measurable (fun p : ℝ × ℝ => delta p.1) :=
    (continuous_fst.min (continuous_const.sub continuous_fst)).measurable
  unfold rawKernel
  simp only [Set.indicator_apply, mem_Ioo]
  apply Measurable.ite (measurableSet_le measurable_const hd)
  · apply Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_const.mul hd)))
    · exact (measurable_const.mul hd).inv
    · exact measurable_const
  · exact measurable_const

theorem measurable_circleEndpoint_pair (h α : ℝ) :
    Measurable (fun p : ℝ × ℝ => circleKernel h α (p.1 - p.2) p.2) := by
  exact (measurable_rawKernel_pair h α).comp
    (((measurable_fst.sub measurable_snd).fract).prodMk measurable_snd.fract)

theorem rawKernel_height {h α s v : ℝ} (hh : 0 < h) (hα : 0 < α) :
    0 ≤ rawKernel h α s v ∧ rawKernel h α s v ≤ (h * α)⁻¹ := by
  unfold rawKernel
  split_ifs with hd
  · by_cases hv : v ∈ Ioo 0 (h * delta s)
    · rw [Set.indicator_of_mem hv]
      have hp : 0 < h * delta s := mul_pos hh (hα.trans_le hd)
      exact ⟨(inv_pos.mpr hp).le, inv_anti₀ (mul_pos hh hα)
        (mul_le_mul_of_nonneg_left hd hh.le)⟩
    · rw [Set.indicator_of_notMem hv]
      exact ⟨le_rfl, (inv_pos.mpr (mul_pos hh hα)).le⟩
  · exact ⟨le_rfl, (inv_pos.mpr (mul_pos hh hα)).le⟩

theorem circleEndpoint_intervalIntegrable {h α : ℝ} (hh : 0 < h) (hα : 0 < α)
    (s : ℝ) : IntervalIntegrable (fun v => circleKernel h α (s - v) v) volume 0 1 := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound (by rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
    ((measurable_circleEndpoint_pair h α).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable ((h * α)⁻¹)
  apply Filter.Eventually.of_forall
  intro v
  change ‖circleKernel h α (s - v) v‖ ≤ _
  unfold circleKernel
  rw [Real.norm_eq_abs, abs_of_nonneg (rawKernel_height hh hα).1]
  exact (rawKernel_height hh hα).2

theorem delta_backward_bound {s v : ℝ} (hv : 0 ≤ v) : delta s ≤ delta (s - v) + v := by
  have heq : delta (s - v) + v = min s (1 - s + 2 * v) := by
    unfold delta
    rw [← min_add_add_right]
    congr 1 <;> ring
  rw [heq]
  exact min_le_min le_rfl (by linarith)

theorem uncut_rawEndpoint_height {h s v : ℝ} (hh : 0 < h)
    (hs0 : 0 < s) (hs1 : s < 1) (hv : 0 ≤ v) :
    0 ≤ rawKernel h 0 (s - v) v ∧
      rawKernel h 0 (s - v) v ≤ (1 + h) / (h * delta s) := by
  have hdS : 0 < delta s := lt_min hs0 (by linarith)
  have hC : 0 ≤ (1 + h) / (h * delta s) := by positivity
  unfold rawKernel
  split_ifs with hd
  · by_cases hmem : v ∈ Ioo 0 (h * delta (s - v))
    · rw [Set.indicator_of_mem hmem]
      have hdpos : 0 < delta (s - v) := by
        have hp : 0 < h * delta (s - v) := lt_trans hmem.1 hmem.2
        exact (mul_pos_iff_of_pos_left hh).mp hp
      refine ⟨(inv_pos.mpr (mul_pos hh hdpos)).le, ?_⟩
      have hcomp : delta s ≤ (1 + h) * delta (s - v) := by
        have := delta_backward_bound (s := s) hv
        linarith [hmem.2]
      rw [inv_eq_one_div, div_le_div_iff₀ (mul_pos hh hdpos) (mul_pos hh hdS)]
      nlinarith [mul_le_mul_of_nonneg_left hcomp hh.le]
    · rw [Set.indicator_of_notMem hmem]
      exact ⟨le_rfl, hC⟩
  · exact ⟨le_rfl, hC⟩

theorem uncut_rawEndpoint_intervalIntegrable {h s : ℝ} (hh : 0 < h)
    (hs0 : 0 < s) (hs1 : s < 1) :
    IntervalIntegrable (fun v => rawKernel h 0 (s - v) v) volume 0 1 := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound (by rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
    ((measurable_rawKernel_pair h 0).comp
      ((measurable_const.sub measurable_id).prodMk measurable_id)).aestronglyMeasurable
    ((1 + h) / (h * delta s))
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
  change ‖rawKernel h 0 (s - v) v‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (uncut_rawEndpoint_height hh hs0 hs1 hv.1.le).1]
  exact (uncut_rawEndpoint_height hh hs0 hs1 hv.1.le).2

theorem uncut_circleEndpoint_intervalIntegrable {h s : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hs0 : 0 < s) (hs1 : s < 1) :
    IntervalIntegrable (fun v => circleKernel h 0 (s - v) v) volume 0 1 := by
  apply (uncut_rawEndpoint_intervalIntegrable hh hs0 hs1).congr_uIoo
  intro v hv
  rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
  exact (uncut_endpoint_no_wrap hh.le hh1 hs0 hs1 hv.1 hv.2).symm

theorem circleEndpoint_average_le_density {h α s : ℝ}
    (hh0 : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hs0 : 0 < s) (hs1 : s < 1) :
    0 ≤ (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ∧
      (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ≤
        ScalarEndpointDensity.averagedDensity h s := by
  constructor
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro v _
    exact (rawKernel_height hh0 hα).1
  · rw [← integral_uncut_circleEndpoint hh0 hh1 hs0 hs1]
    apply intervalIntegral.integral_mono_on (by norm_num)
      (circleEndpoint_intervalIntegrable hh0 hα s)
      (uncut_circleEndpoint_intervalIntegrable hh0 hh1.le hs0 hs1)
    intro v _
    exact rawKernel_le_uncut hh0.le
      ⟨Int.fract_nonneg (s - v), (Int.fract_lt_one (s - v)).le⟩

theorem stronglyMeasurable_circleEndpoint_average (h α : ℝ) :
    StronglyMeasurable (fun s => ∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) := by
  have hm := (measurable_circleEndpoint_pair h α).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) 1))
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hm

theorem circleEndpoint_average_height {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (s : ℝ) :
    0 ≤ (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ∧
      (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ≤ (h * α)⁻¹ := by
  constructor
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro v _
    exact (rawKernel_height hh hα).1
  · calc
      _ ≤ ∫ _v in (0 : ℝ)..1, (h * α)⁻¹ :=
        intervalIntegral.integral_mono_on (by norm_num)
          (circleEndpoint_intervalIntegrable hh hα s) intervalIntegrable_const
          (fun _ _ => (rawKernel_height hh hα).2)
      _ = _ := by simp

theorem intervalIntegrable_square_of_bound {f : ℝ → ℝ} {C : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (uIoc (0 : ℝ) 1)))
    (hC : 0 ≤ C) (hb : ∀ s ∈ Ioo (0 : ℝ) 1, |f s| ≤ C) :
    IntervalIntegrable (fun s => (f s) ^ 2) volume 0 1 := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound (by rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
    (hf.pow 2) (C ^ 2)
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 1 := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae hne] with s hs hne
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
  have hbound := hb s ⟨hs.1, lt_of_le_of_ne hs.2 hne⟩
  change ‖(f s) ^ 2‖ ≤ C ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hC] using hbound)

theorem circleEndpoint_averaged_secondMoment {h α : ℝ}
    (hh0 : 0 < h) (hh1 : h < 1) (hα : 0 < α) :
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v)^2) ≤
      1 + h^2 / (1 - h)^2 := by
  have hcut : IntervalIntegrable
      (fun s => (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v)^2) volume 0 1 := by
    apply intervalIntegrable_square_of_bound
      (stronglyMeasurable_circleEndpoint_average h α).aestronglyMeasurable
      (show 0 ≤ (h * α)⁻¹ by positivity)
    intro s _
    rw [abs_of_nonneg (circleEndpoint_average_height hh0 hα s).1]
    exact (circleEndpoint_average_height hh0 hα s).2
  have huncut : IntervalIntegrable
      (fun s => (ScalarEndpointDensity.averagedDensity h s)^2) volume 0 1 := by
    apply intervalIntegrable_square_of_bound
      (ScalarEndpointDensity.averagedDensity_intervalIntegrable hh0 hh1).def'.aestronglyMeasurable
      (show 0 ≤ (1 - h)⁻¹ by positivity)
    intro s _
    rw [abs_of_nonneg (ScalarEndpointDensity.averagedDensity_nonneg hh0 hh1 s)]
    exact ScalarEndpointDensity.averagedDensity_upper hh0 hh1 s
  calc
    _ ≤ ∫ s in (0 : ℝ)..1, (ScalarEndpointDensity.averagedDensity h s)^2 := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hcut huncut
      intro s hs
      have hp := circleEndpoint_average_le_density hh0 hh1 hα hs.1 hs.2
      exact (sq_le_sq₀ hp.1 (ScalarEndpointDensity.averagedDensity_nonneg hh0 hh1 s)).mpr hp.2
    _ ≤ _ := ScalarEndpointDensity.averagedDensity_second_moment hh0 hh1

theorem manuscriptEndpointKernel_averaged_secondMoment {m : ℕ} (hm : 200 ≤ m) :
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m s v)^2) ≤
      1 + ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by
  obtain ⟨hh, _, hα, _⟩ := manuscript_parameters hm
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hh1 : (m : ℝ)^(-(3 / 5 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hm1 (by norm_num)
  exact circleEndpoint_averaged_secondMoment hh hh1 hα

theorem circleEndpoint_periodize (h α s v : ℝ) :
    circleKernel h α (Int.fract s - v) v = circleKernel h α (s - v) v := by
  unfold circleKernel
  congr 1
  calc
    Int.fract (Int.fract s - v) = Int.fract ((s - v) - (⌊s⌋ : ℝ)) := by
      congr 1
      unfold Int.fract
      ring
    _ = _ := Int.fract_sub_intCast _ _

theorem circleEndpoint_at_zero {h α v : ℝ} (_hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hv0 : 0 < v) (hv1 : v < 1) : circleKernel h α (0 - v) v = 0 := by
  have hfract : Int.fract (-v) = 1 - v := by
    rw [Int.fract_neg (by rw [Int.fract_eq_self.mpr ⟨hv0.le, hv1⟩]; exact hv0.ne'),
      Int.fract_eq_self.mpr ⟨hv0.le, hv1⟩]
  unfold circleKernel
  rw [zero_sub, hfract, Int.fract_eq_self.mpr ⟨hv0.le, hv1⟩]
  unfold rawKernel
  split_ifs
  · apply Set.indicator_of_notMem
    intro hv
    have hd0 : 0 ≤ delta (1 - v) := delta_nonneg ⟨by linarith, by linarith⟩
    have hd : delta (1 - v) ≤ v := by
      unfold delta
      exact (min_le_right _ _).trans (by linarith)
    have hm : h * delta (1 - v) ≤ delta (1 - v) :=
      (mul_le_mul_of_nonneg_right hh1 hd0).trans_eq (one_mul _)
    linarith [hv.2]
  · rfl

theorem integral_circleEndpoint_at_zero {h α : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ v in (0 : ℝ)..1, circleKernel h α (0 - v) v) = 0 := by
  calc
    _ = ∫ _v in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro v hv
      exact circleEndpoint_at_zero hh0 hh1 hv.1 hv.2
    _ = _ := by simp

theorem circleEndpoint_average_uniform_bound {h α : ℝ}
    (hh0 : 0 < h) (hh1 : h < 1) (hα : 0 < α) (s : ℝ) :
    0 ≤ (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ∧
      (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ≤ (1 - h)⁻¹ := by
  refine ⟨(circleEndpoint_average_height hh0 hα s).1, ?_⟩
  have heq : (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) =
      ∫ v in (0 : ℝ)..1, circleKernel h α (Int.fract s - v) v := by
    apply intervalIntegral.integral_congr
    intro v _
    exact (circleEndpoint_periodize h α s v).symm
  rw [heq]
  by_cases hs : Int.fract s = 0
  · rw [hs, integral_circleEndpoint_at_zero hh0.le hh1.le]
    positivity
  · have hs0 : 0 < Int.fract s := lt_of_le_of_ne (Int.fract_nonneg s) (Ne.symm hs)
    exact (circleEndpoint_average_le_density hh0 hh1 hα hs0 (Int.fract_lt_one s)).2.trans
      (ScalarEndpointDensity.averagedDensity_upper hh0 hh1 _)

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

theorem manuscriptEndpointKernel_averaged_bounds {m : ℕ} (hm : 200 ≤ m) (s : ℝ) :
    0 ≤ (∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m s v) ∧
      (∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m s v) ≤ 2 := by
  obtain ⟨hh, _, hα, _⟩ := manuscript_parameters hm
  have hhalf := manuscript_width_le_half hm
  have hh1 : (m : ℝ)^(-(3 / 5 : ℝ)) < 1 := by linarith
  have hb := circleEndpoint_average_uniform_bound hh hh1 hα s
  refine ⟨hb.1, hb.2.trans ?_⟩
  calc
    _ ≤ ((1 / 2 : ℝ))⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    _ = 2 := by norm_num

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingVariation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set

namespace Invariant233.ScalarSampling

lemma antitone_variation_Icc_le {f : ℝ → ℝ} {a b : ℝ}
    (hf : AntitoneOn f (Icc a b)) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal (f a - f b) := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) =
        ∑ i ∈ Finset.range n, ENNReal.ofReal (f (u i) - f (u (i + 1))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [edist_comm, edist_dist, Real.dist_eq, abs_of_nonneg]
      exact sub_nonneg.mpr (hf (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, (f (u i) - f (u (i + 1)))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i _
      exact sub_nonneg.mpr (hf (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (f (u 0) - f (u n)) := by
      congr 1
      exact Finset.sum_range_sub' (fun i => f (u i)) n
    _ ≤ ENNReal.ofReal (f a - f b) := by
      apply ENNReal.ofReal_le_ofReal
      have hab : a ≤ b := (hus 0).1.trans (hus 0).2
      exact sub_le_sub (hf ⟨le_rfl, hab⟩ (hus 0) (hus 0).1)
        (hf (hus n) ⟨hab, le_rfl⟩ (hus n).2)

theorem interval_indicator_variation_le {L C : ℝ}
    (hL : 0 < L) (hLone : L ≤ 1) (hC : 0 ≤ C) :
    eVariationOn ((Ioo 0 L).indicator (fun _ => C)) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (2 * C) := by
  let f : ℝ → ℝ := (Ioo 0 L).indicator (fun _ => C)
  have hhalf : 0 < L / 2 := by linarith
  have hhalfL : L / 2 < L := by linarith
  have hhalfOne : L / 2 ≤ 1 := by linarith
  have hnonneg (x : ℝ) : 0 ≤ f x := Set.indicator_nonneg (fun _ _ => hC) x
  have hleft : MonotoneOn f (Icc 0 (L / 2)) := by
    intro x hx y hy hxy
    by_cases hx0 : 0 < x
    · have hy0 : 0 < y := hx0.trans_le hxy
      have hxL : x < L := hx.2.trans_lt hhalfL
      have hyL : y < L := hy.2.trans_lt hhalfL
      simp [f, hx0, hy0, hxL, hyL]
    · have hfx : f x = 0 := Set.indicator_of_notMem (by simp [hx0]) _
      rw [hfx]
      exact hnonneg y
  have hright : AntitoneOn f (Icc (L / 2) 1) := by
    intro x hx y hy hxy
    by_cases hyL : y < L
    · have hxL : x < L := hxy.trans_lt hyL
      have hx0 : 0 < x := hhalf.trans_le hx.1
      have hy0 : 0 < y := hhalf.trans_le hy.1
      simp [f, hx0, hy0, hxL, hyL]
    · have hfy : f y = 0 := Set.indicator_of_notMem (by simp [hyL]) _
      rw [hfy]
      exact hnonneg x
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 0 := by simp [f, not_lt.mpr hLone]
  have hfc : f (L / 2) = C := by simp [f, hhalf, hhalfL]
  have hleftBound : eVariationOn f (Icc 0 (L / 2)) ≤ ENNReal.ofReal C := by
    simpa only [inter_self, hf0, hfc, sub_zero] using
      (hleft.eVariationOn_eq ⟨le_rfl, hhalf.le⟩ ⟨hhalf.le, le_rfl⟩).le
  have hrightBound : eVariationOn f (Icc (L / 2) 1) ≤ ENNReal.ofReal C := by
    simpa only [hfc, hf1, sub_zero] using antitone_variation_Icc_le hright
  change eVariationOn f (Icc 0 1) ≤ ENNReal.ofReal (2 * C)
  calc
    eVariationOn f (Icc 0 1) =
        eVariationOn f (Icc 0 (L / 2)) + eVariationOn f (Icc (L / 2) 1) := by
      simpa only [univ_inter] using
        (eVariationOn.Icc_add_Icc f hhalf.le hhalfOne (mem_univ (L / 2))).symm
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal C := add_le_add hleftBound hrightBound
    _ = ENNReal.ofReal (2 * C) := by rw [← ENNReal.ofReal_add hC hC]; congr 1; ring

theorem rawKernel_le_height {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (s t : ℝ) :
    rawKernel h α s t ≤ (h * α)⁻¹ := by
  unfold rawKernel
  split_ifs with hs
  · by_cases ht : t ∈ Ioo 0 (h * delta s)
    · rw [Set.indicator_of_mem ht]
      simpa only [one_div] using one_div_le_one_div_of_le (mul_pos hh hα)
        (mul_le_mul_of_nonneg_left hs hh.le)
    · rw [Set.indicator_of_notMem ht]
      positivity
  · positivity

theorem rawKernel_variation_le {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (s : ℝ) :
    eVariationOn (rawKernel h α s) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (2 * (h * α)⁻¹) := by
  by_cases hs : α ≤ delta s
  · have hdelta : 0 < delta s := hα.trans_le hs
    have hL : 0 < h * delta s := mul_pos hh hdelta
    have hLone : h * delta s ≤ 1 := by
      calc
        h * delta s ≤ 1 * delta s := mul_le_mul_of_nonneg_right hhone hdelta.le
        _ ≤ 1 := by nlinarith [delta_le_half s]
    have hi : (h * delta s)⁻¹ ≤ (h * α)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (mul_pos hh hα)
        (mul_le_mul_of_nonneg_left hs hh.le)
    have hfun : rawKernel h α s = (Ioo 0 (h * delta s)).indicator
        (fun _ => (h * delta s)⁻¹) := by
      funext t
      simp only [rawKernel, ite_eq_left hs]
    rw [hfun]
    exact (interval_indicator_variation_le hL hLone (inv_nonneg.mpr hL.le)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hi (by norm_num)))
  · simp [rawKernel, hs, eVariationOn]

lemma rawKernel_zero (h α s : ℝ) : rawKernel h α s 0 = 0 := by
  unfold rawKernel
  split_ifs <;> simp

lemma rawKernel_one {h α s : ℝ} (hhone : h ≤ 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    rawKernel h α s 1 = 0 := by
  have hLone : h * delta s ≤ 1 := by
    calc
      h * delta s ≤ 1 * delta s := mul_le_mul_of_nonneg_right hhone (delta_nonneg hs)
      _ ≤ 1 := by nlinarith [delta_le_half s]
  unfold rawKernel
  split_ifs
  · apply Set.indicator_of_notMem
    intro ht
    exact (not_lt.mpr hLone) ht.2
  · rfl

lemma circleKernel_eq_raw_on_unit {h α : ℝ} (hhone : h ≤ 1) (z : ℝ)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    circleKernel h α z v = rawKernel h α (Int.fract z) v := by
  rcases lt_or_eq_of_le hv.2 with hlt | heq
  · simp only [circleKernel, Int.fract_eq_self.mpr ⟨hv.1, hlt⟩]
  · subst v
    simp only [circleKernel, Int.fract_one, rawKernel_zero]
    exact (rawKernel_one hhone ⟨Int.fract_nonneg z, (Int.fract_lt_one z).le⟩).symm

theorem circleKernel_variation_le {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (z : ℝ) :
    eVariationOn (circleKernel h α z) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (2 * (h * α)⁻¹) := by
  rw [eVariationOn.congr (fun _ hv => circleKernel_eq_raw_on_unit hhone z hv)]
  exact rawKernel_variation_le hh hhone hα (Int.fract z)

lemma manuscript_reciprocal_height {m : ℕ} (hm : 200 ≤ m) :
    ((m : ℝ) ^ (-(3 / 5 : ℝ)) * (1 / (m : ℝ)^2))⁻¹ = (m : ℝ) ^ (13 / 5 : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have htwo : 1 / (m : ℝ)^2 = (m : ℝ) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hmpos.le, Real.rpow_two]
    simp only [one_div]
  rw [htwo, ← Real.rpow_add hmpos, ← Real.rpow_neg hmpos.le]
  congr 1
  norm_num

theorem manuscriptKernel_variation_le {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    eVariationOn (manuscriptKernel m z) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (2 * (m : ℝ) ^ (13 / 5 : ℝ)) := by
  obtain ⟨hh, hhone, hα, _⟩ := manuscript_parameters hm
  change eVariationOn (circleKernel _ _ z) _ ≤ _
  simpa only [manuscript_reciprocal_height hm] using circleKernel_variation_le hh hhone hα z

theorem manuscriptKernel_le_height {m : ℕ} (hm : 200 ≤ m) (z v : ℝ) :
    manuscriptKernel m z v ≤ (m : ℝ) ^ (13 / 5 : ℝ) := by
  obtain ⟨hh, _, hα, _⟩ := manuscript_parameters hm
  simpa only [manuscriptKernel, circleKernel, manuscript_reciprocal_height hm] using
    rawKernel_le_height hh hα (Int.fract z) (Int.fract v)

theorem manuscriptKernel_sup_le {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    sSup (Set.range (fun v : ℝ => |manuscriptKernel m z v|)) ≤
      (m : ℝ) ^ (13 / 5 : ℝ) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨v, rfl⟩
  have hh := (manuscript_parameters hm).1
  have hnonneg : 0 ≤ manuscriptKernel m z v :=
    rawKernel_nonneg hh.le ⟨Int.fract_nonneg z, (Int.fract_lt_one z).le⟩
  dsimp only
  rw [abs_of_nonneg hnonneg]
  exact manuscriptKernel_le_height hm z v

theorem manuscriptKernel_BV_bound {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    BoundedVariationOn (manuscriptKernel m z) (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun v : ℝ => |manuscriptKernel m z v|)) +
          (eVariationOn (manuscriptKernel m z) (Icc (0 : ℝ) 1)).toReal ≤
        3 * (m : ℝ) ^ (13 / 5 : ℝ) := by
  constructor
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (manuscriptKernel_variation_le hm z)
  · have hv := ENNReal.toReal_le_of_le_ofReal
      (by positivity) (manuscriptKernel_variation_le hm z)
    have hf := manuscriptKernel_sup_le hm z
    linarith

theorem manuscriptKernel_BV_bound_ten {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    sSup (Set.range (fun v : ℝ => |manuscriptKernel m z v|)) +
        (eVariationOn (manuscriptKernel m z) (Icc (0 : ℝ) 1)).toReal ≤
      3 * (m : ℝ)^10 := by
  calc
    _ ≤ 3 * (m : ℝ) ^ (13 / 5 : ℝ) := (manuscriptKernel_BV_bound hm z).2
    _ ≤ 3 * (m : ℝ)^10 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ m))
        (by norm_num)

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingShear
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

lemma integrableOn_unitSquare_of_bound {F : ℝ → ℝ → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F)) (hC : ∀ x y, ‖F x y‖ ≤ C) :
    IntegrableOn (Function.uncurry F) (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) := by
  have hfinite : volume (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) < ⊤ := by
    apply lt_of_le_of_lt (measure_mono (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc))
    exact (isCompact_uIcc.prod isCompact_uIcc).measure_lt_top
  exact IntegrableOn.of_bound hfinite hF.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun p => hC p.1 p.2))

theorem double_interval_integral_shear {F : ℝ → ℝ → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F)) (hC : ∀ x y, ‖F x y‖ ≤ C)
    (hperiodic : ∀ y, Function.Periodic (fun x => F x y) 1) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, F (x - y) y) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, F x y := by
  have hG : Measurable (fun p : ℝ × ℝ => F (p.1 - p.2) p.2) :=
    hF.comp ((measurable_fst.sub measurable_snd).prodMk measurable_snd)
  have hFi := integrableOn_unitSquare_of_bound hF hC
  have hGi := integrableOn_unitSquare_of_bound (F := fun x y => F (x - y) y) hG (fun x y => hC (x - y) y)
  rw [intervalIntegral_intervalIntegral_swap hGi, intervalIntegral_intervalIntegral_swap hFi]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  calc
    (∫ x in (0 : ℝ)..1, F (x - y) y) = ∫ x in (-y)..(-y + 1), F x y := by
      rw [intervalIntegral.integral_comp_sub_right (fun x => F x y) y]
      congr 1 <;> ring
    _ = ∫ x in (0 : ℝ)..1, F x y := by
      simpa only [zero_add] using (hperiodic y).intervalIntegral_add_eq (-y) 0

theorem measurable_circleKernel (h α : ℝ) :
    Measurable (Function.uncurry (circleKernel h α)) := by
  have hz : Measurable (fun p : ℝ × ℝ => Int.fract p.1) :=
    measurable_fract.comp measurable_fst
  have hv : Measurable (fun p : ℝ × ℝ => Int.fract p.2) :=
    measurable_fract.comp measurable_snd
  have hd : Measurable (fun p : ℝ × ℝ => delta (Int.fract p.1)) :=
    hz.min (measurable_const.sub hz)
  change Measurable (fun p : ℝ × ℝ => circleKernel h α p.1 p.2)
  simp only [circleKernel, rawKernel, Set.indicator_apply]
  apply Measurable.ite (measurableSet_le measurable_const hd)
  · apply Measurable.ite
    · exact (measurableSet_lt measurable_const hv).inter
        (measurableSet_lt hv (measurable_const.mul hd))
    · exact (measurable_const.mul hd).inv
    · exact measurable_const
  · exact measurable_const

lemma circleKernel_periodic_left (h α v : ℝ) :
    Function.Periodic (fun z => circleKernel h α z v) 1 := by
  intro z
  simp only [circleKernel, Int.fract_add_one]

lemma circleKernel_norm_le {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (z v : ℝ) :
    ‖circleKernel h α z v‖ ≤ (h * α)⁻¹ := by
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact rawKernel_le_height hh hα _ _
  · exact rawKernel_nonneg hh.le ⟨Int.fract_nonneg z, (Int.fract_lt_one z).le⟩

theorem endpoint_circleKernel_mass {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α (z - v) v) =
      1 - 2 * α := by
  rw [double_interval_integral_shear (measurable_circleKernel h α)
    (circleKernel_norm_le hh hα) (circleKernel_periodic_left h α)]
  exact double_interval_integral_circleKernel hh hhone hα hαhalf

theorem endpoint_circleKernel_secondMoment {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α (z - v) v ^ 2) =
      (2 / h) * Real.log (1 / (2 * α)) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => circleKernel h α p.1 p.2 ^ 2) :=
    (measurable_circleKernel h α).pow_const 2
  have hbound (z v : ℝ) : ‖circleKernel h α z v ^ 2‖ ≤ ((h * α)⁻¹)^2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (circleKernel_norm_le hh hα z v) 2
  have hper (v : ℝ) : Function.Periodic (fun z => circleKernel h α z v ^ 2) 1 := by
    intro z
    exact congrArg (fun x : ℝ => x^2) (circleKernel_periodic_left h α v z)
  rw [double_interval_integral_shear (F := fun z v => circleKernel h α z v ^ 2) hmeas hbound hper]
  exact double_interval_integral_sq_circleKernel hh hhone hα hαhalf

theorem manuscriptEndpointKernel_mass {m : ℕ} (hm : 200 ≤ m) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m z v) =
      1 - 2 / (m : ℝ)^2 := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  simpa only [manuscriptEndpointKernel, manuscriptKernel, mul_one_div] using
    endpoint_circleKernel_mass hh hhone hα hαhalf

theorem manuscriptEndpointKernel_secondMoment {m : ℕ} (hm : 200 ≤ m) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m z v ^ 2) =
      (2 / (m : ℝ) ^ (-(3 / 5 : ℝ))) * Real.log ((m : ℝ)^2 / 2) := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have heq : 1 / (2 * (1 / (m : ℝ)^2)) = (m : ℝ)^2 / 2 := by
    field_simp [hmR.ne']
  simpa only [manuscriptEndpointKernel, manuscriptKernel, heq] using
    endpoint_circleKernel_secondMoment hh hhone hα hαhalf

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingEndpointVariation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set

namespace Invariant233.ScalarSampling

lemma variation_add_le {f g : ℝ → ℝ} {s : Set ℝ} :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i+1)) + g (u (i+1))) (f (u i) + g (u i))) ≤
        ∑ i ∈ Finset.range n, (edist (f (u (i+1))) (f (u i)) +
          edist (g (u (i+1))) (g (u i))) := by
      exact Finset.sum_le_sum (fun i _ => edist_add_add_le _ _ _ _)
    _ = (∑ i ∈ Finset.range n, edist (f (u (i+1))) (f (u i))) +
        (∑ i ∈ Finset.range n, edist (g (u (i+1))) (g (u i))) := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

lemma variation_mul_le {f g : ℝ → ℝ} {s : Set ℝ} {F G : ℝ}
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hf : ∀ x ∈ s, |f x| ≤ F) (hg : ∀ x ∈ s, |g x| ≤ G) :
    eVariationOn (fun x => f x * g x) s ≤
      ENNReal.ofReal F * eVariationOn g s + ENNReal.ofReal G * eVariationOn f s := by
  have hp (x y : ℝ) (hx : x ∈ s) (hy : y ∈ s) :
      edist (f x * g x) (f y * g y) ≤
        ENNReal.ofReal F * edist (g x) (g y) +
        ENNReal.ofReal G * edist (f x) (f y) := by
    simp only [edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_mul hF, ← ENNReal.ofReal_mul hG,
      ← ENNReal.ofReal_add (mul_nonneg hF (abs_nonneg _)) (mul_nonneg hG (abs_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    calc
      |f x * g x - f y * g y| = |f x * (g x - g y) + g y * (f x - f y)| := by ring_nf
      _ ≤ |f x * (g x - g y)| + |g y * (f x - f y)| := abs_add_le _ _
      _ = |f x| * |g x - g y| + |g y| * |f x - f y| := by rw [abs_mul, abs_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (hf x hx) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (hg y hy) (abs_nonneg _))
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i+1)) * g (u (i+1))) (f (u i) * g (u i))) ≤
        ∑ i ∈ Finset.range n, (ENNReal.ofReal F * edist (g (u (i+1))) (g (u i)) +
          ENNReal.ofReal G * edist (f (u (i+1))) (f (u i))) :=
      Finset.sum_le_sum (fun i _ => hp _ _ (hus _) (hus _))
    _ = ENNReal.ofReal F * (∑ i ∈ Finset.range n, edist (g (u (i+1))) (g (u i))) +
        ENNReal.ofReal G * (∑ i ∈ Finset.range n, edist (f (u (i+1))) (f (u i))) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_right (eVariationOn.sum_le hu hus) _)
      (mul_le_mul_right (eVariationOn.sum_le hu hus) _)

lemma monotone_variation_le_height {f : ℝ → ℝ} {C : ℝ}
    (hf : MonotoneOn f (Icc (0 : ℝ) 1))
    (hbound : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x ∧ f x ≤ C) :
    eVariationOn f (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal C := by
  have h := (hf.eVariationOn_eq (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)).le
  simp only [inter_self] at h
  exact h.trans (ENNReal.ofReal_le_ofReal (by linarith [(hbound 0 (by norm_num)).1,
    (hbound 1 (by norm_num)).2]))

lemma antitone_variation_le_height {f : ℝ → ℝ} {C : ℝ}
    (hf : AntitoneOn f (Icc (0 : ℝ) 1))
    (hbound : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x ∧ f x ≤ C) :
    eVariationOn f (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal C := by
  exact (antitone_variation_Icc_le hf).trans (ENNReal.ofReal_le_ofReal
    (by linarith [(hbound 0 (by norm_num)).2, (hbound 1 (by norm_num)).1]))

lemma variation_step_le (P : ℝ → Prop) [DecidablePred P]
    (hP : (∀ x y, x ≤ y → P x → P y) ∨ (∀ x y, x ≤ y → P y → P x)) :
    eVariationOn (fun x => if P x then (1 : ℝ) else 0) (Icc (0 : ℝ) 1) ≤ 1 := by
  have hb (x : ℝ) (_ : x ∈ Icc (0 : ℝ) 1) :
      0 ≤ (if P x then (1 : ℝ) else 0) ∧ (if P x then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  rcases hP with hP | hP
  · have hm : MonotoneOn (fun x => if P x then (1 : ℝ) else 0) (Icc (0 : ℝ) 1) := by
      intro x _ y _ hxy
      by_cases hx : P x
      · simp [hx, hP x y hxy hx]
      · simp [hx]; split_ifs <;> norm_num
    simpa using monotone_variation_le_height hm hb
  · have hm : AntitoneOn (fun x => if P x then (1 : ℝ) else 0) (Icc (0 : ℝ) 1) := by
      intro x _ y _ hxy
      by_cases hy : P y
      · simp [hy, hP x y hxy hy]
      · simp [hy]; split_ifs <;> norm_num
    simpa using antitone_variation_le_height hm hb

lemma VariationControl.mask {f : ℝ → ℝ} {C V : ℝ}
    (hf : VariationControl f C V) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (P : ℝ → Prop) [DecidablePred P]
    (hP : (∀ x y, x ≤ y → P x → P y) ∨ (∀ x y, x ≤ y → P y → P x)) :
    VariationControl (fun x => if P x then f x else 0) C (V + C) := by
  constructor
  · intro x; split_ifs; exact hf.nonneg x; exact le_rfl
  · intro x; split_ifs; exact hf.le_height x; exact hC
  · let g : ℝ → ℝ := fun x => if P x then 1 else 0
    have heq : (fun x => if P x then f x else 0) = fun x => f x * g x := by
      funext x; simp only [g]; split_ifs <;> simp
    rw [heq]
    have hb : ∀ x ∈ Icc (0 : ℝ) 1, |g x| ≤ 1 := by
      intro x _; simp only [g]; split_ifs <;> norm_num
    calc
      eVariationOn (fun x => f x * g x) (Icc (0 : ℝ) 1) ≤
          ENNReal.ofReal C * eVariationOn g (Icc (0 : ℝ) 1) +
          ENNReal.ofReal 1 * eVariationOn f (Icc (0 : ℝ) 1) :=
        variation_mul_le hC (by norm_num)
          (fun x _ => by rw [abs_of_nonneg (hf.nonneg x)]; exact hf.le_height x) hb
      _ ≤ ENNReal.ofReal C * 1 + ENNReal.ofReal 1 * ENNReal.ofReal V :=
        add_le_add (mul_le_mul_right (variation_step_le P hP) _) (mul_le_mul_right hf.variation _)
      _ = ENNReal.ofReal (V + C) := by
        simp only [ENNReal.ofReal_one, mul_one, one_mul]
        rw [← ENNReal.ofReal_add hC hV, add_comm]

lemma clipped_reciprocal_control {h α : ℝ} (hh : 0 < h) (hα : 0 < α)
    (g : ℝ → ℝ) (hg : Monotone g ∨ Antitone g) :
    VariationControl (fun x => (h * max α (g x))⁻¹) (h * α)⁻¹ (h * α)⁻¹ := by
  have hpos (x : ℝ) : 0 < h * max α (g x) := mul_pos hh (hα.trans_le (le_max_left _ _))
  have hn (x : ℝ) : 0 ≤ (h * max α (g x))⁻¹ := inv_nonneg.mpr (hpos x).le
  have hb (x : ℝ) : (h * max α (g x))⁻¹ ≤ (h * α)⁻¹ := by
    exact inv_anti₀ (mul_pos hh hα) (mul_le_mul_of_nonneg_left (le_max_left _ _) hh.le)
  refine ⟨hn, hb, ?_⟩
  rcases hg with hg | hg
  · apply antitone_variation_le_height
    · intro x _ y _ hxy
      exact inv_anti₀ (hpos x) (mul_le_mul_of_nonneg_left (max_le_max_left α (hg hxy)) hh.le)
    · exact fun x _ => ⟨hn x, hb x⟩
  · apply monotone_variation_le_height
    · intro x _ y _ hxy
      exact inv_anti₀ (hpos y) (mul_le_mul_of_nonneg_left (max_le_max_left α (hg hxy)) hh.le)
    · exact fun x _ => ⟨hn x, hb x⟩

lemma leftEndpointPiece_control {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (s : ℝ) :
    VariationControl (leftEndpointPiece h α s) (h * α)⁻¹ (5 * (h * α)⁻¹) := by
  have hC : 0 ≤ (h * α)⁻¹ := by positivity
  have hb := clipped_reciprocal_control hh hα (fun v => s - v)
    (Or.inr (show Antitone (fun v : ℝ => s - v) from fun _ _ hxy => sub_le_sub_left hxy s))
  have h1 := hb.mask hC hC (fun v => s - v ≤ 1 / 2)
    (Or.inl (by intro x y hxy hx; linarith))
  have h2 := h1.mask hC (by positivity) (fun v => α ≤ s - v)
    (Or.inr (by intro x y hxy hy; linarith))
  have h3 := h2.mask hC (by positivity) (fun v => v < h * (s - v))
    (Or.inr (by intro x y hxy hy; nlinarith))
  have h4 := h3.mask hC (by positivity) (fun v => 0 < v)
    (Or.inl (by intro x y hxy hx; exact hx.trans_le hxy))
  convert h4 using 1
  · rfl
  · ring

lemma rightEndpointPiece_control {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (s : ℝ) :
    VariationControl (rightEndpointPiece h α s) (h * α)⁻¹ (5 * (h * α)⁻¹) := by
  have hC : 0 ≤ (h * α)⁻¹ := by positivity
  have hb := clipped_reciprocal_control hh hα (fun v => 1 - s + v)
    (Or.inl (show Monotone (fun v : ℝ => 1 - s + v) from by intro x y hxy; dsimp <;> linarith))
  have h1 := hb.mask hC hC (fun v => 1 / 2 < s - v)
    (Or.inr (by intro x y hxy hy; linarith))
  have h2 := h1.mask hC (by positivity) (fun v => α ≤ 1 - s + v)
    (Or.inl (by intro x y hxy hx; linarith))
  have h3 := h2.mask hC (by positivity) (fun v => v < h * (1 - s + v))
    (Or.inr (by intro x y hxy hy; nlinarith))
  have h4 := h3.mask hC (by positivity) (fun v => 0 < v)
    (Or.inl (by intro x y hxy hx; exact hx.trans_le hxy))
  convert h4 using 1
  · rfl
  · ring

lemma rawEndpoint_eq_pieces (h α s v : ℝ) :
    rawKernel h α (s - v) v = leftEndpointPiece h α s v + rightEndpointPiece h α s v := by
  by_cases hm : s - v ≤ 1 / 2
  · have hd : delta (s - v) = s - v := by
      unfold delta; rw [min_eq_left (by linarith)]
    have hn : ¬ 1 / 2 < s - v := not_lt.mpr hm
    by_cases hc : α ≤ s - v
    · simp only [rawKernel, hd, ite_eq_left hc, max_eq_right hc,
        leftEndpointPiece, rightEndpointPiece, ite_eq_left hm, ite_eq_right hn,
        Set.indicator_apply, mem_Ioo]
      split_ifs <;> simp_all
    · simp only [rawKernel, hd, ite_eq_right hc, leftEndpointPiece, rightEndpointPiece,
        ite_eq_left hm, ite_eq_right hn]
      split_ifs <;> simp_all
  · have hm' : 1 / 2 < s - v := lt_of_not_ge hm
    have hd : delta (s - v) = 1 - s + v := by
      unfold delta; rw [min_eq_right (by linarith)]; ring
    by_cases hc : α ≤ 1 - s + v
    · simp only [rawKernel, hd, ite_eq_left hc, leftEndpointPiece, rightEndpointPiece,
        ite_eq_right hm, ite_eq_left hm', max_eq_right hc, Set.indicator_apply, mem_Ioo]
      split_ifs <;> simp_all
    · simp only [rawKernel, hd, ite_eq_right hc, leftEndpointPiece, rightEndpointPiece,
        ite_eq_right hm, ite_eq_left hm']
      split_ifs <;> simp_all

theorem rawEndpoint_variation_le {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (s : ℝ) :
    eVariationOn (fun v => rawKernel h α (s - v) v) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (10 * (h * α)⁻¹) := by
  have hl := (leftEndpointPiece_control hh hα s).variation
  have hr := (rightEndpointPiece_control hh hhone hα s).variation
  have heq : (fun v => rawKernel h α (s - v) v) =
      fun v => leftEndpointPiece h α s v + rightEndpointPiece h α s v := by
    funext v; exact rawEndpoint_eq_pieces h α s v
  rw [heq]
  calc
    _ ≤ eVariationOn (leftEndpointPiece h α s) (Icc (0 : ℝ) 1) +
        eVariationOn (rightEndpointPiece h α s) (Icc (0 : ℝ) 1) := variation_add_le
    _ ≤ ENNReal.ofReal (5 * (h * α)⁻¹) + ENNReal.ofReal (5 * (h * α)⁻¹) := add_le_add hl hr
    _ = ENNReal.ofReal (10 * (h * α)⁻¹) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring

theorem endpoint_no_wrap_on_unit {h α s v : ℝ} (_hh : 0 ≤ h) (hhone : h ≤ 1)
    (hα : 0 < α) (hs : s ∈ Ico (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    circleKernel h α (s - v) v = rawKernel h α (s - v) v := by
  rcases lt_or_eq_of_le hv.2 with hvone | hvone
  · unfold circleKernel
    rw [Int.fract_eq_self.mpr ⟨hv.1, hvone⟩]
    by_cases hvs : v ≤ s
    · rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith [hs.2, hv.1]⟩]
    · have hsv : s < v := lt_of_not_ge hvs
      have hcut : ¬ α ≤ delta (s - v) := by
        have hd : delta (s - v) ≤ s - v := min_le_left _ _
        linarith
      have hfloor : ⌊s - v⌋ = -1 := by
        apply Int.floor_eq_iff.mpr
        norm_num
        constructor <;> linarith [hs.1]
      have hfract : Int.fract (s - v) = s - v + 1 := by
        rw [Int.fract, hfloor]; norm_num
      rw [hfract]
      unfold rawKernel
      rw [ite_eq_right hcut]
      split_ifs
      · apply Set.indicator_of_notMem
        intro hmem
        have hd0 : 0 ≤ delta (s - v + 1) := by
          apply delta_nonneg; constructor <;> linarith [hs.1]
        have hd : delta (s - v + 1) ≤ v - s := by
          exact (min_le_right _ _).trans (by linarith)
        have hm : h * delta (s - v + 1) ≤ delta (s - v + 1) := by
          nlinarith
        linarith [hmem.2, hs.1]
      · rfl
  · subst v
    have hcut : ¬ α ≤ delta (s - 1) := by
      have hd : delta (s - 1) ≤ s - 1 := min_le_left _ _
      linarith [hs.2]
    simp only [circleKernel, Int.fract_one]
    rw [rawKernel_zero]
    simp only [rawKernel, ite_eq_right hcut]

lemma circleEndpoint_fract (h α z v : ℝ) :
    circleKernel h α (z - v) v = circleKernel h α (Int.fract z - v) v := by
  have heq : Int.fract z - v = (z - v) - (⌊z⌋ : ℤ) := by
    rw [Int.fract]; ring
  simp only [circleKernel, heq, Int.fract_sub_intCast]

theorem circleEndpoint_variation_le {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (z : ℝ) :
    eVariationOn (fun v => circleKernel h α (z - v) v) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (10 * (h * α)⁻¹) := by
  have heq : EqOn (fun v => circleKernel h α (z - v) v)
      (fun v => rawKernel h α (Int.fract z - v) v) (Icc (0 : ℝ) 1) := by
    intro v hv
    dsimp only
    rw [circleEndpoint_fract]
    exact endpoint_no_wrap_on_unit hh.le hhone hα ⟨Int.fract_nonneg z, Int.fract_lt_one z⟩ hv
  rw [eVariationOn.congr heq]
  exact rawEndpoint_variation_le hh hhone hα _

theorem manuscriptEndpointKernel_variation_le {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    eVariationOn (manuscriptEndpointKernel m z) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (10 * (m : ℝ) ^ (13 / 5 : ℝ)) := by
  obtain ⟨hh, hhone, hα, _⟩ := manuscript_parameters hm
  change eVariationOn (fun v => circleKernel _ _ (z - v) v) _ ≤ _
  simpa only [manuscript_reciprocal_height hm] using
    circleEndpoint_variation_le hh hhone hα z

theorem manuscriptEndpointKernel_sup_le {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    sSup (Set.range (fun v : ℝ => |manuscriptEndpointKernel m z v|)) ≤
      (m : ℝ) ^ (13 / 5 : ℝ) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨v, rfl⟩
  have hh := (manuscript_parameters hm).1
  have hn : 0 ≤ manuscriptKernel m (z-v) v :=
    rawKernel_nonneg hh.le ⟨Int.fract_nonneg (z-v), (Int.fract_lt_one (z-v)).le⟩
  dsimp only [manuscriptEndpointKernel]
  rw [abs_of_nonneg hn]
  exact manuscriptKernel_le_height hm _ _

theorem manuscriptEndpointKernel_BV_bound {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    BoundedVariationOn (manuscriptEndpointKernel m z) (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun v : ℝ => |manuscriptEndpointKernel m z v|)) +
          (eVariationOn (manuscriptEndpointKernel m z) (Icc (0 : ℝ) 1)).toReal ≤
        11 * (m : ℝ) ^ (13 / 5 : ℝ) := by
  constructor
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (manuscriptEndpointKernel_variation_le hm z)
  · have hv := ENNReal.toReal_le_of_le_ofReal
      (by positivity) (manuscriptEndpointKernel_variation_le hm z)
    have hf := manuscriptEndpointKernel_sup_le hm z
    linarith

theorem manuscriptEndpointKernel_BV_bound_ten {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    sSup (Set.range (fun v : ℝ => |manuscriptEndpointKernel m z v|)) +
        (eVariationOn (manuscriptEndpointKernel m z) (Icc (0 : ℝ) 1)).toReal ≤
      11 * (m : ℝ)^10 := by
  calc
    _ ≤ 11 * (m : ℝ) ^ (13 / 5 : ℝ) := (manuscriptEndpointKernel_BV_bound hm z).2
    _ ≤ 11 * (m : ℝ)^10 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ m))
        (by norm_num)

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingJensen
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

lemma sq_integral_le_integral_sq_unit {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1)
    (hfsq : IntervalIntegrable (fun x => f x ^ 2) volume 0 1) :
    (∫ x in (0 : ℝ)..1, f x)^2 ≤ ∫ x in (0 : ℝ)..1, f x ^ 2 := by
  let c : ℝ := ∫ x in (0 : ℝ)..1, f x
  have hn : 0 ≤ ∫ x in (0 : ℝ)..1, (f x - c)^2 :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun x => sq_nonneg _)
  have heq : (fun x => (f x - c)^2) = fun x => (f x^2 - (2*c)*f x) + c^2 := by
    funext x; ring
  rw [heq, intervalIntegral.integral_add (hfsq.sub (hf.const_mul (2*c)))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c^2) volume 0 1),
    intervalIntegral.integral_sub hfsq (hf.const_mul (2*c)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hn
  simp only [sub_zero, one_smul] at hn
  change c^2 ≤ ∫ x in (0 : ℝ)..1, f x^2
  change 0 ≤ (∫ x in (0 : ℝ)..1, f x^2) - (2*c)*c + c^2 at hn
  nlinarith

lemma intervalIntegrable_unit_of_measurable_bound {f : ℝ → ℝ} {C : ℝ}
    (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ C) :
    IntervalIntegrable f volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  apply IntegrableOn.of_bound (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hf.aestronglyMeasurable C
  exact Filter.Eventually.of_forall hb

lemma measurable_interval_average {F : ℝ → ℝ → ℝ}
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun x => ∫ y in (0 : ℝ)..1, F x y) := by
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact hF.stronglyMeasurable.integral_prod_right.measurable

lemma endpoint_average_integrable {h α : ℝ} (hh : 0 < h) (hα : 0 < α) :
    IntervalIntegrable (fun z => ∫ v in (0 : ℝ)..1, circleKernel h α (z-v) v) volume 0 1 ∧
    IntervalIntegrable (fun z => (∫ v in (0 : ℝ)..1, circleKernel h α (z-v) v)^2) volume 0 1 := by
  have hm : Measurable (fun p : ℝ × ℝ => circleKernel h α (p.1-p.2) p.2) :=
    (measurable_circleKernel h α).comp ((measurable_fst.sub measurable_snd).prodMk measurable_snd)
  have hbar := measurable_interval_average (F := fun z v => circleKernel h α (z-v) v) hm
  have hb (z : ℝ) : ‖∫ v in (0 : ℝ)..1, circleKernel h α (z-v) v‖ ≤ (h*α)⁻¹ := by
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const
      (fun v (_ : v ∈ uIoc (0 : ℝ) 1) => circleKernel_norm_le hh hα (z-v) v)
  constructor
  · exact intervalIntegrable_unit_of_measurable_bound hbar hb
  · apply intervalIntegrable_unit_of_measurable_bound (hbar.pow_const 2)
    intro z
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb z) 2

theorem circleEndpoint_averaged_secondMoment_lower {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (1 - 2*α)^2 ≤ ∫ z in (0 : ℝ)..1,
      (∫ v in (0 : ℝ)..1, circleKernel h α (z-v) v)^2 := by
  obtain ⟨hi, hisq⟩ := endpoint_average_integrable hh hα
  have hj := sq_integral_le_integral_sq_unit hi hisq
  rwa [endpoint_circleKernel_mass hh hhone hα hαhalf] at hj

theorem manuscriptEndpointKernel_averaged_secondMoment_lower_from_mass {m : ℕ} (hm : 200 ≤ m) :
    (1 - 2 / (m : ℝ)^2)^2 ≤ ∫ z in (0 : ℝ)..1,
      (∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m z v)^2 := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  simpa only [manuscriptEndpointKernel, manuscriptKernel, mul_one_div] using
    circleEndpoint_averaged_secondMoment_lower hh hhone hα hαhalf

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarKernelEstimates
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem manuscriptKernel_averaged_bounds {m : ℕ} (hm : 200 ≤ m) (s : ℝ) :
    0 ≤ (∫ v in (0 : ℝ)..1, manuscriptKernel m s v) ∧
      (∫ v in (0 : ℝ)..1, manuscriptKernel m s v) ≤ 2 := by
  obtain ⟨hh, hhone, hα, _⟩ := manuscript_parameters hm
  have hb := averaged_circleKernel_bounds hh hhone hα s
  exact ⟨hb.1, hb.2.trans (by norm_num)⟩

theorem manuscriptKernel_averaged_secondMoment_exact {m : ℕ} (hm : 200 ≤ m) :
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, manuscriptKernel m s v)^2) =
      1 - 2 / (m : ℝ)^2 := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  simpa only [manuscriptKernel, mul_one_div] using
    integral_sq_averaged_circleKernel hh hhone hα hαhalf

theorem manuscriptKernel_averaged_secondMoment_bounds {m : ℕ} (hm : 200 ≤ m) :
    (1 - 2 / (m : ℝ)^2)^2 ≤
      (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, manuscriptKernel m s v)^2) ∧
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, manuscriptKernel m s v)^2) ≤
      1 + ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by
  rw [manuscriptKernel_averaged_secondMoment_exact hm]
  have hα := (manuscript_parameters hm).2.2
  have hq0 : 0 ≤ 2 / (m : ℝ)^2 := by positivity
  have hq1 : 2 / (m : ℝ)^2 ≤ 1 := by
    have := hα.2
    rw [div_eq_mul_inv] at this ⊢
    nlinarith
  constructor
  · nlinarith
  · have : 0 ≤ ((m : ℝ)^(-(3 / 5 : ℝ)))^2 /
        (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by positivity
    linarith

theorem manuscriptKernel_estimates {m : ℕ} (hm : 200 ≤ m) :
    KernelEstimates m (manuscriptKernel m) where
  boundedVariation s := (manuscriptKernel_BV_bound hm s).1
  variation_sharp s := (manuscriptKernel_BV_bound hm s).2.trans
    (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  variation_coarse s := (manuscriptKernel_BV_bound_ten hm s).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  average_bounds := manuscriptKernel_averaged_bounds hm
  mass := manuscriptKernel_mass hm
  average_square_lower := (manuscriptKernel_averaged_secondMoment_bounds hm).1
  average_square_upper := (manuscriptKernel_averaged_secondMoment_bounds hm).2
  square_mass := manuscriptKernel_secondMoment hm

theorem manuscriptEndpointKernel_estimates {m : ℕ} (hm : 200 ≤ m) :
    KernelEstimates m (manuscriptEndpointKernel m) where
  boundedVariation s := (manuscriptEndpointKernel_BV_bound hm s).1
  variation_sharp s := (manuscriptEndpointKernel_BV_bound hm s).2
  variation_coarse := manuscriptEndpointKernel_BV_bound_ten hm
  average_bounds := manuscriptEndpointKernel_averaged_bounds hm
  mass := manuscriptEndpointKernel_mass hm
  average_square_lower := manuscriptEndpointKernel_averaged_secondMoment_lower_from_mass hm
  average_square_upper := manuscriptEndpointKernel_averaged_secondMoment hm
  square_mass := manuscriptEndpointKernel_secondMoment hm

theorem both_kernel_estimates {m : ℕ} (hm : 200 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    KernelEstimates m u := by
  rcases hu with rfl | rfl
  · exact manuscriptKernel_estimates hm
  · exact manuscriptEndpointKernel_estimates hm

end Invariant233.ScalarSampling

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

end InvariantProjection.IndependentAngles

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingEstimates
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem parameter_kernel_eq_manuscript {m : ℕ} (hm : 200 ≤ m) (z : ℝ)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    CircleParameterData.kernel m z v = manuscriptKernel m z v := by
  rw [manuscriptKernel, circleKernel_eq_raw_on_unit (manuscript_parameters hm).2.1 z hv]
  unfold CircleParameterData.kernel CircleParameterData.delta CircleParameterData.kernelWidth
    rawKernel delta
  simp only [Set.indicator_apply, mem_Ioo, ite_and, one_div]

theorem parameter_orientedKernel_eq {m : ℕ} (hm : 200 ≤ m)
    (endpoint : Bool) (z : ℝ) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    CircleParameterData.orientedKernel endpoint m z v =
      if endpoint then manuscriptEndpointKernel m z v else manuscriptKernel m z v := by
  cases endpoint <;>
    simp only [CircleParameterData.orientedKernel, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  · exact parameter_kernel_eq_manuscript hm z hv
  · exact parameter_kernel_eq_manuscript hm (z - v) hv

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingFull
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

theorem SamplingPair.separated_pair {m : ℕ} {N₀ N : ℝ} {n n' : ℕ}
    (h : SamplingPair m N₀ N n n') (i j : ℤ)
    (hi : |i| ≤ (m ^ 300 : ℕ)) (hj : |j| ≤ (m ^ 300 : ℕ))
    (hij : (i, j) ≠ (0, 0)) :
    N * (m : ℝ)^1000 < |(i : ℝ) * n + (j : ℝ) * n'| := by
  apply h.separated i j hi hj
  by_cases hi0 : i = 0
  · exact Or.inr (fun hj0 => hij (by simp [hi0, hj0]))
  · exact Or.inl hi0

theorem bv_estimate {m : ℕ} (hm : 200 ≤ m) {N₀ N : ℝ} {n n' : ℕ}
    (h : SamplingPair m N₀ N n n') : BVEstimate m N₀ n n' 29 := by
  intro f g hf hg
  have hr := ScalarRectangles.scalar_bv_discrepancy m hm N₀ N h.N₀_pos h.N₀_le h.N_le
    n n' h.first_range.1 h.second_range.1 h.separated_pair f g hf hg
  simpa [bvSize, Real.rpow_neg (show (0 : ℝ) ≤ m by positivity), Real.rpow_ofNat,
    div_eq_mul_inv] using hr

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingMomentConsequences
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem eVariationOn_ofReal (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => (f x : ℂ)) s = eVariationOn f s := by
  simp only [eVariationOn, Complex.isometry_ofReal.edist_eq]

theorem bvSize_ofReal_le (f : ℝ → ℝ)
    (hf : BddAbove (Set.range (fun x => |f x|))) :
    bvSize (fun x => (f x : ℂ)) ≤
      sSup (Set.range (fun x => |f x|)) + (eVariationOn f (Icc (0 : ℝ) 1)).toReal := by
  rw [bvSize, eVariationOn_ofReal]
  apply add_le_add _ le_rfl
  apply csSup_le (Set.Nonempty.image _ (nonempty_Icc.mpr (by norm_num)))
  rintro _ ⟨x, _, rfl⟩
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    (le_csSup hf (show |f x| ∈ Set.range (fun x => |f x|) from ⟨x, rfl⟩))

theorem manuscript_kernel_abs_le {m : ℕ} (hm : 200 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) (s v : ℝ) :
    |u s v| ≤ (m : ℝ)^(13 / 5 : ℝ) := by
  have hfirst (z : ℝ) : |manuscriptKernel m z v| ≤ (m : ℝ)^(13 / 5 : ℝ) := by
    have hn : 0 ≤ manuscriptKernel m z v :=
      rawKernel_nonneg (manuscript_parameters hm).1.le
        ⟨Int.fract_nonneg z, (Int.fract_lt_one z).le⟩
    rw [abs_of_nonneg hn]
    exact manuscriptKernel_le_height hm z v
  rcases hu with rfl | rfl
  · exact hfirst s
  · exact hfirst (s - v)

theorem manuscript_kernel_measurable {m : ℕ} {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    Measurable (Function.uncurry u) := by
  rcases hu with rfl | rfl
  · exact measurable_circleKernel _ _
  · exact measurable_circleEndpoint_pair _ _

theorem manuscript_kernel_complex_bv {m : ℕ} (hm : 200 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) (s : ℝ) :
    BoundedVariationOn (fun v => (u s v : ℂ)) (Icc (0 : ℝ) 1) ∧
      0 ≤ bvSize (fun v => (u s v : ℂ)) ∧
      bvSize (fun v => (u s v : ℂ)) ≤ 11 * (m : ℝ)^10 := by
  have hk := both_kernel_estimates hm hu
  have hb : BddAbove (Set.range (fun v => |u s v|)) := by
    refine ⟨(m : ℝ)^(13 / 5 : ℝ), ?_⟩
    rintro _ ⟨v, rfl⟩
    exact manuscript_kernel_abs_le hm hu s v
  have hb' : BddAbove ((fun v => ‖(u s v : ℂ)‖) '' Icc (0 : ℝ) 1) := by
    refine ⟨(m : ℝ)^(13 / 5 : ℝ), ?_⟩
    rintro _ ⟨v, _, rfl⟩
    simpa only [Complex.norm_real, Real.norm_eq_abs] using manuscript_kernel_abs_le hm hu s v
  refine ⟨?_, ?_, (bvSize_ofReal_le (u s) hb).trans (hk.variation_coarse s)⟩
  · unfold BoundedVariationOn
    rw [eVariationOn_ofReal]
    exact hk.boundedVariation s
  · unfold bvSize
    apply add_nonneg _ ENNReal.toReal_nonneg
    exact (norm_nonneg (u s 0 : ℂ)).trans (le_csSup hb' ⟨0, by norm_num, rfl⟩)

theorem two_power_kernel_error {m : ℕ} (hm : 200 ≤ m) {N₀ C : ℝ}
    {n n' : ℕ} (hC : 0 ≤ C) (hBV : BVEstimate m N₀ n n' C)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m)
    (s : ℝ) :
    |(∫ x, u s (Int.fract ((n : ℝ) * x)) * u s (Int.fract ((n' : ℝ) * x))
        ∂UniformIntervalPhase.lambdaLaw N₀) - (∫ v in (0 : ℝ)..1, u s v)^2| ≤
      121 * C * (m : ℝ)^(-(60 : ℝ)) := by
  obtain ⟨hbv, hnonneg, hbound⟩ := manuscript_kernel_complex_bv hm hu s
  have h := hBV (fun v => (u s v : ℂ)) (fun v => (u s v : ℂ)) hbv hbv
  simp only [← Complex.ofReal_mul, integral_complex_ofReal, intervalIntegral.integral_ofReal,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  rw [← sq] at h
  refine h.trans ?_
  have hp : 0 ≤ C * (m : ℝ)^(-(80 : ℝ)) := by positivity
  calc
    C * (m : ℝ)^(-(80 : ℝ)) * bvSize (fun v => (u s v : ℂ)) *
        bvSize (fun v => (u s v : ℂ)) ≤
      C * (m : ℝ)^(-(80 : ℝ)) * (11 * (m : ℝ)^10) * (11 * (m : ℝ)^10) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hbound hp) hbound hnonneg
        (mul_nonneg hp (by positivity))
    _ = 121 * C * (m : ℝ)^(-(60 : ℝ)) := by
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      norm_num [Real.rpow_neg, Real.rpow_natCast]
      field_simp
      ring

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingPairMoments
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

lemma scalarPairLaw_probability {N : ℝ} (hN : 0 < N) :
    IsProbabilityMeasure (scalarPairLaw N) := by
  let := UniformIntervalPhase.lambdaLaw_probability N hN
  dsimp [scalarPairLaw]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma integral_scalarUnitLaw (f : ℝ → ℝ) :
    (∫ s, f s ∂scalarUnitLaw) = ∫ s in (0 : ℝ)..1, f s := by
  simp only [scalarUnitLaw, restrict_Ico_eq_restrict_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

lemma measurable_kernel_mean {m : ℕ} {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    Measurable (fun s => ∫ v in (0 : ℝ)..1, u s v) := by
  simpa only [Function.uncurry, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
    ((manuscript_kernel_measurable hu).stronglyMeasurable.integral_prod_right').measurable

lemma integrable_kernel_mean_square {m : ℕ} (hm : 200 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    Integrable (fun s => (∫ v in (0 : ℝ)..1, u s v)^2) scalarUnitLaw := by
  apply Integrable.of_bound ((measurable_kernel_mean hu).pow_const 2).aestronglyMeasurable 4
  apply Filter.Eventually.of_forall
  intro s
  obtain ⟨h0, h2⟩ := (both_kernel_estimates hm hu).average_bounds s
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith

lemma integrable_sampled_product {m : ℕ} (hm : 200 ≤ m) {N : ℝ} (hN : 0 < N)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m)
    (n n' : ℝ) :
    Integrable (fun p : ℝ × ℝ => u p.2 (Int.fract (n * p.1)) *
      u p.2 (Int.fract (n' * p.1))) (scalarPairLaw N) := by
  let := scalarPairLaw_probability hN
  have hmeas (k : ℝ) : Measurable (fun p : ℝ × ℝ => u p.2 (Int.fract (k * p.1))) :=
    (manuscript_kernel_measurable hu).comp
      (measurable_snd.prodMk (measurable_fract.comp (measurable_const.mul measurable_fst)))
  apply Integrable.of_bound ((hmeas n).mul (hmeas n')).aestronglyMeasurable
    (((m : ℝ)^(13 / 5 : ℝ))^2)
  apply Filter.Eventually.of_forall
  intro p
  change |u p.2 (Int.fract (n * p.1)) * u p.2 (Int.fract (n' * p.1))| ≤ _
  rw [abs_mul, pow_two]
  exact mul_le_mul (manuscript_kernel_abs_le hm hu p.2 _) (manuscript_kernel_abs_le hm hu p.2 _)
    (abs_nonneg _) (by positivity)

lemma scalarPair_error_transfer {N ε : ℝ} (hN : 0 < N)
    {f : ℝ × ℝ → ℝ} {g : ℝ → ℝ}
    (hf : Integrable f (scalarPairLaw N)) (hg : Integrable g scalarUnitLaw)
    (h : ∀ s, |(∫ x, f (x, s) ∂UniformIntervalPhase.lambdaLaw N) - g s| ≤ ε) :
    |(∫ p, f p ∂scalarPairLaw N) - ∫ s, g s ∂scalarUnitLaw| ≤ ε := by
  let := UniformIntervalPhase.lambdaLaw_probability N hN
  change Integrable f ((UniformIntervalPhase.lambdaLaw N).prod scalarUnitLaw) at hf
  rw [scalarPairLaw, integral_prod_symm f hf, ← integral_sub hf.integral_prod_right hg]
  have hh := norm_integral_le_of_norm_le_const
    (μ := scalarUnitLaw) (f := fun s => (∫ x, f (x, s) ∂UniformIntervalPhase.lambdaLaw N) - g s)
    (Filter.Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using h s)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hh

theorem scalarPair_offdiag_error {m : ℕ} (hm : 200 ≤ m) {N₀ N : ℝ} {n n' : ℕ}
    (h : SamplingPair m N₀ N n n')
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    |(∫ p, u p.2 (Int.fract ((n : ℝ) * p.1)) * u p.2 (Int.fract ((n' : ℝ) * p.1))
        ∂scalarPairLaw N₀) - (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, u s v)^2)| ≤
      3509 * (m : ℝ)^(-(60 : ℝ)) := by
  rw [← integral_scalarUnitLaw]
  apply scalarPair_error_transfer h.N₀_pos (integrable_sampled_product hm h.N₀_pos hu n n')
    (integrable_kernel_mean_square hm hu)
  intro s
  convert two_power_kernel_error hm (by norm_num : (0 : ℝ) ≤ 29) (bv_estimate hm h) hu s using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

theorem scalarPair_offdiag_error_fifty {m : ℕ} (hm : 200 ≤ m) {N₀ N : ℝ} {n n' : ℕ}
    (h : SamplingPair m N₀ N n n')
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    |(∫ p, u p.2 (Int.fract ((n : ℝ) * p.1)) * u p.2 (Int.fract ((n' : ℝ) * p.1))
        ∂scalarPairLaw N₀) - (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, u s v)^2)| ≤
      3509 * (m : ℝ)^(-(50 : ℝ)) := by
  apply (scalarPair_offdiag_error hm h hu).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_TrialSamplingMoments
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.TrialSampling

theorem pairLaw_representative_measurePreserving {N : ℝ} (_hN : 0 < N) :
    MeasurePreserving (fun p : ℝ × Circle => (p.1, CircleParameterData.rep p.2))
      (pairLaw N)
      ((ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))).prod
        (volume.restrict (Set.Ico (0 : ℝ) 1))) := by
  let ν : Measure ℝ := ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))
  let : IsProbabilityMeasure ν :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) _hN)
  let : IsProbabilityMeasure circleMeasure := ⟨by
    simp [circleMeasure, AddCircle.measure_univ]⟩
  exact (MeasurePreserving.id ν).prod CocycleSupport.measurePreserving_circleRepresentative

theorem integral_pairLaw_representative {N : ℝ} (hN : 0 < N) (f : ℝ × ℝ → ℝ) :
    (∫ p, f (p.1, CircleParameterData.rep p.2) ∂pairLaw N) =
      ∫ p, f p ∂(ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))).prod
        (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
  have hr : MeasurableEmbedding (CircleParameterData.rep : Circle → ℝ) := by
    exact (MeasurableEmbedding.subtype_coe measurableSet_Ico).comp
      (AddCircle.measurableEquivIco (1 : ℝ) 0).measurableEmbedding
  exact (pairLaw_representative_measurePreserving hN).integral_comp
    (MeasurableEmbedding.id.prodMap hr) f

end Invariant233.TrialSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_TrialSamplingScalar
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.TrialSampling

theorem coordinateSample_eq_scalar {m : ℕ} (hm : 200 ≤ m)
    (endpoint : Bool) (n : ℕ) (p : ℝ × Circle) :
    coordinateSample m endpoint n p =
      if endpoint then ScalarSampling.manuscriptEndpointKernel m (CircleParameterData.rep p.2)
        (Int.fract ((n : ℝ) * p.1))
      else ScalarSampling.manuscriptKernel m (CircleParameterData.rep p.2)
        (Int.fract ((n : ℝ) * p.1)) := by
  exact ScalarSampling.parameter_orientedKernel_eq hm endpoint _
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

theorem coordinateIdeal_eq_scalar {m : ℕ} (hm : 200 ≤ m)
    (endpoint : Bool) (p : ℝ × Circle) :
    coordinateIdeal m endpoint p =
      ∫ v in (0 : ℝ)..1,
        if endpoint then ScalarSampling.manuscriptEndpointKernel m (CircleParameterData.rep p.2) v
        else ScalarSampling.manuscriptKernel m (CircleParameterData.rep p.2) v := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro v hv
  exact ScalarSampling.parameter_orientedKernel_eq hm endpoint _ ⟨hv.1.le, hv.2⟩

theorem integral_coordinate_moment_eq_scalar {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (endpoint : Bool)
    (F : (ℕ → ℝ) → ℝ → ℝ) :
    (∫ p, F (fun n => coordinateSample m endpoint n p) (coordinateIdeal m endpoint p)
      ∂pairLaw N) =
      ∫ p : ℝ × ℝ,
        F (fun n => if endpoint then ScalarSampling.manuscriptEndpointKernel m p.2
            (Int.fract ((n : ℝ) * p.1))
          else ScalarSampling.manuscriptKernel m p.2 (Int.fract ((n : ℝ) * p.1)))
          (∫ v in (0 : ℝ)..1,
            if endpoint then ScalarSampling.manuscriptEndpointKernel m p.2 v
            else ScalarSampling.manuscriptKernel m p.2 v)
        ∂(UniformIntervalPhase.lambdaLaw N).prod
          (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
  simp_rw [coordinateSample_eq_scalar hm, coordinateIdeal_eq_scalar hm]
  rw [UniformIntervalPhase.lambdaLaw_eq_cond N hN]
  exact integral_pairLaw_representative hN (fun p =>
    F (fun n => if endpoint then ScalarSampling.manuscriptEndpointKernel m p.2
          (Int.fract ((n : ℝ) * p.1))
        else ScalarSampling.manuscriptKernel m p.2 (Int.fract ((n : ℝ) * p.1)))
      (∫ v in (0 : ℝ)..1,
        if endpoint then ScalarSampling.manuscriptEndpointKernel m p.2 v
        else ScalarSampling.manuscriptKernel m p.2 v))

end Invariant233.TrialSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_TrialSamplingIdealMoments
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.TrialSampling

theorem integral_coordinateIdeal_comp_eq_scalar {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (endpoint : Bool) (f : ℝ → ℝ) :
    (∫ p, f (coordinateIdeal m endpoint p) ∂pairLaw N) =
      ∫ z in (0 : ℝ)..1, f (∫ v in (0 : ℝ)..1,
        if endpoint then ScalarSampling.manuscriptEndpointKernel m z v
        else ScalarSampling.manuscriptKernel m z v) := by
  let := UniformIntervalPhase.lambdaLaw_probability N hN
  rw [integral_coordinate_moment_eq_scalar hm hN endpoint (fun _ a => f a)]
  rw [integral_fun_snd (fun z : ℝ => f (∫ v in (0 : ℝ)..1,
    if endpoint then ScalarSampling.manuscriptEndpointKernel m z v
    else ScalarSampling.manuscriptKernel m z v))]
  simp only [probReal_univ, one_smul]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_Ico_eq_integral_Ioc

end Invariant233.TrialSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_TrialSamplingActualMoments
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace Invariant233.TrialSampling

private theorem scalar_orientation_mem (m : ℕ) (endpoint : Bool) :
    (fun z v => if endpoint then ScalarSampling.manuscriptEndpointKernel m z v
      else ScalarSampling.manuscriptKernel m z v) = ScalarSampling.manuscriptKernel m ∨
    (fun z v => if endpoint then ScalarSampling.manuscriptEndpointKernel m z v
      else ScalarSampling.manuscriptKernel m z v) = ScalarSampling.manuscriptEndpointKernel m := by
  cases endpoint <;> simp

theorem coordinateSample_offdiag_error_oai {m : ℕ} (hm : 200 ≤ m)
    {N₀ N : ℝ} {n n' : ℕ} (h : ScalarSampling.SamplingPair m N₀ N n n')
    (endpoint : Bool) :
    |(∫ p, coordinateSample m endpoint n p * coordinateSample m endpoint n' p ∂pairLaw N₀) -
      (∫ p, (coordinateIdeal m endpoint p) ^ 2 ∂pairLaw N₀)| ≤
      3509 * (m : ℝ) ^ (-(50 : ℝ)) := by
  rw [integral_coordinate_moment_eq_scalar hm h.N₀_pos endpoint (fun a _ => a n * a n'),
    integral_coordinateIdeal_comp_eq_scalar hm h.N₀_pos endpoint (fun a => a ^ 2)]
  simpa only [ScalarSampling.scalarPairLaw, ScalarSampling.scalarUnitLaw] using
    ScalarSampling.scalarPair_offdiag_error_fifty hm h (scalar_orientation_mem m endpoint)

end Invariant233.TrialSampling

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.TrialSampling.coordinateSample_offdiag_error_oai := @OAI.Invariant233.TrialSampling.coordinateSample_offdiag_error_oai
