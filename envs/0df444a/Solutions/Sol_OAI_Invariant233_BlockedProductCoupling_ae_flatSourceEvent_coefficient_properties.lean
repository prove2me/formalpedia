-- Prove2me | solution 1 for OAI.Invariant233.BlockedProductCoupling.ae_flatSourceEvent_coefficient_properties
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:32:12.048203+00:00
-- url     : https://prove2.me/submissions/8fa11560-bd31-42a3-8bb5-b606e699fb0e

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
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
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CouplingMarginalBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Invariant233.CouplingMarginalBounds

lemma rho_div_width_le {κ m w : ℝ} (hκ : 0 ≤ κ)
    (hm : 0 < m) (hw : 1 / m ≤ w) : rho κ m w / w ≤ κ := by
  exact (div_le_iff₀ (width_pos hm hw)).2 (rho_le_mul_width hκ hm hw)

lemma rho_sq_div_width {κ m w : ℝ} (hm : 0 < m) (hw : 0 < w) :
    (rho κ m w) ^ 2 / w = κ ^ 2 / m := by
  unfold rho
  rw [mul_pow, Real.sq_sqrt (div_nonneg hw.le hm.le)]
  field_simp

lemma marginal_density_bounds {κ m a b t u₁ u₂ u₃ u₄ v : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)
    (hu₁ : 0 ≤ u₁ ∧ u₁ ≤ 2 / a) (hu₂ : 0 ≤ u₂ ∧ u₂ ≤ 2 / a)
    (hu₃ : 0 ≤ u₃ ∧ u₃ ≤ 2 / b) (hu₄ : 0 ≤ u₄ ∧ u₄ ≤ 2 / b)
    (hv : 0 ≤ v ∧ v ≤ m) :
    let h := diagonalMass κ m a b t + rho κ m a * u₁ + rho κ m a * u₂ +
      rho κ m b * u₃ + rho κ m b * u₄ + (t / m) * v
    49 / 50 ≤ h ∧ h ≤ 2 + 8 * κ ∧ h < 10 := by
  dsimp only
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hra0 := rho_nonneg (m := m) (w := a) hκ0
  have hrb0 := rho_nonneg (m := m) (w := b) hκ0
  have hq := diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht
  have hra := rho_div_width_le hκ0 hm0 ha
  have hrb := rho_div_width_le hκ0 hm0 hb
  have hu₁' : rho κ m a * u₁ ≤ 2 * κ := by
    calc
      _ ≤ rho κ m a * (2 / a) := mul_le_mul_of_nonneg_left hu₁.2 hra0
      _ = 2 * (rho κ m a / a) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hra (by norm_num)
  have hu₂' : rho κ m a * u₂ ≤ 2 * κ := by
    calc
      _ ≤ rho κ m a * (2 / a) := mul_le_mul_of_nonneg_left hu₂.2 hra0
      _ = 2 * (rho κ m a / a) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hra (by norm_num)
  have hu₃' : rho κ m b * u₃ ≤ 2 * κ := by
    calc
      _ ≤ rho κ m b * (2 / b) := mul_le_mul_of_nonneg_left hu₃.2 hrb0
      _ = 2 * (rho κ m b / b) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrb (by norm_num)
  have hu₄' : rho κ m b * u₄ ≤ 2 * κ := by
    calc
      _ ≤ rho κ m b * (2 / b) := mul_le_mul_of_nonneg_left hu₄.2 hrb0
      _ = 2 * (rho κ m b / b) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrb (by norm_num)
  have htm0 := div_nonneg ht0 hm0.le
  have hv' : (t / m) * v ≤ t := by
    calc
      _ ≤ (t / m) * m := mul_le_mul_of_nonneg_left hv.2 htm0
      _ = t := div_mul_cancel₀ _ hm0.ne'
  have hlow₁ := mul_nonneg hra0 hu₁.1
  have hlow₂ := mul_nonneg hra0 hu₂.1
  have hlow₃ := mul_nonneg hrb0 hu₃.1
  have hlow₄ := mul_nonneg hrb0 hu₄.1
  have hlowv := mul_nonneg htm0 hv.1
  constructor
  · linarith [hq.1]
  constructor
  · linarith [hq.2]
  · linarith [hq.2]

lemma integral_sq_sum_le {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {μ : Measure Ω} {f : I → Ω → ℝ} (hf : ∀ i, MemLp (f i) 2 μ) :
    (∫ ω, (∑ i, f i ω) ^ 2 ∂μ) ≤
      (Fintype.card I : ℝ) * ∑ i, ∫ ω, (f i ω) ^ 2 ∂μ := by
  classical
  have hsum : MemLp (fun ω => ∑ i, f i ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ => hf i)
  have hsq : Integrable (fun ω => ∑ i, (f i ω) ^ 2) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hf i).integrable_sq)
  calc
    _ ≤ ∫ ω, (Fintype.card I : ℝ) * ∑ i, (f i ω) ^ 2 ∂μ := by
      apply integral_mono hsum.integrable_sq (hsq.const_mul _)
      intro ω
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i => f i ω))
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum]
      intro i _
      exact (hf i).integrable_sq

lemma integral_sq_weighted_sum_le {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {μ : Measure Ω} {f : I → Ω → ℝ} (hf : ∀ i, MemLp (f i) 2 μ)
    (p : I → ℝ) :
    (∫ ω, (∑ i, p i * f i ω) ^ 2 ∂μ) ≤
      (Fintype.card I : ℝ) * ∑ i, (p i) ^ 2 * ∫ ω, (f i ω) ^ 2 ∂μ := by
  have h := integral_sq_sum_le (fun i => (hf i).const_mul (p i))
  simpa only [mul_pow, integral_const_mul] using h

lemma uniformDensity_memLp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω} (hs : MeasurableSet s)
    (p : ℝ≥0∞) : MemLp (uniformDensity μ s) p μ := by
  exact memLp_indicator_const p hs _ (Or.inr (measure_ne_top μ s))

lemma uniformDensity_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    ∫ ω, uniformDensity μ s ω ∂μ = 1 := by
  rw [uniformDensity, integral_indicator_const _ hs, smul_eq_mul]
  exact mul_inv_cancel₀ hpos.ne'

lemma uniformDensity_sq_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    ∫ ω, (uniformDensity μ s ω) ^ 2 ∂μ = (μ.real s)⁻¹ := by
  have hsq : (fun ω => (uniformDensity μ s ω) ^ 2) =
      s.indicator (fun _ => ((μ.real s)⁻¹) ^ 2) := by
    ext ω
    by_cases hω : ω ∈ s <;> simp [uniformDensity, hω]
  rw [hsq, integral_indicator_const _ hs, smul_eq_mul]
  field_simp

lemma uniformDensity_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Set Ω}
    (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    ∫ ω, (uniformDensity μ s ω - 1) ^ 2 ∂μ = (μ.real s)⁻¹ - 1 := by
  have hu := uniformDensity_memLp (μ := μ) hs 2
  have hui : Integrable (uniformDensity μ s) μ := hu.integrable (by norm_num)
  have hfun : (fun ω => (uniformDensity μ s ω - 1) ^ 2) =
      fun ω => (uniformDensity μ s ω) ^ 2 - 2 * uniformDensity μ s ω + 1 := by
    ext ω
    ring
  have hsub : Integrable (fun ω => (uniformDensity μ s ω) ^ 2 - 2 * uniformDensity μ s ω) μ :=
    hu.integrable_sq.sub (hui.const_mul 2)
  rw [hfun, integral_add hsub (integrable_const 1),
    integral_sub hu.integrable_sq (hui.const_mul 2), integral_const_mul,
    uniformDensity_sq_integral hs hpos, uniformDensity_integral hs hpos]
  simp
  ring

lemma uniformDensity_variance_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Set Ω}
    (hs : MeasurableSet s) {w : ℝ} (hw : 0 < w) (hlen : w / 2 ≤ μ.real s) :
    ∫ ω, (uniformDensity μ s ω - 1) ^ 2 ∂μ ≤ 2 / w := by
  have hpos : 0 < μ.real s := lt_of_lt_of_le (by positivity) hlen
  rw [uniformDensity_variance hs hpos]
  have hinv : (μ.real s)⁻¹ ≤ 2 / w := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hpos hw).2
    linarith
  linarith

lemma five_component_energy_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Fin 5 → Ω → ℝ} (hf : ∀ i, MemLp (f i) 2 μ)
    {κ m a b t : ℝ} (hm : 0 < m) (ha : 0 < a) (hb : 0 < b)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)
    (henergy : ∀ i, (∫ ω, (f i ω) ^ 2 ∂μ) ≤ componentVarianceBounds m a b i) :
    (∫ ω, (∑ i, componentProbabilities κ m a b t i * f i ω) ^ 2 ∂μ) ≤
      20 * (2 * κ ^ 2 / m + t / m) := by
  have hbound := integral_sq_weighted_sum_le hf (componentProbabilities κ m a b t)
  have hsum : (∑ i, (componentProbabilities κ m a b t i) ^ 2 *
      ∫ ω, (f i ω) ^ 2 ∂μ) ≤
      ∑ i, (componentProbabilities κ m a b t i) ^ 2 *
        componentVarianceBounds m a b i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (henergy i) (sq_nonneg _)
  have hcalc : (∑ i, (componentProbabilities κ m a b t i) ^ 2 *
      componentVarianceBounds m a b i) = 8 * κ ^ 2 / m + t ^ 2 / m := by
    simp only [componentProbabilities, componentVarianceBounds, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    have hra := rho_sq_div_width (κ := κ) hm ha
    have hrb := rho_sq_div_width (κ := κ) hm hb
    have htag : (t / m) ^ 2 * m = t ^ 2 / m := by field_simp
    rw [htag]
    simp only [div_eq_mul_inv] at hra hrb ⊢
    nlinarith
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have htdiv : t ^ 2 / m ≤ t / m := (div_le_div_iff_of_pos_right hm).2 ht2
  have htm : 0 ≤ t / m := div_nonneg ht0 hm.le
  norm_num only [Fintype.card_fin] at hbound
  calc
    _ ≤ 5 * (∑ i, (componentProbabilities κ m a b t i) ^ 2 *
        componentVarianceBounds m a b i) :=
      hbound.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))
    _ = 5 * (8 * κ ^ 2 / m + t ^ 2 / m) := by rw [hcalc]
    _ ≤ _ := by
      simp only [div_eq_mul_inv] at htdiv htm ⊢
      nlinarith

end Invariant233.CouplingMarginalBounds

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CouplingMixture
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace Invariant233.CouplingMixture

variable {X I : Type*} [MeasurableSpace X] [Fintype I]

lemma diagonal_fst (μ : Measure X) : (diagonal μ).fst = μ := by
  simpa [diagonal] using
    (Measure.fst_map_prodMk (μ := μ) (X := id) (Y := id) measurable_id)

lemma diagonal_snd (μ : Measure X) : (diagonal μ).snd = μ := by
  simpa [diagonal] using
    (Measure.snd_map_prodMk (μ := μ) (X := id) (Y := id) measurable_id)

lemma fst_finsetSum {J : Type*} (s : Finset J) (μ : J → Measure (X × X)) :
    (∑ i ∈ s, μ i).fst = ∑ i ∈ s, (μ i).fst := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma snd_finsetSum {J : Type*} (s : Finset J) (μ : J → Measure (X × X)) :
    (∑ i ∈ s, μ i).snd = ∑ i ∈ s, (μ i).snd := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma mixture_fst (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (v i)] :
    (mixture μ q p u v).fst = q • μ + ∑ i, p i • u i := by
  unfold mixture
  rw [Measure.fst_add, fst_finsetSum]
  simp only [Measure.fst, Measure.map_smul,
    Measure.map_fst_prod, measure_univ, one_smul]
  rw [← Measure.fst, diagonal_fst]

lemma mixture_snd (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)] :
    (mixture μ q p u v).snd = q • μ + ∑ i, p i • v i := by
  unfold mixture
  rw [Measure.snd_add, snd_finsetSum]
  simp only [Measure.snd, Measure.map_smul,
    Measure.map_snd_prod, measure_univ, one_smul]
  rw [← Measure.snd, diagonal_snd]

lemma withDensity_finite_mixture (μ : Measure X) (q : ℝ≥0∞)
    (p : I → ℝ≥0∞) (g : I → X → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    μ.withDensity (fun x => q + ∑ i, p i * g i x) =
      q • μ + ∑ i, p i • μ.withDensity (g i) := by
  classical
  have hsum : μ.withDensity (fun x => ∑ i, p i * g i x) =
      ∑ i, p i • μ.withDensity (g i) := by
    have hfin : ∀ s : Finset I, μ.withDensity (fun x => ∑ i ∈ s, p i * g i x) =
        ∑ i ∈ s, p i • μ.withDensity (g i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        rw [show (fun x => p a * g a x + ∑ i ∈ s, p i * g i x) =
          (fun x => p a * g a x) + (fun x => ∑ i ∈ s, p i * g i x) from rfl,
          withDensity_add_left (show Measurable (fun x => p a * g a x) from measurable_const.mul (hg a)), ih]
        congr 1
        exact withDensity_smul (p a) (hg a)
    exact hfin Finset.univ
  rw [show (fun x => q + ∑ i, p i * g i x) =
    (fun _ => q) + (fun x => ∑ i, p i * g i x) from rfl,
    withDensity_add_left measurable_const, withDensity_const, hsum]

lemma cond_eq_withDensity_uniformDensity {μ : Measure X} [IsFiniteMeasure μ]
    {s : Set X} (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    μ[|s] = μ.withDensity (fun x =>
      ENNReal.ofReal (CouplingMarginalBounds.uniformDensity μ s x)) := by
  have hc : ENNReal.ofReal ((μ.real s)⁻¹) = (μ s)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hpos, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ s)]
  have hfun : (fun x => ENNReal.ofReal (CouplingMarginalBounds.uniformDensity μ s x)) =
      s.indicator (fun _ => (μ s)⁻¹) := by
    ext x
    by_cases hx : x ∈ s <;> simp [CouplingMarginalBounds.uniformDensity, hx, hc]
  rw [hfun, withDensity_indicator hs, withDensity_const]
  rfl

omit [MeasurableSpace X] in
lemma ofReal_mixture_density (q : ℝ) (p : I → ℝ) (g : I → X → ℝ)
    (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i) (hg : ∀ i x, 0 ≤ g i x) (x : X) :
    ENNReal.ofReal (q + ∑ i, p i * g i x) =
      ENNReal.ofReal q + ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (g i x) := by
  rw [ENNReal.ofReal_add hq (Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (hg i x))),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hp i) (hg i x))]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => ENNReal.ofReal_mul (hp i))

lemma mixture_fst_real_density (μ : Measure X) (q : ℝ) (p : I → ℝ)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (v i)]
    (g : I → X → ℝ) (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgm : ∀ i, Measurable (g i))
    (hu : ∀ i, u i = μ.withDensity (fun x => ENNReal.ofReal (g i x))) :
    (mixture μ (ENNReal.ofReal q) (fun i => ENNReal.ofReal (p i)) u v).fst =
      μ.withDensity (fun x => ENNReal.ofReal (q + ∑ i, p i * g i x)) := by
  rw [mixture_fst]
  simp_rw [hu, ofReal_mixture_density q p g hq hp hg0]
  exact (withDensity_finite_mixture μ _ _ _ (fun i => (hgm i).ennreal_ofReal)).symm

lemma mixture_snd_real_density (μ : Measure X) (q : ℝ) (p : I → ℝ)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)]
    (g : I → X → ℝ) (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgm : ∀ i, Measurable (g i))
    (hv : ∀ i, v i = μ.withDensity (fun x => ENNReal.ofReal (g i x))) :
    (mixture μ (ENNReal.ofReal q) (fun i => ENNReal.ofReal (p i)) u v).snd =
      μ.withDensity (fun x => ENNReal.ofReal (q + ∑ i, p i * g i x)) := by
  rw [mixture_snd]
  simp_rw [hv, ofReal_mixture_density q p g hq hp hg0]
  exact (withDensity_finite_mixture μ _ _ _ (fun i => (hgm i).ennreal_ofReal)).symm

end Invariant233.CouplingMixture

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_OneCoordinateCoupling
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.OneCoordinateCoupling

open CouplingMarginalBounds CouplingMixture

lemma baseLaw_eq_restrict : baseLaw = volume.restrict (Ico (0 : ℝ) 1) := by
  simp [baseLaw, intervalLaw, ProbabilityTheory.cond, Real.volume_Ico]

lemma interval_subset_unit {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    Ico a b ⊆ Ico (0 : ℝ) 1 := by
  intro x hx
  exact ⟨ha.trans hx.1, hx.2.trans_le hb⟩

lemma baseLaw_interval_measure {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    baseLaw.real (Ico a b) = b - a := by
  rw [measureReal_def, baseLaw_eq_restrict, Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.mpr (interval_subset_unit ha hb), Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma intervalLaw_eq_base_cond {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    intervalLaw a b = baseLaw[|Ico a b] := by
  rw [baseLaw_eq_restrict]
  simp only [intervalLaw, ProbabilityTheory.cond,
    Measure.restrict_apply measurableSet_Ico,
    Measure.restrict_restrict measurableSet_Ico,
    inter_eq_left.mpr (interval_subset_unit ha hb)]

lemma intervalLaw_eq_base_withDensity {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    intervalLaw a b = baseLaw.withDensity (fun x =>
      ENNReal.ofReal (uniformDensity baseLaw (Ico a b) x)) := by
  rw [intervalLaw_eq_base_cond ha hb]
  apply cond_eq_withDensity_uniformDensity measurableSet_Ico
  rw [baseLaw_interval_measure ha hb hab.le]
  exact sub_pos.mpr hab

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_OneCoordinateDensity
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.OneCoordinateCoupling

open CouplingMarginalBounds CouplingMixture

lemma intervalDensity_measurable (a b : ℝ) : Measurable (intervalDensity a b) :=
  measurable_const.indicator measurableSet_Ico

lemma intervalDensity_nonneg (a b x : ℝ) : 0 ≤ intervalDensity a b x := by
  by_cases hx : x ∈ Ico a b
  · simp [intervalDensity, uniformDensity, hx, inv_nonneg.mpr (measureReal_nonneg)]
  · simp [intervalDensity, uniformDensity, hx]

lemma intervalDensity_memLp (a b : ℝ) (p : ℝ≥0∞) :
    MemLp (intervalDensity a b) p baseLaw :=
  uniformDensity_memLp measurableSet_Ico p

lemma intervalDensity_integral {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    (∫ x, intervalDensity a b x ∂baseLaw) = 1 := by
  apply uniformDensity_integral measurableSet_Ico
  rw [baseLaw_interval_measure ha hb hab.le]
  exact sub_pos.mpr hab

lemma intervalDensity_variance {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    (∫ x, (intervalDensity a b x - 1) ^ 2 ∂baseLaw) = (b - a)⁻¹ - 1 := by
  have hpos : 0 < baseLaw.real (Ico a b) := by
    rw [baseLaw_interval_measure ha hb hab.le]
    exact sub_pos.mpr hab
  rw [intervalDensity, uniformDensity_variance measurableSet_Ico hpos,
    baseLaw_interval_measure ha hb hab.le]

lemma intervalDensity_le_inv_length {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) (x : ℝ) :
    intervalDensity a b x ≤ (b - a)⁻¹ := by
  by_cases hx : x ∈ Ico a b
  · simp [intervalDensity, uniformDensity, hx, baseLaw_interval_measure ha hb hab.le]
  · simp [intervalDensity, uniformDensity, hx, inv_nonneg.mpr (sub_nonneg.mpr hab.le)]

lemma intervalDensity_le_width {a b w : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hw : 0 < w) (hlen : w / 2 ≤ b - a) (x : ℝ) :
    intervalDensity a b x ≤ 2 / w := by
  have hab : a < b := by linarith
  apply (intervalDensity_le_inv_length ha hb hab x).trans
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (sub_pos.mpr hab) hw).2
  linarith

lemma leftLaw_eq_withDensity {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    leftLaw m a b i = baseLaw.withDensity (fun x => ENNReal.ofReal (leftDensity m a b i x)) := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [leftLaw, leftDensity] <;>
    apply intervalLaw_eq_base_withDensity <;> linarith

lemma rightLaw_eq_withDensity {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    rightLaw m a b i = baseLaw.withDensity (fun x => ENNReal.ofReal (rightDensity m a b i x)) := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [rightLaw, rightDensity] <;>
    apply intervalLaw_eq_base_withDensity <;> linarith

lemma leftDensity_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) (x : ℝ) :
    0 ≤ leftDensity m a b i x ∧ leftDensity m a b i x ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  constructor
  · fin_cases i <;> exact intervalDensity_nonneg _ _ _
  · fin_cases i <;> simp only [leftDensity, componentVarianceBounds]
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · simpa using intervalDensity_le_inv_length (a := 0) (b := 1 / m)
        (by norm_num) (by linarith) hinv0 x

lemma rightDensity_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) (x : ℝ) :
    0 ≤ rightDensity m a b i x ∧ rightDensity m a b i x ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  constructor
  · fin_cases i <;> exact intervalDensity_nonneg _ _ _
  · fin_cases i <;> simp only [rightDensity, componentVarianceBounds]
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · simpa using intervalDensity_le_inv_length (a := 1 - 1 / m) (b := 1)
        (by linarith) (by norm_num) (by linarith) x

lemma pairLaw_fst_density {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (pairLaw κ m a b t).fst = baseLaw.withDensity
      (fun x => ENNReal.ofReal (leftMarginalDensity κ m a b t x)) := by
  have hm0 : 0 < m := by linarith
  have hm2 : 2 ≤ m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure hm2 ha0 ha' hb0 hb'
  apply mixture_fst_real_density
  · exact le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  · exact componentProbabilities_nonneg hκ0 hm0 ht0
  · intro i x
    exact (leftDensity_bound hm2 ha0 ha' hb0 hb' i x).1
  · intro i
    fin_cases i <;> exact intervalDensity_measurable _ _
  · exact leftLaw_eq_withDensity hm2 ha0 ha' hb0 hb'

lemma pairLaw_snd_density {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (pairLaw κ m a b t).snd = baseLaw.withDensity
      (fun x => ENNReal.ofReal (rightMarginalDensity κ m a b t x)) := by
  have hm0 : 0 < m := by linarith
  have hm2 : 2 ≤ m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (leftLaw m a b i) :=
    leftLaw_isProbabilityMeasure hm0 ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure hm2 ha0 ha' hb0 hb'
  apply mixture_snd_real_density
  · exact le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  · exact componentProbabilities_nonneg hκ0 hm0 ht0
  · intro i x
    exact (rightDensity_bound hm2 ha0 ha' hb0 hb' i x).1
  · intro i
    fin_cases i <;> exact intervalDensity_measurable _ _
  · exact rightLaw_eq_withDensity hm2 ha0 ha' hb0 hb'

lemma leftMarginalDensity_bounds {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) (x : ℝ) :
    49 / 50 ≤ leftMarginalDensity κ m a b t x ∧
      leftMarginalDensity κ m a b t x ≤ 2 + 8 * κ ∧
      leftMarginalDensity κ m a b t x < 10 := by
  have hm0 : 0 < m := by linarith
  have hd := leftDensity_bound (m := m) (by linarith) (width_pos hm0 ha) ha'
    (width_pos hm0 hb) hb'
  have h := marginal_density_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht
    (hd 0 x) (hd 1 x) (hd 2 x) (hd 3 x) (hd 4 x)
  simpa [leftMarginalDensity, componentProbabilities, Fin.sum_univ_succ, leftDensity, add_assoc] using h

lemma rightMarginalDensity_bounds {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) (x : ℝ) :
    49 / 50 ≤ rightMarginalDensity κ m a b t x ∧
      rightMarginalDensity κ m a b t x ≤ 2 + 8 * κ ∧
      rightMarginalDensity κ m a b t x < 10 := by
  have hm0 : 0 < m := by linarith
  have hd := rightDensity_bound (m := m) (by linarith) (width_pos hm0 ha) ha'
    (width_pos hm0 hb) hb'
  have h := marginal_density_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht
    (hd 0 x) (hd 1 x) (hd 2 x) (hd 3 x) (hd 4 x)
  simpa [rightMarginalDensity, componentProbabilities, Fin.sum_univ_succ, rightDensity, add_assoc] using h

lemma intervalDensity_variance_le_width {a b w : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hw : 0 < w) (hlen : w / 2 ≤ b - a) :
    (∫ x, (intervalDensity a b x - 1) ^ 2 ∂baseLaw) ≤ 2 / w := by
  apply uniformDensity_variance_le measurableSet_Ico hw
  rw [baseLaw_interval_measure ha hb (by linarith)]
  exact hlen

lemma leftDensity_variance_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    (∫ x, (leftDensity m a b i x - 1) ^ 2 ∂baseLaw) ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [leftDensity, componentVarianceBounds]
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · change (∫ x, (intervalDensity 0 (1 / m) x - 1) ^ 2 ∂baseLaw) ≤ m
    rw [intervalDensity_variance (by norm_num) (by linarith) hinv0]
    simp

lemma rightDensity_variance_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    (∫ x, (rightDensity m a b i x - 1) ^ 2 ∂baseLaw) ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [rightDensity, componentVarianceBounds]
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · apply intervalDensity_variance_le_width <;> linarith
  · change (∫ x, (intervalDensity (1 - 1 / m) 1 x - 1) ^ 2 ∂baseLaw) ≤ m
    rw [intervalDensity_variance (by linarith) (by norm_num) (by linarith)]
    simp

lemma marginalDensity_sub_one (κ m a b t : ℝ) (d : Fin 5 → ℝ) :
    diagonalMass κ m a b t + ∑ i, componentProbabilities κ m a b t i * d i - 1 =
      ∑ i, componentProbabilities κ m a b t i * (d i - 1) := by
  simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, diagonalMass]
  ring

lemma leftMarginalDensity_energy {κ m a b t : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (∫ x, (leftMarginalDensity κ m a b t x - 1) ^ 2 ∂baseLaw) ≤
      20 * (2 * κ ^ 2 / m + t / m) := by
  have hf : ∀ i, MemLp (fun x => leftDensity m a b i x - 1) 2 baseLaw := by
    intro i
    fin_cases i <;> exact (intervalDensity_memLp _ _ 2).sub (memLp_const 1)
  have h := five_component_energy_bound hf (κ := κ) (by linarith) ha0 hb0 ht0 ht
    (leftDensity_variance_bound hm ha0 ha1 hb0 hb1)
  simpa only [leftMarginalDensity, marginalDensity_sub_one] using h

lemma rightMarginalDensity_energy {κ m a b t : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (∫ x, (rightMarginalDensity κ m a b t x - 1) ^ 2 ∂baseLaw) ≤
      20 * (2 * κ ^ 2 / m + t / m) := by
  have hf : ∀ i, MemLp (fun x => rightDensity m a b i x - 1) 2 baseLaw := by
    intro i
    fin_cases i <;> exact (intervalDensity_memLp _ _ 2).sub (memLp_const 1)
  have h := five_component_energy_bound hf (κ := κ) (by linarith) ha0 hb0 ht0 ht
    (rightDensity_variance_bound hm ha0 ha1 hb0 hb1)
  simpa only [rightMarginalDensity, marginalDensity_sub_one] using h

lemma leftMarginalDensity_memLp (κ m a b t : ℝ) :
    MemLp (leftMarginalDensity κ m a b t) 2 baseLaw := by
  apply (memLp_const (diagonalMass κ m a b t)).add
  apply memLp_finsetSum Finset.univ
  intro i _
  apply MemLp.const_mul
  fin_cases i <;> exact intervalDensity_memLp _ _ 2

lemma rightMarginalDensity_memLp (κ m a b t : ℝ) :
    MemLp (rightMarginalDensity κ m a b t) 2 baseLaw := by
  apply (memLp_const (diagonalMass κ m a b t)).add
  apply memLp_finsetSum Finset.univ
  intro i _
  apply MemLp.const_mul
  fin_cases i <;> exact intervalDensity_memLp _ _ 2

lemma leftMarginalDensity_integral {κ m a b t : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) :
    (∫ x, leftMarginalDensity κ m a b t x ∂baseLaw) = 1 := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  have hi : ∀ i, Integrable (fun x => componentProbabilities κ m a b t i * leftDensity m a b i x) baseLaw := by
    intro i
    apply Integrable.const_mul
    fin_cases i <;> exact (intervalDensity_memLp _ _ 2).integrable (by first | (simp; all_goals first | (norm_num; done) | rfl | decide) | (norm_num; done) | norm_num)
  have hmean : ∀ i, (∫ x, leftDensity m a b i x ∂baseLaw) = 1 := by
    intro i
    fin_cases i <;> apply intervalDensity_integral <;> linarith
  have hs := integrable_finsetSum Finset.univ (fun i _ => hi i)
  change (∫ x, diagonalMass κ m a b t + ∑ i, componentProbabilities κ m a b t i * leftDensity m a b i x ∂baseLaw) = 1
  rw [integral_add (integrable_const _) hs,
    integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_const, probReal_univ, one_smul,
    integral_const_mul, hmean, mul_one]
  simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, diagonalMass]
  ring

lemma rightMarginalDensity_integral {κ m a b t : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) :
    (∫ x, rightMarginalDensity κ m a b t x ∂baseLaw) = 1 := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  have hi : ∀ i, Integrable (fun x => componentProbabilities κ m a b t i * rightDensity m a b i x) baseLaw := by
    intro i
    apply Integrable.const_mul
    fin_cases i <;> exact (intervalDensity_memLp _ _ 2).integrable (by first | (simp; all_goals first | (norm_num; done) | rfl | decide) | (norm_num; done) | norm_num)
  have hmean : ∀ i, (∫ x, rightDensity m a b i x ∂baseLaw) = 1 := by
    intro i
    fin_cases i <;> apply intervalDensity_integral <;> linarith
  have hs := integrable_finsetSum Finset.univ (fun i _ => hi i)
  change (∫ x, diagonalMass κ m a b t + ∑ i, componentProbabilities κ m a b t i * rightDensity m a b i x ∂baseLaw) = 1
  rw [integral_add (integrable_const _) hs,
    integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_const, probReal_univ, one_smul,
    integral_const_mul, hmean, mul_one]
  simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, diagonalMass]
  ring

lemma pairLaw_fst_le_ten {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (pairLaw κ m a b t).fst ≤ (10 : ℝ≥0∞) • baseLaw := by
  rw [pairLaw_fst_density hκ0 hκ hm ha ha' hb hb' ht0 ht, ← withDensity_const]
  apply withDensity_mono
  apply Filter.Eventually.of_forall
  intro x
  exact (ENNReal.ofReal_le_ofReal
    (leftMarginalDensity_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht x).2.2.le).trans_eq (by norm_num)

lemma pairLaw_snd_le_ten {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) :
    (pairLaw κ m a b t).snd ≤ (10 : ℝ≥0∞) • baseLaw := by
  rw [pairLaw_snd_density hκ0 hκ hm ha ha' hb hb' ht0 ht, ← withDensity_const]
  apply withDensity_mono
  apply Filter.Eventually.of_forall
  intro x
  exact (ENNReal.ofReal_le_ofReal
    (rightMarginalDensity_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht x).2.2.le).trans_eq (by norm_num)

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConcreteTagEvent
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace Invariant233.OneCoordinateCoupling

open CouplingMixture CouplingMarginalBounds

theorem labelledLaw_left_map (κ m a b t : ℝ) :
    (labelledLaw κ m a b t).map (fun z => z.2.1) = (pairLaw κ m a b t).fst := by
  change _ = (pairLaw κ m a b t).map Prod.fst
  rw [← labelledLaw_map_snd, Measure.map_map measurable_fst measurable_snd]
  rfl

theorem labelledLaw_right_map (κ m a b t : ℝ) :
    (labelledLaw κ m a b t).map (fun z => z.2.2) = (pairLaw κ m a b t).snd := by
  change _ = (pairLaw κ m a b t).map Prod.snd
  rw [← labelledLaw_map_snd, Measure.map_map measurable_snd measurable_snd]
  rfl

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_BlockedProductCoupling
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.unflatten_flatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.BlockedProductCoupling

open OneCoordinateCoupling

variable {m : ℕ → ℕ} {κ : ℕ → ℝ}
  {a b : (s : ℕ) → Fin (m s) → ℝ}
  (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
  (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
  (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)

include hm hκ0 hκ ha ha' hb hb'

theorem coordinate_isProbabilityMeasure (j s : ℕ) (i : Fin (m s)) :
    IsProbabilityMeasure (labelledLaw (κ s) (m s) (a s i) (b s i)
      (if s = j then 1 else 0)) := by
  apply labelledLaw_isProbabilityMeasure (hκ0 s) (hκ s)
    (by exact_mod_cast hm s) (ha s i) (ha' s i) (hb s i) (hb' s i)
  all_goals split_ifs <;> norm_num

theorem blockLaw_isProbabilityMeasure (j s : ℕ) :
    IsProbabilityMeasure (blockLaw m κ a b j s) := by
  have := coordinate_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb' j s
  unfold blockLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem law_map_block (j s : ℕ) :
    (law m κ a b j).map (fun z => z s) = blockLaw m κ a b j s := by
  have := blockLaw_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb' j
  exact Measure.infinitePi_map_eval _ s

theorem law_map_coordinate (j s : ℕ) (i : Fin (m s)) :
    (law m κ a b j).map (fun z => z s i) =
      labelledLaw (κ s) (m s) (a s i) (b s i) (if s = j then 1 else 0) := by
  have := coordinate_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb' j s
  change (law m κ a b j).map ((fun z => z i) ∘ (fun z => z s)) = _
  rw [← Measure.map_map (measurable_pi_apply i) (measurable_pi_apply s),
    law_map_block hm hκ0 hκ ha ha' hb hb']
  exact (measurePreserving_eval _ i).map_eq

theorem law_map_uncurry (j : ℕ) :
    (law m κ a b j).map (fun z (p : Σ s, Fin (m s)) => z p.1 p.2) =
      Measure.infinitePi (fun p : Σ s, Fin (m s) =>
        labelledLaw (κ p.1) (m p.1) (a p.1 p.2) (b p.1 p.2)
          (if p.1 = j then 1 else 0)) := by
  have := coordinate_isProbabilityMeasure hm hκ0 hκ ha ha' hb hb' j
  unfold law blockLaw
  have h := Measure.infinitePi_map_piCurry_symm
    (fun s i => labelledLaw (κ s) (m s) (a s i) (b s i)
      (if s = j then 1 else 0))
  simp only [Measure.infinitePi_eq_pi] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1

theorem law_left_marginal_le_ten (j s : ℕ) (i : Fin (m s)) :
    (law m κ a b j).map (fun z => (z s i).2.1) ≤
      (10 : ℝ≥0∞) • volume.restrict (Ico (0 : ℝ) 1) := by
  change (law m κ a b j).map ((Prod.fst ∘ Prod.snd) ∘
    (fun z => z s i)) ≤ _
  rw [← Measure.map_map (measurable_fst.comp measurable_snd)
      ((measurable_pi_apply i).comp (measurable_pi_apply s)),
    law_map_coordinate hm hκ0 hκ ha ha' hb hb']
  change (labelledLaw (κ s) (m s) (a s i) (b s i) _).map
    (fun z => z.2.1) ≤ _
  rw [labelledLaw_left_map, ← baseLaw_eq_restrict]
  apply pairLaw_fst_le_ten (hκ0 s) (hκ s) (by exact_mod_cast hm s)
    (ha s i) (ha' s i) (hb s i) (hb' s i)
  all_goals split_ifs <;> norm_num

theorem law_right_marginal_le_ten (j s : ℕ) (i : Fin (m s)) :
    (law m κ a b j).map (fun z => (z s i).2.2) ≤
      (10 : ℝ≥0∞) • volume.restrict (Ico (0 : ℝ) 1) := by
  change (law m κ a b j).map ((Prod.snd ∘ Prod.snd) ∘
    (fun z => z s i)) ≤ _
  rw [← Measure.map_map (measurable_snd.comp measurable_snd)
      ((measurable_pi_apply i).comp (measurable_pi_apply s)),
    law_map_coordinate hm hκ0 hκ ha ha' hb hb']
  change (labelledLaw (κ s) (m s) (a s i) (b s i) _).map
    (fun z => z.2.2) ≤ _
  rw [labelledLaw_right_map, ← baseLaw_eq_restrict]
  apply pairLaw_snd_le_ten (hκ0 s) (hκ s) (by exact_mod_cast hm s)
    (ha s i) (ha' s i) (hb s i) (hb' s i)
  all_goals split_ifs <;> norm_num

end Invariant233.BlockedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BlockedEventConditions
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set

namespace Invariant233.BlockedProductCoupling

theorem not_mem_futureBad_iff {m : ℕ → ℕ} {K : ℕ → ℝ}
    {j : ℕ} {z : Sample m} :
    z ∉ futureBad m K j ↔
      ∀ s, j < s → ∀ i : Fin (m s),
        (z s i).2.1 < 1 - 2 * K j / ((m s : ℝ) * K s) ∧
        2 * K j / ((m s : ℝ) * K s) < (z s i).2.2 := by
  simp only [futureBad, mem_iUnion, mem_ofPred_eq, not_exists, not_or, not_le]
  constructor
  · intro h s hs
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hs)
    subst s
    exact h n
  · intro h n i
    exact h (j + 1 + n) (by omega) i

end Invariant233.BlockedProductCoupling

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

theorem C_pos (n : ℕ) : 0 < p.C n := by
  rw [hp.C_eq n]
  exact lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hp.L_ge_one n))
    (le_max_left _ _)

theorem real_K_pos (n : ℕ) : 0 < (p.K n : ℝ) := by exact_mod_cast hp.K_pos n

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductDensity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.ProductDensity

theorem integral_sq_eq_one_add_centered_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {h : Ω → ℝ} (hh : MemLp h 2 μ) (hmean : ∫ x, h x ∂μ = 1) :
    (∫ x, h x ^ 2 ∂μ) = 1 + ∫ x, (h x - 1) ^ 2 ∂μ := by
  have hv := ProbabilityTheory.variance_eq_sub hh
  rw [ProbabilityTheory.variance_eq_integral hh.aemeasurable, hmean] at hv
  norm_num at hv
  linarith

theorem integral_finite_product_sq
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1) :
    (∫ x, (∏ i, h i (x i)) ^ 2 ∂Measure.pi μ) =
      ∏ i, (1 + ∫ x, (h i x - 1) ^ 2 ∂μ i) := by
  calc
    _ = ∫ x, ∏ i, (h i (x i)) ^ 2 ∂Measure.pi μ := by
      congr 1
      funext x
      exact (Finset.prod_pow _ _ _).symm
    _ = ∏ i, ∫ x, (h i x) ^ 2 ∂μ i := integral_fintype_prod_eq_prod (μ := μ) (fun i x => h i x ^ 2)
    _ = _ := Finset.prod_congr rfl fun i _ =>
      integral_sq_eq_one_add_centered_sq (hh i) (hmean i)

theorem integral_finite_product_sq_le_exp
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1) :
    (∫ x, (∏ i, h i (x i)) ^ 2 ∂Measure.pi μ) ≤
      Real.exp (∑ i, ∫ x, (h i x - 1) ^ 2 ∂μ i) := by
  rw [integral_finite_product_sq hh hmean]
  exact Real.prod_one_add_le_exp_sum _ fun i => integral_nonneg fun x => sq_nonneg _

theorem integral_finite_product_sq_le_exp_of_sum_le
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hC : (∑ i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    (∫ x, (∏ i, h i (x i)) ^ 2 ∂Measure.pi μ) ≤ Real.exp C :=
  (integral_finite_product_sq_le_exp hh hmean).trans (Real.exp_le_exp.mpr hC)

theorem eLpNorm_finite_product_le_exp_half
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {h : (i : ι) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hC : (∑ i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    eLpNorm (fun x => ∏ i, h i (x i)) 2 (Measure.pi μ) ≤
      ENNReal.ofReal (Real.exp (C / 2)) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    (memLp_finite_product hh)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (Real.exp C) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _)
        (integral_finite_product_sq_le_exp_of_sum_le hh hmean hC) (by positivity)
    _ = Real.exp (C / 2) := by
      rw [← Real.exp_mul]
      congr 1
      ring

theorem eLpNorm_partial_product_le_exp_half
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} {C : ℝ} (s : Finset ι)
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hC : (∑ i ∈ s, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    eLpNorm (fun x => ∏ i ∈ s, h i (x i)) 2 (Measure.infinitePi μ) ≤
      ENNReal.ofReal (Real.exp (C / 2)) := by
  have heq := eLpNorm_comp_measurePreserving
    (memLp_finite_product (fun i : s => hh i)).aestronglyMeasurable
    (measurePreserving_restrict_infinitePi μ s) (p := (2 : ℝ≥0∞))
  have hbound := eLpNorm_finite_product_le_exp_half (fun i : s => hh i)
    (fun i : s => hmean i) (C := C) (by
      exact (Finset.sum_coe_sort s (fun i => ∫ x, (h i x - 1) ^ 2 ∂μ i)).le.trans hC)
  rw [partial_product_eq_restrict h s]
  exact heq.le.trans hbound

theorem eLpNorm_partial_product_le_exp_half_of_tsum_le
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} {C : ℝ} (s : Finset ι)
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hsum : Summable (fun i => ∫ x, (h i x - 1) ^ 2 ∂μ i))
    (hC : (∑' i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    eLpNorm (fun x => ∏ i ∈ s, h i (x i)) 2 (Measure.infinitePi μ) ≤
      ENNReal.ofReal (Real.exp (C / 2)) := by
  apply eLpNorm_partial_product_le_exp_half s hh hmean
  exact (hsum.sum_le_tsum s fun i _ => integral_nonneg fun x => sq_nonneg _).trans hC

theorem integral_partial_product
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} (s : Finset ι)
    (hh : ∀ i, Integrable (h i) (μ i)) :
    (∫ x, ∏ i ∈ s, h i (x i) ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x, h i x ∂μ i := by
  rw [partial_product_eq_restrict h s]
  change (∫ x, (fun y : (i : s) → Ω i => ∏ i : s, h i (y i)) (s.restrict x)
    ∂Measure.infinitePi μ) = _
  rw [integral_restrict_infinitePi (μ := μ) (s := s)
    (f := fun y : (i : s) → Ω i => ∏ i : s, h i (y i))
    (Integrable.fintype_prod_dep (fun i : s => hh i)).aestronglyMeasurable]
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_coe_sort s (fun i => ∫ x, h i x ∂μ i)

theorem partial_product_mul_of_subset
    {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    (h : (i : ι) → Ω i → ℝ) {s t : Finset ι} (hst : s ⊆ t) (x : (i : ι) → Ω i) :
    (∏ i ∈ s, h i (x i)) * (∏ i ∈ t, h i (x i)) =
      ∏ i ∈ t, if i ∈ s then h i (x i) ^ 2 else h i (x i) := by
  have heq : (∏ i ∈ t, if i ∈ s then h i (x i) else 1) =
      ∏ i ∈ s, h i (x i) := by
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hst]
  rw [← heq, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> ring

theorem integral_partial_product_mul_of_subset
    {ι : Type*} [DecidableEq ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} {s t : Finset ι} (hst : s ⊆ t)
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1) :
    (∫ x, (∏ i ∈ s, h i (x i)) * (∏ i ∈ t, h i (x i)) ∂Measure.infinitePi μ) =
      ∫ x, (∏ i ∈ s, h i (x i)) ^ 2 ∂Measure.infinitePi μ := by
  have hmixed : ∀ i, Integrable (fun x => if i ∈ s then h i x ^ 2 else h i x) (μ i) := by
    intro i
    by_cases hi : i ∈ s
    · simpa only [ite_eq_left hi] using (hh i).integrable_sq
    · simpa only [ite_eq_right hi] using (hh i).integrable (by norm_num)
  have hleft : (∫ x, (∏ i ∈ s, h i (x i)) * (∏ i ∈ t, h i (x i)) ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x, h i x ^ 2 ∂μ i := by
    simp_rw [partial_product_mul_of_subset h hst]
    rw [integral_partial_product t hmixed]
    calc
      _ = ∏ i ∈ t, if i ∈ s then ∫ x, h i x ^ 2 ∂μ i else 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases his : i ∈ s
        · simp only [ite_eq_left his]
        · simp only [ite_eq_right his, hmean]
      _ = _ := by rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hst]
  rw [hleft]
  symm
  calc
    _ = ∫ x, ∏ i ∈ s, h i (x i) ^ 2 ∂Measure.infinitePi μ := by
      congr 1
      funext x
      exact (Finset.prod_pow _ _ _).symm
    _ = _ := integral_partial_product s (fun i => (hh i).integrable_sq)

theorem indicator_partial_product
    {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    (h : (i : ι) → Ω i → ℝ) {s t : Finset ι} (hst : s ⊆ t)
    (a : (i : ι) → Set (Ω i)) (x : (i : ι) → Ω i) :
    (Set.pi (s : Set ι) a).indicator (fun y => ∏ i ∈ t, h i (y i)) x =
      ∏ i ∈ t, if i ∈ s then (a i).indicator (h i) (x i) else h i (x i) := by
  classical
  by_cases hx : x ∈ Set.pi (s : Set ι) a
  · rw [Set.indicator_of_mem hx]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases his : i ∈ s
    · rw [ite_eq_left his, Set.indicator_of_mem ((Set.mem_pi.mp hx) i his)]
    · rw [ite_eq_right his]
  · rw [Set.indicator_of_notMem hx]
    symm
    have hex : ∃ i ∈ s, x i ∉ a i := by
      by_contra hnone
      apply hx
      apply Set.mem_pi.mpr
      intro i hi
      by_contra hix
      exact hnone ⟨i, hi, hix⟩
    obtain ⟨i, his, hix⟩ := hex
    apply Finset.prod_eq_zero (hst his)
    rw [ite_eq_left his, Set.indicator_of_notMem hix]

theorem setIntegral_partial_product_pi
    {ι : Type*} [DecidableEq ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} {s t : Finset ι} (hst : s ⊆ t)
    (hh : ∀ i, Integrable (h i) (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (a : (i : ι) → Set (Ω i)) (ha : ∀ i, MeasurableSet (a i)) :
    (∫ x in Set.pi (s : Set ι) a, ∏ i ∈ t, h i (x i) ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x in a i, h i x ∂μ i := by
  classical
  have hmeas : MeasurableSet (Set.pi (s : Set ι) a) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ha i)
  rw [← integral_indicator hmeas]
  simp_rw [indicator_partial_product h hst a]
  have hmixed : ∀ i, Integrable (fun x => if i ∈ s then (a i).indicator (h i) x else h i x) (μ i) := by
    intro i
    by_cases his : i ∈ s
    · simpa only [ite_eq_left his] using (hh i).indicator (ha i)
    · simpa only [ite_eq_right his] using hh i
  rw [integral_partial_product t hmixed]
  calc
    _ = ∏ i ∈ t, if i ∈ s then ∫ x in a i, h i x ∂μ i else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases his : i ∈ s
      · simp only [ite_eq_left his, integral_indicator (ha i)]
      · simp only [ite_eq_right his, hmean]
    _ = _ := by rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hst]

end Invariant233.ProductDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_OrthogonalPrefixLimit
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.ProductDensity

theorem cauchySeq_of_prefix_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℕ → E)
    (hinner : ∀ n m, n ≤ m → inner ℝ (f n) (f m) = ‖f n‖ ^ 2)
    (hbound : BddAbove (Set.range fun n => ‖f n‖ ^ 2)) : CauchySeq f := by
  have hdist : ∀ n m, n ≤ m → dist (f n) (f m) ^ 2 = ‖f m‖ ^ 2 - ‖f n‖ ^ 2 := by
    intro n m hnm
    rw [dist_eq_norm, norm_sub_sq_real, hinner n m hnm]
    ring
  have hmono : Monotone (fun n => ‖f n‖ ^ 2) := by
    intro n m hnm
    have := sq_nonneg (dist (f n) (f m))
    rw [hdist n m hnm] at this
    linarith
  have hc : CauchySeq (fun n => ‖f n‖ ^ 2) :=
    (tendsto_atTop_ciSup hmono hbound).cauchySeq
  apply Metric.cauchySeq_iff.2
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hc (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hreal := hN n hn m hm
  rw [Real.dist_eq] at hreal
  rcases le_total n m with hnm | hmn
  · have hs := hdist n m hnm
    have hl := (abs_lt.mp hreal).1
    nlinarith [dist_nonneg (x := f n) (y := f m)]
  · have hs := hdist m n hmn
    have hl := (abs_lt.mp hreal).2
    rw [dist_comm (f m) (f n)] at hs
    nlinarith [dist_nonneg (x := f n) (y := f m)]

theorem exists_limit_of_prefix_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : ℕ → E)
    (hinner : ∀ n m, n ≤ m → inner ℝ (f n) (f m) = ‖f n‖ ^ 2)
    (hbound : BddAbove (Set.range fun n => ‖f n‖ ^ 2)) :
    ∃ g : E, Tendsto f atTop (𝓝 g) :=
  cauchySeq_tendsto_of_complete (cauchySeq_of_prefix_inner f hinner hbound)

end Invariant233.ProductDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductDensityLimit
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.ProductDensity

theorem inner_toLp_eq_integral_mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp [hfx, hgx, mul_comm]

theorem partialDensityLp_inner
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1) {n m : ℕ} (hnm : n ≤ m) :
    inner ℝ (partialDensityLp hh n) (partialDensityLp hh m) =
      ‖partialDensityLp hh n‖ ^ 2 := by
  calc
    _ = ∫ x, (∏ i ∈ Finset.range n, h i (x i)) *
        (∏ i ∈ Finset.range m, h i (x i)) ∂Measure.infinitePi μ :=
      inner_toLp_eq_integral_mul _ _
    _ = ∫ x, (∏ i ∈ Finset.range n, h i (x i)) ^ 2 ∂Measure.infinitePi μ :=
      integral_partial_product_mul_of_subset (Finset.range_mono hnm) hh hmean
    _ = inner ℝ (partialDensityLp hh n) (partialDensityLp hh n) := by
      rw [partialDensityLp, inner_toLp_eq_integral_mul]
      congr 1
      funext x
      ring
    _ = _ := real_inner_self_eq_norm_sq _

theorem exists_partialDensityLp_limit
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hsum : Summable (fun i => ∫ x, (h i x - 1) ^ 2 ∂μ i))
    (hC : (∑' i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    ∃ g : Lp ℝ 2 (Measure.infinitePi μ),
      Tendsto (partialDensityLp hh) atTop (𝓝 g) ∧ ‖g‖ ≤ Real.exp (C / 2) := by
  have hb : ∀ n, ‖partialDensityLp hh n‖ ≤ Real.exp (C / 2) := by
    intro n
    rw [partialDensityLp, Lp.norm_toLp]
    have hnorm := eLpNorm_partial_product_le_exp_half_of_tsum_le
      (Finset.range n) hh hmean hsum hC
    have := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hnorm
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using this
  obtain ⟨g, hg⟩ := exists_limit_of_prefix_inner (partialDensityLp hh)
    (fun n m hnm => partialDensityLp_inner hh hmean hnm)
    ⟨(Real.exp (C / 2)) ^ 2, by
      rintro _ ⟨n, rfl⟩
      exact pow_le_pow_left₀ (norm_nonneg _) (hb n) 2⟩
  exact ⟨g, hg, le_of_tendsto hg.norm (Filter.Eventually.of_forall hb)⟩

theorem tendsto_eLpNorm_one_partialDensity_sub
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g)) :
    Tendsto (fun n => eLpNorm
      ((fun x => ∏ i ∈ Finset.range n, h i (x i)) - (g : ((i : ℕ) → Ω i) → ℝ))
      1 (Measure.infinitePi μ)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n => eLpNorm
      ((fun x => ∏ i ∈ Finset.range n, h i (x i)) - (g : ((i : ℕ) → Ω i) → ℝ))
      2 (Measure.infinitePi μ)) atTop (𝓝 0) := by
    have ht := hg.edist (tendsto_const_nhds (x := g))
    simp only [edist_self] at ht
    apply ht.congr
    intro n
    rw [Lp.edist_def]
    apply eLpNorm_congr_ae
    exact (memLp_partial_product (Finset.range n) hh).coeFn_toLp.sub Filter.EventuallyEq.rfl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
    (fun _ => bot_le)
  intro n
  exact eLpNorm_le_eLpNorm_of_exponent_le (hf := by first | exact (memLp_partial_product (Finset.range n) hh).aestronglyMeasurable.sub (Lp.aestronglyMeasurable g) | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)

theorem partialDensityLp_limit_nonneg
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hnonneg : ∀ i x, 0 ≤ h i x)
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g)) :
    0 ≤ᵐ[Measure.infinitePi μ] (g : ((i : ℕ) → Ω i) → ℝ) := by
  apply ae_nonneg_of_forall_setIntegral_nonneg ((Lp.memLp g).integrable (by norm_num))
  intro s hs hsf
  have hi := tendsto_setIntegral_of_L1' (g : ((i : ℕ) → Ω i) → ℝ) (Lp.aestronglyMeasurable g)
    (Filter.Eventually.of_forall fun n =>
      (memLp_partial_product (Finset.range n) hh).integrable (by norm_num))
    (tendsto_eLpNorm_one_partialDensity_sub hh hg) s
  exact ge_of_tendsto hi (Filter.Eventually.of_forall fun n =>
    integral_nonneg fun x => Finset.prod_nonneg fun i _ => hnonneg i (x i))

theorem partialDensityLp_limit_integral
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g)) :
    (∫ x, g x ∂Measure.infinitePi μ) = 1 := by
  have hi := tendsto_integral_of_L1' (hfi := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (g : ((i : ℕ) → Ω i) → ℝ)
    (Filter.Eventually.of_forall fun n =>
      (memLp_partial_product (Finset.range n) hh).integrable (by norm_num))
    (tendsto_eLpNorm_one_partialDensity_sub hh hg)
  have heq : ∀ n, (∫ x, ∏ i ∈ Finset.range n, h i (x i) ∂Measure.infinitePi μ) = 1 := by
    intro n
    rw [integral_partial_product (Finset.range n) (fun i => (hh i).integrable (by norm_num))]
    simp [hmean]
  simp_rw [heq] at hi
  exact tendsto_nhds_unique hi tendsto_const_nhds

theorem partialDensityLp_limit_setIntegral_pi
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g))
    (s : Finset ℕ) (a : (i : ℕ) → Set (Ω i)) (ha : ∀ i, MeasurableSet (a i)) :
    (∫ x in Set.pi (s : Set ℕ) a, g x ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x in a i, h i x ∂μ i := by
  have hi := tendsto_setIntegral_of_L1' (g : ((i : ℕ) → Ω i) → ℝ) (Lp.aestronglyMeasurable g)
    (Filter.Eventually.of_forall fun n =>
      (memLp_partial_product (Finset.range n) hh).integrable (by norm_num))
    (tendsto_eLpNorm_one_partialDensity_sub hh hg) (Set.pi (s : Set ℕ) a)
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range s
  have heq : (fun n => ∫ x in Set.pi (s : Set ℕ) a,
      ∏ i ∈ Finset.range n, h i (x i) ∂Measure.infinitePi μ) =ᶠ[atTop]
      (fun _ => ∏ i ∈ s, ∫ x in a i, h i x ∂μ i) := by
    apply Filter.eventually_atTop.2
    refine ⟨N, fun n hn => ?_⟩
    exact setIntegral_partial_product_pi (hN.trans (Finset.range_mono hn))
      (fun i => (hh i).integrable (by norm_num)) hmean a ha
  exact tendsto_nhds_unique hi (tendsto_const_nhds.congr' heq.symm)

theorem isProbabilityMeasure_withDensity_ofReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {h : Ω → ℝ} (hh : Integrable h μ) (hnonneg : 0 ≤ᵐ[μ] h)
    (hmean : ∫ x, h x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (h x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hh hnonneg, hmean]
  simp

theorem partialDensityLp_limit_withDensity
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hnonneg : ∀ i x, 0 ≤ h i x)
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    {g : Lp ℝ 2 (Measure.infinitePi μ)}
    (hg : Tendsto (partialDensityLp hh) atTop (𝓝 g)) :
    (Measure.infinitePi μ).withDensity (fun x => ENNReal.ofReal (g x)) =
      Measure.infinitePi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (h i x))) := by
  let : ∀ i, IsProbabilityMeasure ((μ i).withDensity (fun x => ENNReal.ofReal (h i x))) :=
    fun i => isProbabilityMeasure_withDensity_ofReal ((hh i).integrable (by norm_num))
      (Filter.Eventually.of_forall (hnonneg i)) (hmean i)
  have hgnonneg := partialDensityLp_limit_nonneg hh hnonneg hg
  have hgi := (Lp.memLp g).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply Measure.eq_infinitePi
  intro s a ha
  have hmeas : MeasurableSet (Set.pi (s : Set ℕ) a) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ha i)
  rw [withDensity_apply _ hmeas,
    ← ofReal_integral_eq_lintegral_ofReal hgi.restrict (ae_restrict_of_ae hgnonneg),
    partialDensityLp_limit_setIntegral_pi hh hmean hg s a ha]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnonneg i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (ha i)]
  exact ofReal_integral_eq_lintegral_ofReal ((hh i).integrable (by norm_num)).restrict
    (Filter.Eventually.of_forall (hnonneg i))

theorem exists_product_density
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hnonneg : ∀ i x, 0 ≤ h i x)
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hsum : Summable (fun i => ∫ x, (h i x - 1) ^ 2 ∂μ i))
    (hC : (∑' i, ∫ x, (h i x - 1) ^ 2 ∂μ i) ≤ C) :
    ∃ H : ((i : ℕ) → Ω i) → ℝ,
      MemLp H 2 (Measure.infinitePi μ) ∧
      (0 ≤ᵐ[Measure.infinitePi μ] H) ∧
      (∫ x, H x ∂Measure.infinitePi μ) = 1 ∧
      eLpNorm H 2 (Measure.infinitePi μ) ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (Measure.infinitePi μ).withDensity (fun x => ENNReal.ofReal (H x)) =
        Measure.infinitePi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (h i x))) := by
  obtain ⟨g, hg, hgbound⟩ := exists_partialDensityLp_limit hh hmean hsum hC
  refine ⟨g, Lp.memLp g, partialDensityLp_limit_nonneg hh hnonneg hg,
    partialDensityLp_limit_integral hh hmean hg, ?_,
    partialDensityLp_limit_withDensity hh hnonneg hmean hg⟩
  rw [← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hgbound

theorem exists_hybrid_product_density
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : Bool → (i : ℕ) → Ω i → ℝ} {b : ℕ → ℝ} {C : ℝ}
    (ε : ℕ → Bool)
    (hh : ∀ a i, MemLp (h a i) 2 (μ i))
    (hnonneg : ∀ a i x, 0 ≤ h a i x)
    (hmean : ∀ a i, ∫ x, h a i x ∂μ i = 1)
    (hb : ∀ a i, (∫ x, (h a i x - 1) ^ 2 ∂μ i) ≤ b i)
    (hsum : Summable b) (hC : (∑' i, b i) ≤ C) :
    ∃ H : ((i : ℕ) → Ω i) → ℝ,
      MemLp H 2 (Measure.infinitePi μ) ∧
      (0 ≤ᵐ[Measure.infinitePi μ] H) ∧
      (∫ x, H x ∂Measure.infinitePi μ) = 1 ∧
      eLpNorm H 2 (Measure.infinitePi μ) ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (Measure.infinitePi μ).withDensity (fun x => ENNReal.ofReal (H x)) =
        Measure.infinitePi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (h (ε i) i x))) := by
  have hsel : Summable (fun i => ∫ x, (h (ε i) i x - 1) ^ 2 ∂μ i) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg fun x => sq_nonneg _)
      (fun i => hb (ε i) i) hsum
  exact exists_product_density (fun i => hh (ε i) i)
    (fun i => hnonneg (ε i) i) (fun i => hmean (ε i) i) hsel
    ((hsel.tsum_le_tsum (fun i => hb (ε i) i) hsum).trans hC)

end Invariant233.ProductDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductCoupling
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.flatten_unflatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace Invariant233.OrderedProductCoupling

open OneCoordinateCoupling

lemma hybridEndpoint_measurable (ε : ℕ → Bool) : Measurable (hybridEndpoint ε) := by
  apply Measurable.of_eval
  intro i
  unfold hybridEndpoint rightEndpoint leftEndpoint
  split_ifs <;> fun_prop

lemma coordinateLaw_map_pair (P : Parameters) (i : ℕ) :
    (coordinateLaw P i).map Prod.snd = pairLaw (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i) :=
  labelledLaw_map_snd _ _ _ _ _

lemma coordinateLaw_map_left (P : Parameters) (i : ℕ) :
    (coordinateLaw P i).map (fun z => z.2.1) = baseLaw.withDensity
      (fun x => ENNReal.ofReal (marginalDensity P false i x)) := by
  have h := pairLaw_fst_density (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
    (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i) (P.t_nonneg i) (P.t_le i)
  rw [← coordinateLaw_map_pair P i, Measure.fst,
    Measure.map_map measurable_fst measurable_snd] at h
  exact h

lemma coordinateLaw_map_right (P : Parameters) (i : ℕ) :
    (coordinateLaw P i).map (fun z => z.2.2) = baseLaw.withDensity
      (fun x => ENNReal.ofReal (marginalDensity P true i x)) := by
  have h := pairLaw_snd_density (P.κ_nonneg i) (P.κ_le i) (P.m_ge i)
    (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i) (P.t_nonneg i) (P.t_le i)
  rw [← coordinateLaw_map_pair P i, Measure.snd,
    Measure.map_map measurable_snd measurable_snd] at h
  exact h

lemma hybridEndpoint_map (P : Parameters) (ε : ℕ → Bool) :
    (law P).map (hybridEndpoint ε) = Measure.infinitePi (fun i => baseLaw.withDensity
      (fun x => ENNReal.ofReal (marginalDensity P (ε i) i x))) := by
  let f : ℕ → CoordinateSample → ℝ :=
    fun i z => if ε i then z.2.2 else z.2.1
  have hf : ∀ i, Measurable (f i) := by
    intro i
    dsimp [f]
    split_ifs <;> fun_prop
  calc
    _ = Measure.infinitePi (fun i => (coordinateLaw P i).map (f i)) :=
      Measure.infinitePi_map_pi (coordinateLaw P) hf
    _ = _ := by
      congr 1
      funext i
      cases h : ε i
      · simpa only [f, h, Bool.false_eq_true, ite_false, if_false] using coordinateLaw_map_left P i
      · simpa only [f, h, ite_true, if_true] using coordinateLaw_map_right P i

lemma marginalDensity_memLp (P : Parameters) (side : Bool) (i : ℕ) :
    MemLp (marginalDensity P side i) 2 baseLaw := by
  cases side
  · exact leftMarginalDensity_memLp _ _ _ _ _
  · exact rightMarginalDensity_memLp _ _ _ _ _

lemma marginalDensity_nonneg (P : Parameters) (side : Bool) (i : ℕ) (x : ℝ) :
    0 ≤ marginalDensity P side i x := by
  cases side
  · exact le_trans (by norm_num) (leftMarginalDensity_bounds (P.κ_nonneg i) (P.κ_le i)
      (P.m_ge i) (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i) x).1
  · exact le_trans (by norm_num) (rightMarginalDensity_bounds (P.κ_nonneg i) (P.κ_le i)
      (P.m_ge i) (P.a_lower i) (P.a_upper i) (P.b_lower i) (P.b_upper i)
      (P.t_nonneg i) (P.t_le i) x).1

lemma marginalDensity_integral (P : Parameters) (side : Bool) (i : ℕ) :
    (∫ x, marginalDensity P side i x ∂baseLaw) = 1 := by
  have hm0 : 0 < P.m i := by linarith [P.m_ge i]
  have ha0 := CouplingMarginalBounds.width_pos hm0 (P.a_lower i)
  have hb0 := CouplingMarginalBounds.width_pos hm0 (P.b_lower i)
  cases side
  · exact leftMarginalDensity_integral (by linarith [P.m_ge i]) ha0 (P.a_upper i) hb0 (P.b_upper i)
  · exact rightMarginalDensity_integral (by linarith [P.m_ge i]) ha0 (P.a_upper i) hb0 (P.b_upper i)

lemma marginalDensity_variance_le (P : Parameters) (side : Bool) (i : ℕ) :
    (∫ x, (marginalDensity P side i x - 1) ^ 2 ∂baseLaw) ≤ energyBound P i := by
  have hm0 : 0 < P.m i := by linarith [P.m_ge i]
  have ha0 := CouplingMarginalBounds.width_pos hm0 (P.a_lower i)
  have hb0 := CouplingMarginalBounds.width_pos hm0 (P.b_lower i)
  cases side
  · exact leftMarginalDensity_energy (by linarith [P.m_ge i]) ha0 (P.a_upper i) hb0 (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)
  · exact rightMarginalDensity_energy (by linarith [P.m_ge i]) ha0 (P.a_upper i) hb0 (P.b_upper i)
      (P.t_nonneg i) (P.t_le i)

lemma exists_hybrid_density (P : Parameters) (ε : ℕ → Bool) {C : ℝ}
    (hsum : Summable (energyBound P)) (hC : (∑' i, energyBound P i) ≤ C) :
    ∃ H : Endpoint → ℝ, MemLp H 2 baseMeasure ∧ (0 ≤ᵐ[baseMeasure] H) ∧
      (∫ x, H x ∂baseMeasure) = 1 ∧
      eLpNorm H 2 baseMeasure ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (law P).map (hybridEndpoint ε) = baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
  obtain ⟨H, hH, hnonneg, hmean, hnorm, hlaw⟩ :=
    ProductDensity.exists_hybrid_product_density ε
      (marginalDensity_memLp P) (marginalDensity_nonneg P) (marginalDensity_integral P)
      (marginalDensity_variance_le P) hsum hC
  exact ⟨H, hH, hnonneg, hmean, hnorm, (hybridEndpoint_map P ε).trans hlaw.symm⟩

end Invariant233.OrderedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_BlockedCouplingEnergy
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Invariant233.BlockedProductCoupling

theorem sum_block_energy (m : ℕ) (hm : 0 < m) (κ t : ℝ) :
    (∑' _i : Fin m, 20 * (2 * κ ^ 2 / (m : ℝ) + t / (m : ℝ))) =
      20 * (2 * κ ^ 2 + t) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem full_energy_sum (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    (κ : ℕ → ℝ) (hκ : Summable (fun s => κ s ^ 2)) (j : ℕ) :
    Summable (fun p : Σ s, Fin (m s) =>
      20 * (2 * κ p.1 ^ 2 / (m p.1 : ℝ) +
        (if p.1 = j then 1 else 0) / (m p.1 : ℝ))) ∧
    (∑' p : Σ s, Fin (m s),
      20 * (2 * κ p.1 ^ 2 / (m p.1 : ℝ) +
        (if p.1 = j then 1 else 0) / (m p.1 : ℝ))) =
      20 * (2 * (∑' s, κ s ^ 2) + 1) := by
  classical
  have htag : Summable (fun s : ℕ => if s = j then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {j}) (by simp)
  have he (s : ℕ) :
      (∑' _i : Fin (m s), 20 * (2 * κ s ^ 2 / (m s : ℝ) +
        (if s = j then 1 else 0) / (m s : ℝ))) =
      20 * (2 * κ s ^ 2 + (if s = j then 1 else 0)) :=
    sum_block_energy _ (hm s) _ _
  have hblock : Summable (fun s => 20 * (2 * κ s ^ 2 +
      (if s = j then (1 : ℝ) else 0))) :=
    ((hκ.mul_left 2).add htag).mul_left 20
  have hs : Summable (fun p : Σ s, Fin (m s) =>
      20 * (2 * κ p.1 ^ 2 / (m p.1 : ℝ) +
        (if p.1 = j then 1 else 0) / (m p.1 : ℝ))) := by
    apply (summable_sigma_of_nonneg (fun p => by positivity)).2
    refine ⟨fun s => (hasSum_fintype _).summable, ?_⟩
    simpa only [he] using hblock
  refine ⟨hs, ?_⟩
  rw [hs.tsum_sigma' (fun s => (hasSum_fintype _).summable)]
  simp only [he]
  rw [tsum_mul_left, (hκ.mul_left 2).tsum_add htag, tsum_mul_left]
  simp

theorem enumerated_energy_sum (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    (κ : ℕ → ℝ) (hκ : Summable (fun s => κ s ^ 2))
    (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) :
    Summable (fun i : ℕ => 20 * (2 * κ (e i).1 ^ 2 / (m (e i).1 : ℝ) +
      (if (e i).1 = j then 1 else 0) / (m (e i).1 : ℝ))) ∧
    (∑' i : ℕ, 20 * (2 * κ (e i).1 ^ 2 / (m (e i).1 : ℝ) +
      (if (e i).1 = j then 1 else 0) / (m (e i).1 : ℝ))) =
      20 * (2 * (∑' s, κ s ^ 2) + 1) := by
  obtain ⟨hs, hv⟩ := full_energy_sum m hm κ hκ j
  exact ⟨e.summable_iff.mpr hs, (e.tsum_eq _).trans hv⟩

end Invariant233.BlockedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_BlockedCouplingDensity
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.flatten_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.unflatten_flatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.BlockedProductCoupling

variable {m : ℕ → ℕ} {κ : ℕ → ℝ}
  {a b : (s : ℕ) → Fin (m s) → ℝ}
  (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
  (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
  (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)

include hm hκ0 hκ ha ha' hb hb'

theorem law_map_flatten (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) :
    (law m κ a b j).map (flatten e) =
      OrderedProductCoupling.law (parameters hm hκ0 hκ ha ha' hb hb' e j) := by
  let P := parameters hm hκ0 hκ ha ha' hb hb' e j
  change (law m κ a b j).map
    ((fun z : (Σ s, Fin (m s)) → Coordinate => fun i => z (e i)) ∘
      (fun z p => z p.1 p.2)) = OrderedProductCoupling.law P
  rw [← Measure.map_map (by fun_prop) (by fun_prop),
    law_map_uncurry hm hκ0 hκ ha ha' hb hb']
  have h := Measure.infinitePi_map_piCongrLeft
    (OrderedProductCoupling.coordinateLaw P) e.symm
  simp only [OrderedProductCoupling.coordinateLaw, P, parameters,
    Equiv.apply_symm_apply] at h
  unfold OrderedProductCoupling.law
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1)
  · funext z i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  · congr 1
    funext p
    rw [e.apply_symm_apply]

theorem exists_hybrid_density_of_blocks
    (hsq : Summable (fun s => κ s ^ 2))
    (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) (sel : ℕ → Bool) :
    ∃ H : OrderedProductCoupling.Endpoint → ℝ,
      MemLp H 2 OrderedProductCoupling.baseMeasure ∧
      (0 ≤ᵐ[OrderedProductCoupling.baseMeasure] H) ∧
      (∫ x, H x ∂OrderedProductCoupling.baseMeasure) = 1 ∧
      eLpNorm H 2 OrderedProductCoupling.baseMeasure ≤
        ENNReal.ofReal (Real.exp (10 * (2 * (∑' s, κ s ^ 2) + 1))) ∧
      (law m κ a b j).map (OrderedProductCoupling.hybridEndpoint sel ∘ flatten e) =
        OrderedProductCoupling.baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
  let P := parameters hm hκ0 hκ ha ha' hb hb' e j
  obtain ⟨hs, he⟩ := enumerated_energy_sum m (fun s => by have := hm s; omega) κ hsq e j
  have hs' : Summable (OrderedProductCoupling.energyBound P) := hs
  have he' : (∑' i, OrderedProductCoupling.energyBound P i) ≤
      20 * (2 * (∑' s, κ s ^ 2) + 1) := he.le
  obtain ⟨H, hH, hn, hmean, hnorm, hmap⟩ :=
    OrderedProductCoupling.exists_hybrid_density P sel hs' he'
  refine ⟨H, hH, hn, hmean, ?_, ?_⟩
  · convert hnorm using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  · rw [← Measure.map_map (OrderedProductCoupling.hybridEndpoint_measurable sel)
      (by unfold flatten; fun_prop), law_map_flatten hm hκ0 hκ ha ha' hb hb']
    exact hmap

end Invariant233.BlockedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_BlockedCircleEvent
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.unflatten_flatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory Set
open scoped Topology

namespace Invariant233.BlockedProductCoupling

theorem ae_all_coordinates_mem_Ico
    {m : ℕ → ℕ} {κ : ℕ → ℝ} {a b : (s : ℕ) → Fin (m s) → ℝ}
    (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
    (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
    (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)
    (j : ℕ) :
    ∀ᵐ z ∂law m κ a b j, ∀ s i,
      (z s i).2.1 ∈ Ico (0 : ℝ) 1 ∧ (z s i).2.2 ∈ Ico (0 : ℝ) 1 := by
  apply ae_all_iff.2
  intro s
  apply ae_all_iff.2
  intro i
  have hs : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ico (0 : ℝ) 1),
      t ∈ Ico (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ico
  have hx := (Measure.absolutelyContinuous_of_le_smul
    (law_left_marginal_le_ten hm hκ0 hκ ha ha' hb hb' j s i)).ae_le hs
  have hy := (Measure.absolutelyContinuous_of_le_smul
    (law_right_marginal_le_ten hm hκ0 hκ ha ha' hb hb' j s i)).ae_le hs
  have hmx : Measurable (fun z : Sample m => (z s i).2.1) := by fun_prop
  have hmy : Measurable (fun z : Sample m => (z s i).2.2) := by fun_prop
  exact (ae_of_ae_map hmx.aemeasurable hx).and (ae_of_ae_map hmy.aemeasurable hy)

theorem ae_circle_representatives
    {m : ℕ → ℕ} {κ : ℕ → ℝ} {a b : (s : ℕ) → Fin (m s) → ℝ}
    (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
    (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
    (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) :
    ∀ᵐ z ∂law m κ a b j, ∀ i,
      circleRepresentative (circleLeftEndpoint e z i) = leftEndpoint e z i ∧
      circleRepresentative (circleRightEndpoint e z i) = rightEndpoint e z i := by
  filter_upwards [ae_all_coordinates_mem_Ico hm hκ0 hκ ha ha' hb hb' j] with z hz
  intro i
  have hx := (hz (e i).1 (e i).2).1
  have hy := (hz (e i).1 (e i).2).2
  have hx' : (z (e i).1 (e i).2).2.1 ∈ Ico (0 : ℝ) (0 + 1) := by simpa using hx
  have hy' : (z (e i).1 (e i).2).2.2 ∈ Ico (0 : ℝ) (0 + 1) := by simpa using hy
  constructor
  · exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hx')
  · exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hy')

theorem measurePreserving_toCircle : MeasurePreserving toCircle
    OrderedProductCoupling.baseMeasure ProductModel.baseMeasure := by
  have hc : MeasurePreserving (fun t : ℝ => (t : Circle))
      OneCoordinateCoupling.baseLaw circleMeasure := by
    rw [OneCoordinateCoupling.baseLaw_eq_restrict, circleMeasure,
      restrict_Ico_eq_restrict_Ioc]
    simpa only [zero_add] using AddCircle.measurePreserving_mk (1 : ℝ) 0
  refine ⟨by unfold toCircle; fun_prop, ?_⟩
  unfold OrderedProductCoupling.baseMeasure ProductModel.baseMeasure toCircle
  rw [Measure.infinitePi_map_pi _ (fun _ => hc.measurable)]
  simp only [hc.map_eq]

end Invariant233.BlockedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BlockedSourceEvent
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Invariant233.BlockedProductCoupling

theorem mem_sourceRetainedEvent_iff {X : Type*} {m : ℕ → ℕ} {K : ℕ → ℝ}
    {r : X → ℝ} {x y : Sample m → X} {j : ℕ} {z : Sample m} :
    z ∈ sourceRetainedEvent m K r x y j ↔
      (∃ i, (z j i).1 = some (4 : Fin 5)) ∧
      (∀ i, (z j i).2.1 < 1 - 2 / (m j : ℝ) ∧
        2 / (m j : ℝ) < (z j i).2.2) ∧
      (∀ s, j < s → ∀ i : Fin (m s),
        (z s i).2.1 < 1 - 2 * K j / ((m s : ℝ) * K s) ∧
        2 * K j / ((m s : ℝ) * K s) < (z s i).2.2) ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤ r (x z) ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤ 1 - r (y z) := by
  simp only [sourceRetainedEvent, Set.mem_sdiff, mem_union, not_or,
    not_mem_futureBad_iff, currentEvent, mem_ofPred_eq, not_lt]
  tauto

theorem source_kappa_nonneg (j : ℕ) : 0 ≤ ProductScaleData.kappa j := by
  unfold ProductScaleData.kappa
  positivity

theorem source_kappa_le (j : ℕ) : ProductScaleData.kappa j ≤ 1 / 100 := by
  apply one_div_le_one_div_of_le (by norm_num)
  have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
  linarith

theorem source_kappa_sq_summable : Summable (fun j => ProductScaleData.kappa j ^ 2) := by
  have hs : Summable (fun j : ℕ => 1 / (j : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have ht := (summable_nat_add_iff 1).mpr hs
  apply (ht.mul_left (1 / (100 : ℝ) ^ 2)).congr
  intro j
  dsimp [ProductScaleData.kappa]
  ring

theorem sourceLaw_quasiMeasurePreserving_hybrid {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ)
    (sel : ℕ → Bool) :
    Measure.QuasiMeasurePreserving
      (toCircle ∘ (OrderedProductCoupling.hybridEndpoint sel ∘ flatten e))
      (sourceLaw p j) ProductModel.baseMeasure := by
  apply measurePreserving_toCircle.quasiMeasurePreserving.comp
  refine ⟨(OrderedProductCoupling.hybridEndpoint_measurable sel).comp
    (by unfold flatten; fun_prop), ?_⟩
  obtain ⟨H, _, _, _, _, hmap⟩ := exists_hybrid_density_of_blocks
    hp.m_ge_100 source_kappa_nonneg source_kappa_le
    (fun s _ => (hp.a_bounds s).1) (fun s _ => (hp.a_bounds s).2)
    (fun s _ => (hp.b_bounds s).1) (fun s _ => (hp.b_bounds s).2)
    source_kappa_sq_summable e j sel
  change (sourceLaw p j).map _ = _ at hmap
  rw [hmap]
  exact withDensity_absolutelyContinuous _ _

theorem sourceLaw_quasiMeasurePreserving_left {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ) :
    Measure.QuasiMeasurePreserving (circleLeftEndpoint e)
      (sourceLaw p j) ProductModel.baseMeasure := by
  exact sourceLaw_quasiMeasurePreserving_hybrid hp e j (fun _ => false)

theorem sourceLaw_quasiMeasurePreserving_right {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ) :
    Measure.QuasiMeasurePreserving (circleRightEndpoint e)
      (sourceLaw p j) ProductModel.baseMeasure := by
  exact sourceLaw_quasiMeasurePreserving_hybrid hp e j (fun _ => true)

end Invariant233.BlockedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FiniteSupportCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Function

namespace Invariant233.FiniteSupportCocycle

theorem exp_tsum_floor_zero {I : Type*} (x c : I → ℝ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) :
    Real.exp (-(∑' i, c i * (⌊x i⌋ : ℝ))) = 1 := by
  have hf (i : I) : ⌊x i⌋ = 0 := Int.floor_eq_zero_iff.mpr (hx i)
  simp [hf]

end Invariant233.FiniteSupportCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function

namespace Invariant233.ProductCocycle

theorem representative_mem_Ico (x : UnitAddCircle) :
    representative x ∈ Ico (0 : ℝ) 1 := by
  simpa only [representative, zero_add] using (AddCircle.equivIco (1 : ℝ) 0 x).property

@[simp] theorem cocycleVersion_zero {I : Type*} (θ c : I → ℝ) (x : Space I) :
    cocycleVersion θ c 0 x = 1 := by
  simp only [cocycleVersion, Int.cast_zero, zero_mul, add_zero]
  exact FiniteSupportCocycle.exp_tsum_floor_zero _ c
    (fun i ↦ representative_mem_Ico (x i))

end Invariant233.ProductCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CocycleWindowBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set

open scoped BigOperators ComplexConjugate lp
namespace Invariant233.CocycleWindowBounds

theorem floor_forward_eq_zero {x α v K : ℝ}
    (hx : 0 ≤ x) (hα : 0 ≤ α) (hv : 0 ≤ v) (hvK : v ≤ K)
    (hexclude : x + K * α < 1) : ⌊x + v * α⌋ = 0 := by
  apply Int.floor_eq_zero_iff.mpr
  constructor
  · positivity
  · have hmul := mul_le_mul_of_nonneg_right hvK hα
    linarith

theorem floor_backward_eq_zero {y α v K : ℝ}
    (hy : y < 1) (hα : 0 ≤ α) (hv : 0 ≤ v) (hvK : v ≤ K)
    (hexclude : K * α ≤ y) : ⌊y - v * α⌋ = 0 := by
  apply Int.floor_eq_zero_iff.mpr
  constructor
  · exact sub_nonneg.mpr ((mul_le_mul_of_nonneg_right hvK hα).trans hexclude)
  · exact (sub_le_self y (mul_nonneg hv hα)).trans_lt hy

theorem floor_forward_le {x α v : ℝ} (K : ℕ)
    (hx : x < 1) (hα : α ≤ 1) (hv : 0 ≤ v) (hvK : v ≤ K) :
    (⌊x + v * α⌋ : ℝ) ≤ (K : ℝ) + 1 := by
  have hmul : v * α ≤ (K : ℝ) :=
    (mul_le_mul_of_nonneg_left hα hv).trans (by simpa using hvK)
  linarith [Int.floor_le (x + v * α)]

theorem neg_floor_backward_le {y α v : ℝ} (K : ℕ)
    (hy : 0 ≤ y) (hα : α ≤ 1) (hv : 0 ≤ v) (hvK : v ≤ K) :
    -(⌊y - v * α⌋ : ℝ) ≤ (K : ℝ) + 1 := by
  have hmul : v * α ≤ (K : ℝ) :=
    (mul_le_mul_of_nonneg_left hα hv).trans (by simpa using hvK)
  linarith [Int.lt_floor_add_one (y - v * α)]

theorem tsum_weighted_le_prefix {I : Type*} (s : Finset I)
    (c a : I → ℝ) (B : ℝ) (hc : ∀ i, 0 ≤ c i)
    (hout : ∀ i ∉ s, a i = 0) (hbound : ∀ i ∈ s, a i ≤ B) :
    (∑' i, c i * a i) ≤ B * ∑ i ∈ s, c i := by
  rw [tsum_eq_sum (s := s) (fun i hi => by rw [hout i hi]; simp)]
  calc
    (∑ i ∈ s, c i * a i) ≤ ∑ i ∈ s, c i * B :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hbound i hi) (hc i))
    _ = B * ∑ i ∈ s, c i := by rw [← Finset.sum_mul]; ring

theorem signed_floor_sums_le {I : Type*} (s : Finset I)
    (x y α c : I → ℝ) (K : ℕ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1)
    (hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hleft : ∀ i ∉ s, x i + (K : ℝ) * α i < 1)
    (hright : ∀ i ∉ s, (K : ℝ) * α i ≤ y i)
    (v : ℤ) (hv : |v| ≤ (K : ℤ)) :
    (∑' i, c i * (⌊x i + (v : ℝ) * α i⌋ : ℝ)) ≤
        ((K : ℝ) + 1) * ∑ i ∈ s, c i ∧
    -(∑' i, c i * (⌊y i - (v : ℝ) * α i⌋ : ℝ)) ≤
        ((K : ℝ) + 1) * ∑ i ∈ s, c i := by
  have hcost : 0 ≤ ((K : ℝ) + 1) * ∑ i ∈ s, c i := by
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hc i)
  rcases le_or_gt 0 v with hv0 | hv0
  · have hv0' : (0 : ℝ) ≤ v := by exact_mod_cast hv0
    have hvK : (v : ℝ) ≤ K := by exact_mod_cast (le_abs_self v).trans hv
    constructor
    · apply tsum_weighted_le_prefix s c _ _ hc
      · intro i hi
        rw [floor_forward_eq_zero (hx i).1 (hα i).1 hv0' hvK (hleft i hi)]
        simp
      · intro i _
        exact floor_forward_le K (hx i).2 (hα i).2 hv0' hvK
    · rw [← tsum_neg]
      have heq : (fun i => -(c i * (⌊y i - (v : ℝ) * α i⌋ : ℝ))) =
          (fun i => c i * -(⌊y i - (v : ℝ) * α i⌋ : ℝ)) := by
        funext i; ring
      rw [heq]
      apply tsum_weighted_le_prefix s c _ _ hc
      · intro i hi
        rw [floor_backward_eq_zero (hy i).2 (hα i).1 hv0' hvK (hright i hi)]
        simp
      · intro i _
        exact neg_floor_backward_le K (hy i).1 (hα i).2 hv0' hvK
  · have hv0' : (v : ℝ) ≤ 0 := by exact_mod_cast hv0.le
    constructor
    · apply le_trans (tsum_nonpos fun i => ?_) hcost
      apply mul_nonpos_of_nonneg_of_nonpos (hc i)
      have hf : ⌊x i + (v : ℝ) * α i⌋ ≤ 0 := by
        apply Int.floor_le_iff.mpr
        norm_num
        exact (add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg hv0' (hα i).1)).trans_lt
          (hx i).2
      exact_mod_cast hf
    · apply le_trans (neg_nonpos.mpr (tsum_nonneg fun i => ?_)) hcost
      apply mul_nonneg (hc i)
      have hf : (0 : ℤ) ≤ ⌊y i - (v : ℝ) * α i⌋ := by
        apply Int.floor_nonneg.mpr
        exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hv0' (hα i).1).trans (hy i).1)
      exact_mod_cast hf

theorem cocycle_bounds {I : Type*} (s : Finset I)
    (x y α c : I → ℝ) (K : ℕ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1)
    (hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hleft : ∀ i ∉ s, x i + (K : ℝ) * α i < 1)
    (hright : ∀ i ∉ s, (K : ℝ) * α i ≤ y i)
    (v : ℤ) (hv : |v| ≤ (K : ℤ)) :
    1 / Real.exp (-(∑' i, c i * (⌊x i + (v : ℝ) * α i⌋ : ℝ))) ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) ∧
    Real.exp (-(∑' i, c i * (⌊y i + ((-v : ℤ) : ℝ) * α i⌋ : ℝ))) ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) := by
  obtain ⟨hforward, hbackward⟩ :=
    signed_floor_sums_le s x y α c K hx hy hα hc hleft hright v hv
  constructor
  · simpa only [Real.exp_neg, one_div, inv_inv] using Real.exp_le_exp.mpr hforward
  · simpa only [Int.cast_neg, neg_mul, sub_eq_add_neg] using
      Real.exp_le_exp.mpr hbackward

theorem coefficient_bounds {I : Type*} (s : Finset I)
    (x y α c : I → ℝ) (K : ℕ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1)
    (hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hleft : ∀ i ∉ s, x i + (K : ℝ) * α i < 1)
    (hright : ∀ i ∉ s, (K : ℝ) * α i ≤ y i)
    (ξ γ : ℓ²(ℤ, ℂ)) (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1)
    (v : ℤ) (hv : |v| ≤ (K : ℤ)) :
    ‖ξ v / (Real.exp (-(∑' i, c i * (⌊x i + (v : ℝ) * α i⌋ : ℝ))) : ℂ)‖ ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) ∧
    ‖(Real.exp (-(∑' i, c i * (⌊y i + ((-v : ℤ) : ℝ) * α i⌋ : ℝ))) : ℂ) *
        conj (γ (-v))‖ ≤ Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) := by
  obtain ⟨hforward, hbackward⟩ :=
    cocycle_bounds s x y α c K hx hy hα hc hleft hright v hv
  have hξv : ‖ξ v‖ ≤ 1 := (lp.norm_apply_le_norm (by norm_num) ξ v).trans hξ
  have hγv : ‖γ (-v)‖ ≤ 1 := (lp.norm_apply_le_norm (by norm_num) γ (-v)).trans hγ
  constructor
  · simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (div_le_div_of_nonneg_right hξv (Real.exp_pos _).le).trans hforward
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_conj]
    exact (mul_le_of_le_one_right (Real.exp_pos _).le hγv).trans hbackward

end Invariant233.CocycleWindowBounds

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCocycleWindow
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate lp
namespace Invariant233.ProductCocycle

theorem finite_window_coefficients {I : Type*} (s : Finset I)
    (θ c : I → ℝ) (K : ℕ) (x y : Space I)
    (hθ : ∀ i, θ i ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hleft : ∀ i ∉ s, representative (x i) + (K : ℝ) * θ i < 1)
    (hright : ∀ i ∉ s, (K : ℝ) * θ i ≤ representative (y i))
    (ξ γ : ℓ²(ℤ, ℂ)) (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1) :
    (∀ v : ℤ, |v| ≤ (K : ℤ) →
      ‖ξ v / (cocycleVersion θ c v x : ℂ)‖ ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i)) ∧
    (∀ v : ℤ, |v| ≤ (K : ℤ) →
      ‖(cocycleVersion θ c (-v) y : ℂ) * conj (γ (-v))‖ ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i)) := by
  have h := fun v hv => CocycleWindowBounds.coefficient_bounds s
    (fun i => representative (x i)) (fun i => representative (y i)) θ c K
    (fun i => representative_mem_Ico (x i)) (fun i => representative_mem_Ico (y i))
    hθ hc hleft hright ξ γ hξ hγ v hv
  exact ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩

end Invariant233.ProductCocycle

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductScaleCocycleWindow
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate lp

namespace Invariant233.ProductScaleData

theorem sum_earlyCoordinates_cost (p : ProductScaleData)
    (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ) :
    (∑ i ∈ p.earlyCoordinates e j, p.C (e i).1) = p.prefixCost j := by
  simp [earlyCoordinates, Finset.sum_sigma, prefixCost, mul_comm]

end Invariant233.ProductScaleData

namespace Invariant233.ProductScaleLaws
variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem current_window_margin (j : ℕ) :
    2 * (p.K j : ℝ) / p.N j = 2 / (p.m j : ℝ) := by
  have hK : (p.K j : ℝ) ≠ 0 := (hp.real_K_pos j).ne'
  have hm : (p.m j : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos j).ne'
  unfold ProductScaleData.N
  field_simp

theorem product_finite_window_coefficients
    (e : ℕ ≃ Σ s, Fin (p.m s)) (θ : ℕ → ℝ)
    (hphase : ∀ i, θ i ∈ Set.Icc (1 / p.N (e i).1) (2 / p.N (e i).1))
    (j : ℕ) (x y : ProductCocycle.Space ℕ)
    (hcurrent : ∀ i, (e i).1 = j →
      ProductCocycle.representative (x i) < 1 - 2 / (p.m j : ℝ) ∧
        2 / (p.m j : ℝ) < ProductCocycle.representative (y i))
    (hfuture : ∀ i, j < (e i).1 →
      ProductCocycle.representative (x i) < 1 - 2 * (p.K j : ℝ) / p.N (e i).1 ∧
        2 * (p.K j : ℝ) / p.N (e i).1 < ProductCocycle.representative (y i))
    (ξ γ : ℓ²(ℤ, ℂ)) (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1) :
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖ξ v / (ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) v x : ℂ)‖ ≤
        p.coefficientBound j) ∧
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖(ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) (-v) y : ℂ) *
        conj (γ (-v))‖ ≤ p.coefficientBound j) := by
  have hN (s : ℕ) : 2 ≤ p.N s := by
    have hm : (100 : ℝ) ≤ p.m s := by exact_mod_cast hp.m_ge_100 s
    have hK : (1 : ℝ) ≤ p.K s := by exact_mod_cast hp.K_pos s
    dsimp [ProductScaleData.N]
    nlinarith
  have hθ (i : ℕ) : θ i ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact (div_nonneg (by norm_num) (by linarith [hN (e i).1])).trans (hphase i).1
    · exact (hphase i).2.trans ((div_le_one (by linarith [hN (e i).1])).mpr (hN _))
  have hexclude (i : ℕ) (hi : i ∉ p.earlyCoordinates e j) :
      ProductCocycle.representative (x i) + (p.K j : ℝ) * θ i < 1 ∧
      (p.K j : ℝ) * θ i ≤ ProductCocycle.representative (y i) := by
    have htag : j ≤ (e i).1 := by simpa only [p.mem_earlyCoordinates, not_lt] using hi
    have hevent : ProductCocycle.representative (x i) < 1 - 2 * (p.K j : ℝ) / p.N (e i).1 ∧
        2 * (p.K j : ℝ) / p.N (e i).1 < ProductCocycle.representative (y i) := by
      rcases eq_or_lt_of_le htag with h | h
      · simpa only [← h, hp.current_window_margin] using hcurrent i h.symm
      · exact hfuture i h
    have hmul := mul_le_mul_of_nonneg_left (hphase i).2 (Nat.cast_nonneg (p.K j))
    have hbound : (p.K j : ℝ) * θ i ≤ 2 * (p.K j : ℝ) / p.N (e i).1 := by
      calc
        _ ≤ (p.K j : ℝ) * (2 / p.N (e i).1) := hmul
        _ = _ := by ring
    constructor
    · linarith [hevent.1]
    · exact hbound.trans hevent.2.le
  have h := ProductCocycle.finite_window_coefficients (p.earlyCoordinates e j)
    θ (fun i => p.C (e i).1) (p.K j) x y hθ (fun i => (hp.C_pos _).le)
    (fun i hi => (hexclude i hi).1) (fun i hi => (hexclude i hi).2) ξ γ hξ hγ
  simpa only [p.sum_earlyCoordinates_cost, ProductScaleData.coefficientBound] using h

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixCircle
attribute [-instance] _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.MixedRadix

@[simp] theorem hybrid_apply_lt {r : ℕ → ℕ} (d e : Digits r) {N n : ℕ} (hn : n < N) :
    hybrid d e N n = e n := ite_eq_left hn

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ProjectionCocycleWindow
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped lp ComplexConjugate InnerProductSpace

namespace Invariant233.ProjectionCocycleWindow

theorem projection_vector_norm_le (P : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hP : IsStarProjection P) : ‖P basisZero‖ ≤ 1 := by
  calc
    ‖P basisZero‖ ≤ ‖P‖ * ‖basisZero‖ := P.le_opNorm basisZero
    _ = ‖P‖ := by simp
    _ ≤ 1 := IsStarProjection.norm_le P hP

theorem complement_vector_norm_le (Q : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hQ : IsStarProjection Q) : ‖(1 - Q) basisZero‖ ≤ 1 :=
  projection_vector_norm_le (1 - Q) hQ.one_sub

theorem central_lower_bounds (P Q : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (a : ℝ) (hP : a ≤ ((P basisZero) 0).re)
    (hQ : ((Q basisZero) 0).re ≤ 1 - a) :
    a ≤ ‖(P basisZero) 0‖ ∧ a ≤ ‖conj (((1 - Q) basisZero) 0)‖ := by
  constructor
  · exact hP.trans (Complex.re_le_norm _)
  · rw [Complex.norm_conj]
    apply le_trans _ (Complex.re_le_norm _)
    have hcoord : ((1 - Q) basisZero) 0 = 1 - (Q basisZero) 0 := by
      simp only [sub_apply, one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply, basisZero_zero]
    rw [hcoord, Complex.sub_re, Complex.one_re]
    linarith

end Invariant233.ProjectionCocycleWindow

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_BlockedProjectionWindow
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.unflatten_flatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ComplexConjugate lp

namespace Invariant233.BlockedProductCoupling

theorem ae_sourceEvent_coefficient_properties {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (θ : ℕ → ℝ)
    (hphase : ∀ i, θ i ∈ Icc (1 / p.N (e i).1) (2 / p.N (e i).1))
    (P : ProjectionField) (hP : ∀ᵐ x ∂ProductModel.baseMeasure, IsStarProjection (P x)) (j : ℕ) :
    ∀ᵐ z ∂sourceLaw p j,
      z ∈ sourceEvent p e (projectionDiagonal P) j →
      (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
        ‖sourceCoefficientA p e θ P z v‖ ≤ p.coefficientBound j) ∧
      (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
        ‖sourceCoefficientB p e θ P z v‖ ≤ p.coefficientBound j) ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤ ‖sourceCoefficientA p e θ P z 0‖ ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤ ‖sourceCoefficientB p e θ P z 0‖ := by
  have hrep := ae_circle_representatives hp.m_ge_100 source_kappa_nonneg source_kappa_le
    (fun s _ => (hp.a_bounds s).1) (fun s _ => (hp.a_bounds s).2)
    (fun s _ => (hp.b_bounds s).1) (fun s _ => (hp.b_bounds s).2) e j
  filter_upwards [hrep, (sourceLaw_quasiMeasurePreserving_left hp e j).ae hP,
    (sourceLaw_quasiMeasurePreserving_right hp e j).ae hP] with z hz hPx hPy
  intro he
  obtain ⟨_, hcurrent, hfuture, hdiagx, hdiagy⟩ := mem_sourceRetainedEvent_iff.mp he
  have hcur : ∀ i, (e i).1 = j →
      ProductCocycle.representative (circleLeftEndpoint e z i) < 1 - 2 / (p.m j : ℝ) ∧
      2 / (p.m j : ℝ) < ProductCocycle.representative (circleRightEndpoint e z i) := by
    intro i hi
    change circleRepresentative _ < _ ∧ _ < circleRepresentative _
    rw [(hz i).1, (hz i).2]
    change (z (e i).1 (e i).2).2.1 < _ ∧ _ < (z (e i).1 (e i).2).2.2
    subst j
    exact hcurrent (e i).2
  have hfut : ∀ i, j < (e i).1 →
      ProductCocycle.representative (circleLeftEndpoint e z i) <
        1 - 2 * (p.K j : ℝ) / p.N (e i).1 ∧
      2 * (p.K j : ℝ) / p.N (e i).1 <
        ProductCocycle.representative (circleRightEndpoint e z i) := by
    intro i hi
    change circleRepresentative _ < _ ∧ _ < circleRepresentative _
    rw [(hz i).1, (hz i).2]
    exact hfuture (e i).1 hi (e i).2
  obtain ⟨hA, hB⟩ := hp.product_finite_window_coefficients e θ hphase j
    (circleLeftEndpoint e z) (circleRightEndpoint e z) hcur hfut
    (P (circleLeftEndpoint e z) sourceBasisZero)
    ((1 - P (circleRightEndpoint e z)) sourceBasisZero)
    (ProjectionCocycleWindow.projection_vector_norm_le _ hPx)
    (ProjectionCocycleWindow.complement_vector_norm_le _ hPy)
  obtain ⟨hA0, hB0⟩ := ProjectionCocycleWindow.central_lower_bounds
    (P (circleLeftEndpoint e z)) (P (circleRightEndpoint e z))
    (1 / ((j + 1 : ℕ) : ℝ)) hdiagx (by
      change 1 / ((j + 1 : ℕ) : ℝ) ≤
        1 - ((P (circleRightEndpoint e z) ProjectionCocycleWindow.basisZero) 0).re at hdiagy
      linarith)
  exact ⟨hA, hB,
    by simpa [sourceCoefficientA, sourceBasisZero, ProjectionCocycleWindow.basisZero] using hA0,
    by simpa [sourceCoefficientB, sourceBasisZero, ProjectionCocycleWindow.basisZero] using hB0⟩

end Invariant233.BlockedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BlockedSourceTransport
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

noncomputable section
open MeasureTheory Set Filter

namespace Invariant233.BlockedProductCoupling

theorem measurable_unflatten {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s)) :
    Measurable (unflatten e) := by unfold unflatten; fun_prop

theorem measurable_flatten {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s)) :
    Measurable (flatten e) := by unfold flatten; fun_prop

theorem source_measurePreserving_flatten {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ) :
    MeasurePreserving (flatten e) (sourceLaw p j)
      (OrderedProductCoupling.law (OrderedProductCoupling.sourceBlocks p.m p.a p.b
        hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
        (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j)) := by
  refine ⟨measurable_flatten e, ?_⟩
  change (law _ _ _ _ _).map _ = _
  rw [law_map_flatten hp.m_ge_100 source_kappa_nonneg source_kappa_le
    (fun s _ => (hp.a_bounds s).1) (fun s _ => (hp.a_bounds s).2)
    (fun s _ => (hp.b_bounds s).1) (fun s _ => (hp.b_bounds s).2)]
  congr 1
  simp [parameters, OrderedProductCoupling.sourceBlocks, OrderedProductCoupling.ofBlocks,
    OrderedProductCoupling.sourceKappa, ProductScaleData.kappa, Nat.cast_add, Nat.cast_one]

theorem source_measurePreserving_unflatten {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ) :
    MeasurePreserving (unflatten e)
      (OrderedProductCoupling.law (OrderedProductCoupling.sourceBlocks p.m p.a p.b
        hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
        (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j))
      (sourceLaw p j) := by
  refine ⟨measurable_unflatten e, ?_⟩
  rw [← (source_measurePreserving_flatten hp e j).map_eq,
    Measure.map_map (measurable_unflatten e) (measurable_flatten e)]
  rw [show unflatten e ∘ flatten e = id from funext (unflatten_flatten e)]
  exact Measure.map_id

theorem ae_flatSourceEvent_coefficient_properties_oai {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (θ : ℕ → ℝ)
    (hphase : ∀ i, θ i ∈ Icc (1 / p.N (e i).1) (2 / p.N (e i).1))
    (P : ProjectionField) (hP : ∀ᵐ x ∂ProductModel.baseMeasure, IsStarProjection (P x)) (j : ℕ) :
    ∀ᵐ ω ∂OrderedProductCoupling.law (OrderedProductCoupling.sourceBlocks p.m p.a p.b
      hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
      (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j),
      ω ∈ flatSourceEvent p e (projectionDiagonal P) j →
      (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
        ‖sourceCoefficientA p e θ P (unflatten e ω) v‖ ≤ p.coefficientBound j) ∧
      (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
        ‖sourceCoefficientB p e θ P (unflatten e ω) v‖ ≤ p.coefficientBound j) ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤ ‖sourceCoefficientA p e θ P (unflatten e ω) 0‖ ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤ ‖sourceCoefficientB p e θ P (unflatten e ω) 0‖ :=
  (source_measurePreserving_unflatten hp e j).quasiMeasurePreserving.ae
    (ae_sourceEvent_coefficient_properties hp e θ hphase P hP j)

end Invariant233.BlockedProductCoupling

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.BlockedProductCoupling.ae_flatSourceEvent_coefficient_properties_oai := @OAI.Invariant233.BlockedProductCoupling.ae_flatSourceEvent_coefficient_properties_oai
