-- Prove2me | solution 1 for OAI.Invariant233.ProductModel.eventually_actualSource_conditionalData
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:32:19.782335+00:00
-- url     : https://prove2.me/submissions/989bc283-5b12-49d6-a18d-b5e2f0a96e22

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Find
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalLExpectation
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003
import Theorems.Thm_OAI_Invariant233_BlockedProductCoupling_ae_flatSourceEvent_coefficient_properties
import Theorems.Thm_OAI_Invariant233_BlockedProductCoupling_eventually_flatSourceEvent_mass

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BlockAverageSum
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
namespace InvariantProjection.IndependentAngles

theorem tsum_fin_block_average {m : ℕ} (hm : 0 < m) (u : ℝ) :
    (∑' _i : Fin m, u / (m : ℝ)) = u := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

theorem summable_block_average (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    (u : ℕ → ℝ) (hu : ∀ s, 0 ≤ u s) (hsum : Summable u) :
    Summable (fun i : Σ s, Fin (m s) => u i.1 / (m i.1 : ℝ)) := by
  apply (summable_sigma_of_nonneg (fun i =>
    div_nonneg (hu i.1) (Nat.cast_nonneg _))).2
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa only [tsum_fin_block_average (hm _)] using hsum

theorem tsum_block_average (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    (u : ℕ → ℝ) (hu : ∀ s, 0 ≤ u s) (hsum : Summable u) :
    (∑' i : Σ s, Fin (m s), u i.1 / (m i.1 : ℝ)) = ∑' s, u s := by
  rw [(summable_block_average m hm u hu hsum).tsum_sigma'
    (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fin_block_average (hm _)]

theorem enumerated_block_average {ι : Type*} (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    (u : ℕ → ℝ) (hu : ∀ s, 0 ≤ u s) (hsum : Summable u)
    (e : ι ≃ Σ s, Fin (m s)) :
    Summable (fun i => u (e i).1 / (m (e i).1 : ℝ)) ∧
    (∑' i, u (e i).1 / (m (e i).1 : ℝ)) = ∑' s, u s := by
  constructor
  · exact e.summable_iff.mpr (summable_block_average m hm u hu hsum)
  · exact (e.tsum_eq _).trans (tsum_block_average m hm u hu hsum)

end InvariantProjection.IndependentAngles

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

lemma intervalLaw_ae_mem (a b : ℝ) : ∀ᵐ x ∂intervalLaw a b, x ∈ Ico a b :=
  ae_cond_mem measurableSet_Ico

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
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace Invariant233.OneCoordinateCoupling

open CouplingMixture CouplingMarginalBounds

theorem labelledLaw_ae_tag_interval (κ m a b t : ℝ) :
    ∀ᵐ z ∂labelledLaw κ m a b t, z.1 = some (4 : Fin 5) →
      z.2.1 < 1 / m ∧ 1 - 1 / m ≤ z.2.2 := by
  let P : Option (Fin 5) × (ℝ × ℝ) → Prop := fun z =>
    z.1 = some (4 : Fin 5) → z.2.1 < 1 / m ∧ 1 - 1 / m ≤ z.2.2
  have hP : MeasurableSet {z | P z} := by
    simp only [P, imp_iff_not_or]
    change MeasurableSet ({z : Option (Fin 5) × (ℝ × ℝ) | z.1 = some (4 : Fin 5)}ᶜ ∪
      {z : Option (Fin 5) × (ℝ × ℝ) | z.2.1 < 1 / m ∧ 1 - 1 / m ≤ z.2.2})
    exact (measurable_fst (measurableSet_singleton _)).compl.union
      ((measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const).inter
       (measurableSet_le measurable_const (measurable_snd.comp measurable_snd)))
  change ∀ᵐ z ∂labelledLaw κ m a b t, P z
  rw [labelledLaw, labelledMixture, ae_add_measure_iff, ae_finsetSum_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hP).2
    exact Filter.Eventually.of_forall (by intro z; simp [P])
  · intro i _
    apply Measure.ae_smul_measure
    apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hP).2
    by_cases hi : i = 4
    · subst i
      change ∀ᵐ z ∂(intervalLaw 0 (1 / m)).prod (intervalLaw (1 - 1 / m) 1),
        P (some 4, z)
      have : IsZeroOrProbabilityMeasure (intervalLaw 0 (1 / m)) := inferInstanceAs
        (IsZeroOrProbabilityMeasure (volume[|Ico 0 (1 / m)]))
      have : IsZeroOrProbabilityMeasure (intervalLaw (1 - 1 / m) 1) := inferInstanceAs
        (IsZeroOrProbabilityMeasure (volume[|Ico (1 - 1 / m) 1]))
      have hs : MeasurableSet {z : ℝ × ℝ | P (some 4, z)} :=
        hP.preimage (measurable_const.prodMk measurable_id)
      rw [Measure.ae_prod_iff_ae_ae hs]
      filter_upwards [intervalLaw_ae_mem 0 (1 / m)] with x hx
      filter_upwards [intervalLaw_ae_mem (1 - 1 / m) 1] with y hy
      exact fun _ => ⟨hx.2, hy.1⟩
    · exact Filter.Eventually.of_forall (by intro z; simp [P, hi])

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

end Invariant233.BlockedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_BlockedCircleEvent
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

end Invariant233.BlockedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BlockedSourceEvent
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

end Invariant233.BlockedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_InvariantConullCore
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233

theorem exists_invariant_conull_subset
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (σ : ℤ → X → X)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ k n x, σ (k + n) x = σ n (σ k x))
    (hmp : ∀ k, MeasurePreserving (σ k) μ μ)
    {s : Set X} (hs : MeasurableSet s) (hfull : ∀ᵐ x ∂μ, x ∈ s) :
    ∃ t : Set X, MeasurableSet t ∧ t ⊆ s ∧
      (∀ᵐ x ∂μ, x ∈ t) ∧ ∀ k, σ k ⁻¹' t = t := by
  let t : Set X := ⋂ k : ℤ, σ k ⁻¹' s
  have ht_mem : ∀ x, x ∈ t ↔ ∀ k, σ k x ∈ s := by
    intro x
    simp only [t, mem_iInter, mem_preimage]
  refine ⟨t, MeasurableSet.iInter (fun k ↦ hs.preimage (hmp k).measurable), ?_, ?_, ?_⟩
  · intro x hx
    simpa only [hzero] using (ht_mem x).mp hx 0
  · have h : ∀ᵐ x ∂μ, ∀ k : ℤ, σ k x ∈ s :=
      ae_all_iff.mpr (fun k ↦ (hmp k).quasiMeasurePreserving.ae hfull)
    exact h.mono fun x hx ↦ (ht_mem x).mpr hx
  · intro k
    ext x
    change σ k x ∈ t ↔ x ∈ t
    rw [ht_mem, ht_mem]
    constructor
    · intro hx n
      have h := hx (n - k)
      rw [← hadd] at h
      rw [← add_sub_assoc, add_comm k n, add_sub_cancel_right] at h
      exact h
    · intro hx n
      rw [← hadd]
      exact hx (k + n)

theorem exists_invariant_conull_property
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (σ : ℤ → X → X)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ k n x, σ (k + n) x = σ n (σ k x))
    (hmp : ∀ k, MeasurePreserving (σ k) μ μ)
    (P : X → Prop) (hP : ∀ᵐ x ∂μ, P x) :
    ∃ t : Set X, MeasurableSet t ∧ (∀ᵐ x ∂μ, x ∈ t) ∧
      (∀ x ∈ t, P x) ∧ ∀ k, σ k ⁻¹' t = t := by
  obtain ⟨u, hsub, hu, hnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hP)
  have hfull : ∀ᵐ x ∂μ, x ∈ uᶜ := by
    rw [ae_iff]
    simpa using hnull
  obtain ⟨t, ht, htu, htf, hinv⟩ :=
    exists_invariant_conull_subset σ hzero hadd hmp hu.compl hfull
  refine ⟨t, ht, htf, ?_, hinv⟩
  intro x hx
  by_contra hbad
  exact htu hx (hsub hbad)

theorem exists_invariant_conull_forall
    {X I : Type*} [MeasurableSpace X] [Countable I] {μ : Measure X}
    (σ : ℤ → X → X)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ k n x, σ (k + n) x = σ n (σ k x))
    (hmp : ∀ k, MeasurePreserving (σ k) μ μ)
    (P : I → X → Prop) (hP : ∀ i, ∀ᵐ x ∂μ, P i x) :
    ∃ t : Set X, MeasurableSet t ∧ (∀ᵐ x ∂μ, x ∈ t) ∧
      (∀ x ∈ t, ∀ k i, P i (σ k x)) ∧ ∀ k, σ k ⁻¹' t = t := by
  obtain ⟨t, ht, htf, hprop, hinv⟩ :=
    exists_invariant_conull_property σ hzero hadd hmp
      (fun x ↦ ∀ i, P i x) (ae_all_iff.mpr hP)
  refine ⟨t, ht, htf, ?_, hinv⟩
  intro x hx k i
  apply hprop (σ k x) _ i
  change x ∈ σ k ⁻¹' t
  rw [hinv]
  exact hx

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleRepresentative
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.CocycleSupport

theorem measurePreserving_productRepresentative {ι : Type*} (i : ι) :
    MeasurePreserving
      (fun x : ι → UnitAddCircle => ((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
      (volume.restrict (Ico (0 : ℝ) 1)) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  exact measurePreserving_circleRepresentative.comp
    (measurePreserving_eval_infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)) i)

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CocycleSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.CocycleSupport

theorem uniform_floor_ne_zero_le (t : ℝ) :
    (volume.restrict (Ico (0 : ℝ) 1)) {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ≤
      ENNReal.ofReal |t| := by
  have hm : MeasurableSet {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
    ((measurable_id.add_const t).floor (measurableSet_singleton 0)).compl
  rw [Measure.restrict_apply hm]
  rcases le_or_gt 0 t with ht | ht
  · calc
      volume ({x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ∩ Ico 0 1) ≤
          volume (Ico (1 - t) 1) := by
        apply measure_mono
        rintro x ⟨hx, hx0, hx1⟩
        refine ⟨?_, hx1⟩
        by_contra h
        apply hx
        apply Int.floor_eq_zero_iff.mpr
        constructor <;> linarith
      _ = ENNReal.ofReal |t| := by
        rw [Real.volume_Ico, abs_of_nonneg ht]
        congr 1
        ring
  · calc
      volume ({x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ∩ Ico 0 1) ≤
          volume (Ico 0 (-t)) := by
        apply measure_mono
        rintro x ⟨hx, hx0, hx1⟩
        refine ⟨hx0, ?_⟩
        by_contra h
        apply hx
        apply Int.floor_eq_zero_iff.mpr
        constructor <;> linarith
      _ = ENNReal.ofReal |t| := by
        rw [Real.volume_Ico, sub_zero, abs_of_neg ht]

theorem ae_finite_support_of_tsum_ne_top {Ω ι A : Type*}
    [MeasurableSpace Ω] [Countable ι] [Zero A]
    (μ : Measure Ω) (a : ι → Ω → A)
    (h : (∑' i, μ {x | a i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, (Function.support (fun i => a i x)).Finite := by
  exact ae_finite_setOfPred_mem h

theorem ae_all_finite_support_of_tsum_ne_top {Ω ι K A : Type*}
    [MeasurableSpace Ω] [Countable ι] [Countable K] [Zero A]
    (μ : Measure Ω) (a : K → ι → Ω → A)
    (h : ∀ k, (∑' i, μ {x | a k i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ k, (Function.support (fun i => a k i x)).Finite := by
  rw [ae_all_iff]
  intro k
  exact ae_finite_support_of_tsum_ne_top μ (a k) (h k)

theorem measure_floor_ne_zero_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (u : Ω → ℝ) (hu : Measurable u)
    (hlaw : μ.map u = volume.restrict (Ico (0 : ℝ) 1)) (t : ℝ) :
    μ {x | ⌊u x + t⌋ ≠ (0 : ℤ)} ≤ ENNReal.ofReal |t| := by
  have hm : MeasurableSet {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
    ((measurable_id.add_const t).floor (measurableSet_singleton 0)).compl
  calc
    μ {x | ⌊u x + t⌋ ≠ (0 : ℤ)} =
        (μ.map u) {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
      (Measure.map_apply hu hm).symm
    _ = (volume.restrict (Ico (0 : ℝ) 1))
        {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} := by rw [hlaw]
    _ ≤ ENNReal.ofReal |t| := uniform_floor_ne_zero_le t

theorem ae_all_int_finite_floor_support {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (u : ι → Ω → ℝ) (hu : ∀ i, Measurable (u i))
    (hlaw : ∀ i, μ.map (u i) = volume.restrict (Ico (0 : ℝ) 1))
    (θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂μ, ∀ k : ℤ,
      (Function.support (fun i => (⌊u i x + (k : ℝ) * θ i⌋ : ℤ))).Finite := by
  apply ae_all_finite_support_of_tsum_ne_top
  intro k
  apply ne_top_of_le_ne_top ((hθ.mul_left |(k : ℝ)|).tsum_ofReal_ne_top)
  apply ENNReal.tsum_le_tsum
  intro i
  simpa only [abs_mul, abs_of_nonneg (hθ0 i)] using
    measure_floor_ne_zero_le μ (u i) (hu i) (hlaw i) ((k : ℝ) * θ i)

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.CocycleSupport

theorem ae_product_all_int_finite_floor_support {ι : Type*} [Countable ι]
    (θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂(Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))),
      ∀ k : ℤ,
        (Function.support (fun i =>
          (⌊((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ) + (k : ℝ) * θ i⌋ : ℤ))).Finite := by
  exact ae_all_int_finite_floor_support
    (Ω := ι → UnitAddCircle) (ι := ι)
    (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
    (fun i x => ((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ))
    (fun i => (measurePreserving_productRepresentative i).measurable)
    (fun i => (measurePreserving_productRepresentative i).map_eq)
    θ hθ0 hθ

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FloorCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
namespace FloorCocycle

theorem floor_fract_add (x y : ℝ) :
    ⌊Int.fract x + y⌋ + ⌊x⌋ = ⌊x + y⌋ := by
  rw [Int.fract, sub_add_eq_add_sub, Int.floor_sub_intCast]
  omega

theorem floor_cocycle (u α : ℝ) (v n : ℤ) :
    ⌊u + (v : ℝ) * α⌋ + ⌊Int.fract (u + (v : ℝ) * α) + (n : ℝ) * α⌋ =
      ⌊u + ((v + n : ℤ) : ℝ) * α⌋ := by
  rw [add_comm, floor_fract_add]
  congr 1
  push_cast
  ring

end FloorCocycle
end Invariant233

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

theorem summable_weighted_int {I : Type*} (c : I → ℝ) {a : I → ℤ}
    (ha : HasFiniteSupport a) : Summable (fun i ↦ c i * (a i : ℝ)) := by
  apply summable_of_hasFiniteSupport
  exact HasFiniteSupport.mul_right c (ha.fun_comp (by simp))

theorem exp_tsum_floor_cocycle {I : Type*} (x θ c : I → ℝ) (k n : ℤ)
    (hk : HasFiniteSupport (fun i ↦ ⌊x i + (k : ℝ) * θ i⌋))
    (hn : HasFiniteSupport
      (fun i ↦ ⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋)) :
    Real.exp (-(∑' i, c i * (⌊x i + ((k + n : ℤ) : ℝ) * θ i⌋ : ℝ))) =
      Real.exp (-(∑' i, c i *
        (⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋ : ℝ))) *
      Real.exp (-(∑' i, c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ))) := by
  have hcoord (i : I) :
      c i * (⌊x i + ((k + n : ℤ) : ℝ) * θ i⌋ : ℝ) =
        c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ) +
        c i * (⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋ : ℝ) := by
    rw [← FloorCocycle.floor_cocycle]
    push_cast
    ring
  rw [tsum_congr hcoord,
    (summable_weighted_int c hk).tsum_add (summable_weighted_int c hn),
    neg_add, Real.exp_add, mul_comm]

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

theorem representative_add (x : UnitAddCircle) (t : ℝ) :
    representative (x + (t : UnitAddCircle)) = Int.fract (representative x + t) := by
  have hx : x + (t : UnitAddCircle) =
      ((representative x + t : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_add, coe_representative]
  rw [hx]
  change ((AddCircle.equivIco (1 : ℝ) 0
    ((representative x + t : ℝ) : UnitAddCircle)) : ℝ) = _
  simpa only [div_one, mul_one] using
    (AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) (representative x + t))

theorem representative_rotate {I : Type*} (θ : I → ℝ) (k : ℤ)
    (x : Space I) (i : I) :
    representative (rotate θ k x i) =
      Int.fract (representative (x i) + (k : ℝ) * θ i) :=
  representative_add (x i) ((k : ℝ) * θ i)

theorem measurable_cocycleVersion {I : Type*} [Countable I]
    (θ c : I → ℝ) (k : ℤ) : Measurable (cocycleVersion θ c k) := by
  apply Real.measurable_exp.comp
  apply Measurable.neg
  apply Measurable.tsum
  intro i
  have hrep : Measurable (fun x : Space I ↦ representative (x i)) :=
    measurable_representative.comp (measurable_pi_apply i)
  exact measurable_const.mul ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
    ((hrep.add_const ((k : ℝ) * θ i)).floor))

theorem cocycleVersion_pos {I : Type*} (θ c : I → ℝ) (k : ℤ) (x : Space I) :
    0 < cocycleVersion θ c k x :=
  Real.exp_pos _

@[simp] theorem cocycleVersion_zero {I : Type*} (θ c : I → ℝ) (x : Space I) :
    cocycleVersion θ c 0 x = 1 := by
  simp only [cocycleVersion, Int.cast_zero, zero_mul, add_zero]
  exact FiniteSupportCocycle.exp_tsum_floor_zero _ c
    (fun i ↦ representative_mem_Ico (x i))

theorem cocycleVersion_add_of_finite_support {I : Type*}
    (θ c : I → ℝ) (k n : ℤ) (x : Space I)
    (hk : HasFiniteSupport
      (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋))
    (hn : HasFiniteSupport
      (fun i ↦ ⌊representative (rotate θ k x i) + (n : ℝ) * θ i⌋)) :
    cocycleVersion θ c (k + n) x =
      cocycleVersion θ c n (rotate θ k x) * cocycleVersion θ c k x := by
  simp only [cocycleVersion, representative_rotate] at hn ⊢
  exact FiniteSupportCocycle.exp_tsum_floor_cocycle _ θ c k n hk hn

theorem exists_invariant_cocycle_core {I : Type*} [Countable I]
    (θ : I → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∃ s : Set (Space I), MeasurableSet s ∧ (∀ᵐ x ∂haar I, x ∈ s) ∧
      (∀ k : ℤ, rotate θ k ⁻¹' s = s) ∧
      (∀ x ∈ s, ∀ k : ℤ, HasFiniteSupport
        (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋)) ∧
      (∀ x ∈ s, ∀ (c : I → ℝ) (k n : ℤ),
        cocycleVersion θ c (k + n) x =
          cocycleVersion θ c n (rotate θ k x) * cocycleVersion θ c k x) := by
  have hall : ∀ᵐ x ∂haar I, ∀ k : ℤ, HasFiniteSupport
      (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋) :=
    CocycleSupport.ae_product_all_int_finite_floor_support θ hθ0 hθ
  obtain ⟨s, hs, hfull, hprop, hinv⟩ :=
    Invariant233.exists_invariant_conull_forall (rotate θ) (rotate_zero θ)
      (rotate_add θ) (measurePreserving_rotate θ)
      (fun (k : ℤ) (x : Space I) ↦ HasFiniteSupport
        (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋))
      (ae_all_iff.mp hall)
  have hsupport (x : Space I) (hx : x ∈ s) (k : ℤ) :
      HasFiniteSupport (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋) := by
    simpa only [rotate_zero] using hprop x hx 0 k
  refine ⟨s, hs, hfull, hinv, hsupport, ?_⟩
  intro x hx c k n
  exact cocycleVersion_add_of_finite_support θ c k n x
    (hsupport x hx k) (hprop x hx k n)

end Invariant233.ProductCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CocycleWindowBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set

namespace Invariant233.ProductCocycle

theorem cocycleVersion_le_one_of_nonneg_time {I : Type*}
    (θ c : I → ℝ) (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (k : ℤ) (hk : 0 ≤ k) (x : Space I) : cocycleVersion θ c k x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  apply neg_nonpos.mpr
  apply tsum_nonneg
  intro i
  apply mul_nonneg (hc i)
  have hfloor : (0 : ℤ) ≤ ⌊representative (x i) + (k : ℝ) * θ i⌋ :=
    Int.floor_nonneg.mpr (add_nonneg (representative_mem_Ico (x i)).1
      (mul_nonneg (by exact_mod_cast hk) (hθ i)))
  exact_mod_cast hfloor

end Invariant233.ProductCocycle

open scoped BigOperators ComplexConjugate lp

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
-- module Solutions.Q234_IR.IrrationalRotation_Operators_BlockedProjectionWindow
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ComplexConjugate lp

namespace Invariant233.BlockedProductCoupling

theorem measurable_sourceEvent (p : ProductScaleData)
    (e : ℕ ≃ Σ s, Fin (p.m s)) {r : ProductModel.Base → ℝ}
    (hr : Measurable r) (j : ℕ) : MeasurableSet (sourceEvent p e r j) := by
  have hx : Measurable (circleLeftEndpoint e) := by
    unfold circleLeftEndpoint toCircle leftEndpoint flatten OrderedProductCoupling.leftEndpoint
    fun_prop
  have hy : Measurable (circleRightEndpoint e) := by
    unfold circleRightEndpoint toCircle rightEndpoint flatten OrderedProductCoupling.rightEndpoint
    fun_prop
  have hc : MeasurableSet (currentEvent p.m j) := by
    change MeasurableSet ({z : Sample p.m | ∃ i, (z j i).1 = some (4 : Fin 5)} ∩
      {z | ∀ i, (z j i).2.1 < 1 - 2 / (p.m j : ℝ) ∧
        2 / (p.m j : ℝ) < (z j i).2.2})
    apply MeasurableSet.inter
    · simp only [ofPred_exists]
      exact MeasurableSet.iUnion fun i => (by fun_prop :
        Measurable (fun z : Sample p.m => (z j i).1)) (measurableSet_singleton _)
    · simp only [ofPred_forall]
      apply MeasurableSet.iInter
      intro i
      have hxi : Measurable (fun z : Sample p.m => (z j i).2.1) := by fun_prop
      have hyi : Measurable (fun z : Sample p.m => (z j i).2.2) := by fun_prop
      exact (measurableSet_lt hxi measurable_const).inter
        (measurableSet_lt measurable_const hyi)
  have hf : MeasurableSet (futureBad p.m (fun s => (p.K s : ℝ)) j) := by
    apply MeasurableSet.iUnion
    intro n
    apply MeasurableSet.iUnion
    intro i
    have hxi : Measurable (fun z : Sample p.m => (z (j + 1 + n) i).2.1) := by fun_prop
    have hyi : Measurable (fun z : Sample p.m => (z (j + 1 + n) i).2.2) := by fun_prop
    exact (measurableSet_le measurable_const hxi).union
      (measurableSet_le hyi measurable_const)
  exact hc.diff (hf.union
    ((measurableSet_lt (hr.comp hx) measurable_const).union
      (measurableSet_lt (measurable_const.sub (hr.comp hy)) measurable_const)))

end Invariant233.BlockedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BlockedSourceTransport
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.ProductPhases.card_consecutiveBlock
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

theorem measurable_flatSourceEvent (p : ProductScaleData)
    (e : ℕ ≃ Σ s, Fin (p.m s)) {r : ProductModel.Base → ℝ} (hr : Measurable r) (j : ℕ) :
    MeasurableSet (flatSourceEvent p e r j) :=
  (measurable_sourceEvent p e hr j).preimage (measurable_unflatten e)

theorem ae_sourceEvent_tag_endpoints {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (r : ProductModel.Base → ℝ) (j : ℕ) :
    ∀ᵐ z ∂sourceLaw p j, z ∈ sourceEvent p e r j →
      ∃ k ∈ ProductPhases.consecutiveBlock p.m j,
        circleRepresentative (circleLeftEndpoint e z k) < 1 / (p.m j : ℝ) ∧
        1 - 1 / (p.m j : ℝ) ≤ circleRepresentative (circleRightEndpoint e z k) := by
  have ht : ∀ᵐ z ∂sourceLaw p j, ∀ i : Fin (p.m j),
      (z j i).1 = some (4 : Fin 5) →
        (z j i).2.1 < 1 / (p.m j : ℝ) ∧ 1 - 1 / (p.m j : ℝ) ≤ (z j i).2.2 := by
    apply ae_all_iff.mpr
    intro i
    have h := OneCoordinateCoupling.labelledLaw_ae_tag_interval
      (ProductScaleData.kappa j) (p.m j) (p.a j) (p.b j) (if j = j then 1 else 0)
    rw [← law_map_coordinate hp.m_ge_100 source_kappa_nonneg source_kappa_le
      (fun s _ => (hp.a_bounds s).1) (fun s _ => (hp.a_bounds s).2)
      (fun s _ => (hp.b_bounds s).1) (fun s _ => (hp.b_bounds s).2) j j i] at h
    exact ae_of_ae_map (by fun_prop : Measurable (fun z : Sample p.m => z j i)).aemeasurable h
  have hrep := ae_circle_representatives hp.m_ge_100 source_kappa_nonneg source_kappa_le
    (fun s _ => (hp.a_bounds s).1) (fun s _ => (hp.a_bounds s).2)
    (fun s _ => (hp.b_bounds s).1) (fun s _ => (hp.b_bounds s).2) e j
  filter_upwards [ht, hrep] with z hz hr
  intro hE
  obtain ⟨i, hi⟩ := (mem_sourceRetainedEvent_iff.mp hE).1
  let k := e.symm ⟨j, i⟩
  have hk : k ∈ ProductPhases.consecutiveBlock p.m j := by
    dsimp [k]
    rw [he]
    simp only [ProductPhases.consecutiveBlock, Finset.mem_Ico]
    have := i.isLt
    omega
  have hcoord : flatten e z k = z j i := by
    change (fun q : Σ s, Fin (p.m s) => z q.1 q.2) (e (e.symm ⟨j, i⟩)) = _
    rw [e.apply_symm_apply]
  refine ⟨k, hk, ?_⟩
  rw [(hr k).1, (hr k).2]
  change (flatten e z k).2.1 < _ ∧ _ ≤ (flatten e z k).2.2
  rw [hcoord]
  exact hz i hi

theorem ae_flatSourceEvent_tag_endpoints {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (r : ProductModel.Base → ℝ) (j : ℕ) :
    ∀ᵐ ω ∂OrderedProductCoupling.law (OrderedProductCoupling.sourceBlocks p.m p.a p.b
      hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
      (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j),
      ω ∈ flatSourceEvent p e r j →
      ∃ k ∈ ProductPhases.consecutiveBlock p.m j,
        circleRepresentative (OrderedProductCoupling.circleLeftEndpoint ω k) < 1 / (p.m j : ℝ) ∧
        1 - 1 / (p.m j : ℝ) ≤ circleRepresentative (OrderedProductCoupling.circleRightEndpoint ω k) := by
  have h := (source_measurePreserving_unflatten hp e j).quasiMeasurePreserving.ae
    (ae_sourceEvent_tag_endpoints hp e he r j)
  simpa only [circleLeftEndpoint_unflatten, circleRightEndpoint_unflatten,
    flatSourceEvent, mem_preimage] using h

end Invariant233.BlockedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConvolutionRatios
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ComplexConjugate ENNReal lp

namespace InvariantProjection

theorem cocycle_two_ratio_bounds
    (Fx Fy : ℤ → ℝ) (hFx : ∀ k, 0 < Fx k) (hFy : ∀ k, 0 < Fy k)
    (hx : Antitone Fx) (hy : Antitone Fy)
    (hxy : ∀ k, Fy k / Fx k ≤ 1) (n : ℕ) (v : ℤ) :
    0 < Fy ((n : ℤ) + v) / Fx v ∧
      Fy ((n : ℤ) + v) / Fx v ≤ min (Fy v / Fx v)
        (Fy ((n : ℤ) + v) / Fx ((n : ℤ) + v)) ∧
      min (Fy v / Fx v) (Fy ((n : ℤ) + v) / Fx ((n : ℤ) + v)) ≤ 1 := by
  have hv : v ≤ (n : ℤ) + v := by omega
  refine ⟨div_pos (hFy _) (hFx _), le_min ?_ ?_, (min_le_left _ _).trans (hxy v)⟩
  · exact div_le_div_of_nonneg_right (hy hv) (le_of_lt (hFx v))
  · exact div_le_div_of_nonneg_left (le_of_lt (hFy _)) (hFx _) (hx hv)

end InvariantProjection

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_DensityTransport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.DensityTransport

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} {F : X → Y} {G : Y → X}

theorem map_inverse_eq (hF : Measurable F) (hG : Measurable G)
    (hmap : μ.map F = ν) (hinv : ∀ᵐ x ∂μ, G (F x) = x) : ν.map G = μ := by
  rw [← hmap, Measure.map_map hG hF]
  calc
    μ.map (G ∘ F) = μ.map id := Measure.map_congr hinv
    _ = μ := Measure.map_id

theorem map_withDensity_eq (hF : Measurable F) (hG : Measurable G)
    (hmap : μ.map F = ν) (hinv : ∀ᵐ x ∂μ, G (F x) = x)
    {h : X → ℝ≥0∞} (hh : Measurable h) :
    (μ.withDensity h).map F = ν.withDensity (h ∘ G) := by
  ext s hs
  rw [Measure.map_apply hF hs, withDensity_apply _ (hF hs), withDensity_apply _ hs,
    ← hmap, Measure.restrict_map hF hs,
    lintegral_map' (hh.comp hG).aemeasurable hF.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hinv] with x hx
  simp only [Function.comp_apply, hx]

theorem eLpNorm_comp_inverse {E : Type*} [NormedAddCommGroup E]
    (hF : Measurable F) (hG : Measurable G)
    (hmap : μ.map F = ν) (hinv : ∀ᵐ x ∂μ, G (F x) = x)
    {h : X → E} (hh : AEStronglyMeasurable h μ) (p : ℝ≥0∞) :
    eLpNorm (h ∘ G) p ν = eLpNorm h p μ := by
  exact eLpNorm_comp_measurePreserving hh
    ⟨hG, map_inverse_eq hF hG hmap hinv⟩

theorem real_density_transport (hF : Measurable F) (hG : Measurable G)
    (hmap : μ.map F = ν) (hinv : ∀ᵐ x ∂μ, G (F x) = x)
    {h : X → ℝ} (hh : Measurable h) :
    (μ.withDensity (fun x => ENNReal.ofReal (h x))).map F =
      ν.withDensity (fun y => ENNReal.ofReal (h (G y))) ∧
    eLpNorm (h ∘ G) 2 ν = eLpNorm h 2 μ := by
  constructor
  · exact map_withDensity_eq hF hG hmap hinv hh.ennreal_ofReal
  · exact eLpNorm_comp_inverse hF hG hmap hinv hh.aestronglyMeasurable 2

theorem real_density_transport_ae (hF : Measurable F) (hG : Measurable G)
    (hmap : μ.map F = ν) (hinv : ∀ᵐ x ∂μ, G (F x) = x)
    {h : X → ℝ} (hh : AEMeasurable h μ) :
    (μ.withDensity (fun x => ENNReal.ofReal (h x))).map F =
      ν.withDensity (fun y => ENNReal.ofReal (h (G y))) ∧
    eLpNorm (h ∘ G) 2 ν = eLpNorm h 2 μ := by
  have hback : ν.map G = μ := map_inverse_eq hF hG hmap hinv
  have ht : Filter.Tendsto G (ae ν) (ae μ) := by
    rw [← hback]
    exact Measure.tendsto_ae_map hG.aemeasurable
  have heq : h =ᵐ[μ] hh.mk h := hh.ae_eq_mk
  have heqG : h ∘ G =ᵐ[ν] hh.mk h ∘ G := heq.comp_tendsto ht
  obtain ⟨hweighted, hnorm⟩ := real_density_transport hF hG hmap hinv hh.measurable_mk
  constructor
  · have hx : μ.withDensity (fun x => ENNReal.ofReal (h x)) =
        μ.withDensity (fun x => ENNReal.ofReal (hh.mk h x)) := by
      apply withDensity_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]
    have hy : ν.withDensity (fun y => ENNReal.ofReal (h (G y))) =
        ν.withDensity (fun y => ENNReal.ofReal (hh.mk h (G y))) := by
      apply withDensity_congr_ae
      filter_upwards [heqG] with y hy
      exact congrArg ENNReal.ofReal hy
    rw [hx, hy]
    exact hweighted
  · calc
      eLpNorm (h ∘ G) 2 ν = eLpNorm (hh.mk h ∘ G) 2 ν := eLpNorm_congr_ae heqG
      _ = eLpNorm (hh.mk h) 2 μ := hnorm
      _ = eLpNorm h 2 μ := (eLpNorm_congr_ae heq).symm

end Invariant233.DensityTransport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_OrbitInvariance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.OrbitInvariance

section Ring
variable {A : Type*} [Ring A] {p T : A}

theorem invariant_iff_compression :
    (1 - p) * T * p = 0 ↔ p * T * p = T * p := by
  rw [sub_mul, one_mul, sub_mul]
  exact sub_eq_zero.trans eq_comm

theorem invariant_pow (hp : IsIdempotentElem p)
    (hT : (1 - p) * T * p = 0) (n : ℕ) :
    (1 - p) * T ^ n * p = 0 := by
  have hTp : p * T * p = T * p := invariant_iff_compression.mp hT
  apply invariant_iff_compression.mpr
  induction n with
  | zero => simpa using hp.eq
  | succ n ih =>
    calc
      p * T ^ (n + 1) * p = p * T ^ n * (T * p) := by rw [pow_succ]; simp [mul_assoc]
      _ = p * T ^ n * (p * T * p) := by rw [hTp]
      _ = (p * T ^ n * p) * T * p := by simp [mul_assoc]
      _ = (T ^ n * p) * T * p := by rw [ih]
      _ = T ^ n * (p * T * p) := by simp [mul_assoc]
      _ = T ^ n * (T * p) := by rw [hTp]
      _ = T ^ (n + 1) * p := by rw [pow_succ]; simp [mul_assoc]

theorem endpoint_inclusion_pow {q D : A} (hq : IsIdempotentElem q)
    (hT : (1 - q) * T * q = 0) (hD : (1 - q) * D * p = 0) (n : ℕ) :
    (1 - q) * T ^ n * D * p = 0 := by
  have hD' : q * (D * p) = D * p := by
    rw [sub_mul, one_mul, sub_mul, sub_eq_zero] at hD
    simpa only [mul_assoc] using hD.symm
  calc
    (1 - q) * T ^ n * D * p = ((1 - q) * T ^ n) * (D * p) := by
      simp only [mul_assoc]
    _ = ((1 - q) * T ^ n) * (q * (D * p)) := by rw [hD']
    _ = ((1 - q) * T ^ n * q) * (D * p) := by simp only [mul_assoc]
    _ = 0 := by rw [invariant_pow hq hT n, zero_mul]

end Ring


end Invariant233.OrbitInvariance

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_RepresentedInvariance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.L2Multiplication

variable {X E ι : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Countable ι]

theorem ae_invariance_of_represented
    (b : HilbertBasis ι ℂ E)
    (p T : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (P W : X → E →L[ℂ] E)
    (hp : ∀ f : Lp E 2 μ, p f =ᵐ[μ] fun x => P x (f x))
    (hT : ∀ f : Lp E 2 μ, T f =ᵐ[μ] fun x => W x (f x))
    (hinv : (1 - p) * T * p = 0) :
    ∀ᵐ x ∂μ, (1 - P x) * W x * P x = 0 := by
  have hzero : ∀ f : Lp E 2 μ, (0 : Lp E 2 μ →L[ℂ] Lp E 2 μ) f =ᵐ[μ]
      fun x => ((1 - P x) * W x * P x) (f x) := by
    intro f
    have hfix : T (p f) = p (T (p f)) := by
      have h := congrArg (fun A : Lp E 2 μ →L[ℂ] Lp E 2 μ => A f) hinv
      simpa only [mul_apply_eq_comp, sub_apply,
        one_apply_eq_self, zero_apply, sub_eq_zero] using h
    filter_upwards [hp f, hT (p f), hp (T (p f)), Lp.coeFn_zero E 2 μ]
      with x hpf hTf hpTf h0
    change (0 : Lp E 2 μ) x = _
    rw [h0]
    have heq : W x (P x (f x)) = P x (W x (P x (f x))) := by
      calc
        W x (P x (f x)) = T (p f) x := by rw [hTf, hpf]
        _ = p (T (p f)) x := congrArg (fun g : Lp E 2 μ => g x) hfix
        _ = P x (W x (P x (f x))) := by rw [hpTf, hTf, hpf]
    change (0 : E) = W x (P x (f x)) - P x (W x (P x (f x)))
    exact (sub_eq_zero.mpr heq).symm
  have huniq := field_unique_of_representation b
    (0 : Lp E 2 μ →L[ℂ] Lp E 2 μ) (fun x => (1 - P x) * W x * P x)
    (fun _ => 0) hzero (fun f => by
      filter_upwards [Lp.coeFn_zero E 2 μ] with x hx
      change (0 : Lp E 2 μ) x = (0 : E)
      exact hx)
  exact huniq

end Invariant233.L2Multiplication

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_BlockProductCoupling
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Invariant233.OrderedProductCoupling
open InvariantProjection.IndependentAngles

lemma summable_sourceKappa_sq : Summable (fun s => sourceKappa s ^ 2) := by
  have hbase : Summable (fun s : ℕ => 1 / ((s + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.mpr (by norm_num))
  apply (hbase.mul_left (1 / 10000 : ℝ)).congr
  intro s
  have hs : (s : ℝ) + 1 ≠ 0 := by positivity
  simp only [sourceKappa, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

section BlockData
variable (m : ℕ → ℕ) (κ a b : ℕ → ℝ)
    (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
    (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (tag : ℕ)

lemma energyBound_ofBlocks (i : ℕ) :
    energyBound (ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag) i =
      (20 * (2 * κ (e i).1 ^ 2 + if (e i).1 = tag then 1 else 0)) /
        (m (e i).1 : ℝ) := by
  unfold energyBound ofBlocks
  ring

theorem ofBlocks_energy_sum (hsκ : Summable (fun s => κ s ^ 2)) :
    Summable (energyBound (ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag)) ∧
    (∑' i, energyBound (ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag) i) =
      20 * (2 * (∑' s, κ s ^ 2) + 1) := by
  let u : ℕ → ℝ := fun s => 20 * (2 * κ s ^ 2 + if s = tag then 1 else 0)
  have hu : ∀ s, 0 ≤ u s := by
    intro s
    dsimp [u]
    split_ifs <;> positivity
  have htag : Summable (fun s : ℕ => if s = tag then (1 : ℝ) else 0) :=
    (hasSum_ite_eq tag (1 : ℝ)).summable
  have hsu : Summable u := ((hsκ.mul_left 2).add htag).mul_left 20
  have hblock := enumerated_block_average m (fun s => by have := hm s; omega) u hu hsu e
  have henergy : energyBound (ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag) =
      fun i => u (e i).1 / (m (e i).1 : ℝ) := by
    funext i
    exact energyBound_ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag i
  rw [henergy]
  refine ⟨hblock.1, hblock.2.trans ?_⟩
  dsimp [u]
  rw [tsum_mul_left, (hsκ.mul_left 2).tsum_add htag, tsum_mul_left,
    tsum_ite_eq]

end BlockData

end Invariant233.OrderedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedShiftPowers
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.WeightedShift.diagonalAlgHom_apply _root_.OAI.Invariant233.WeightedShift.diagonal_add _root_.OAI.Invariant233.WeightedShift.diagonal_mul _root_.OAI.Invariant233.WeightedShift.diagonal_one _root_.OAI.Invariant233.WeightedShift.diagonal_smul _root_.OAI.Invariant233.WeightedShift.diagonal_star _root_.OAI.Invariant233.WeightedShift.diagonal_zero _root_.OAI.Invariant233.WeightedShift.shift_zero _root_.OAI.Invariant233.WeightedShift.translate_add _root_.OAI.Invariant233.WeightedShift.translate_apply _root_.OAI.Invariant233.WeightedShift.translate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal BigOperators
namespace Invariant233.WeightedShift

theorem operator_pow_apply_add (w : Weight) (n : ℕ) (ξ : Hilbert) (k : ℤ) :
    (((operator w)^n) ξ) (k + n) =
      (∏ j ∈ Finset.range n, w (k + j)) * ξ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, operator_apply]
    have hk : k + (↑(n + 1) : ℤ) - 1 = k + n := by omega
    rw [hk, ih, Finset.prod_range_succ]
    ring

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal lp Topology

namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

variable (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
  (ha : ∀ x, ‖a x‖ ≤ C)
  (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ)

variable {a C hC ha hm}

theorem fieldShift_ae (m : ℤ) (f : Lp Hilbert 2 μ) :
    (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f =ᵐ[μ]
      fun x => shift m (f x) :=
  ContinuousLinearMap.coeFn_compLp _ f

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_DiagonalContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.sequenceHilbertIntBorelSpace _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ENNReal lp

namespace Invariant233.SequenceHilbert

variable {I X : Type*}

theorem diagonal_congr (a b : I → ℂ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ i, ‖a i‖ ≤ C) (hb : ∀ i, ‖b i‖ ≤ D)
    (hab : ∀ i, a i = b i) : diagonal a C hC ha = diagonal b D hD hb := by
  ext v i
  simp only [diagonal_apply, hab]

end Invariant233.SequenceHilbert

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_UnrestrictedDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.sequenceHilbertIntBorelSpace _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.SequenceHilbert

variable {I : Type*}

theorem boundedDiagonal_eq (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) : boundedDiagonal a = diagonal a C hC ha := by
  unfold boundedDiagonal
  split
  · rename_i h
    exact diagonal_congr a a h.choose C h.choose_spec.1 hC h.choose_spec.2 ha (fun _ => rfl)
  · rename_i h
    exact False.elim (h ⟨C, hC, ha⟩)

@[simp]
theorem boundedDiagonal_apply_of_bound (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) (v : SequenceHilbert I) (i : I) :
    boundedDiagonal a v i = a i * v i := by
  rw [boundedDiagonal_eq a C hC ha, diagonal_apply]

end Invariant233.SequenceHilbert

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductWeightBridge
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function
open scoped ENNReal

namespace Invariant233.ProductModel

theorem cost_summand_nonneg (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base) (i : ℕ) :
    0 ≤ c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ) := by
  apply mul_nonneg (hc i)
  have hf : (0 : ℤ) ≤ ⌊circleRepresentative (x i) + θ i⌋ := by
    apply Int.floor_nonneg.mpr
    exact add_nonneg (ProductCocycle.representative_mem_Ico (x i)).1 (hθ i)
  exact_mod_cast hf

theorem logarithmicCost_eq_ofReal_tsum (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base)
    (hx : HasFiniteSupport (fun i ↦ ⌊circleRepresentative (x i) + θ i⌋)) :
    logarithmicCost θ c x =
      ENNReal.ofReal (∑' i, c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ)) := by
  exact (ENNReal.ofReal_tsum_of_nonneg
    (cost_summand_nonneg θ c hθ hc x)
    (FiniteSupportCocycle.summable_weighted_int c hx)).symm

theorem weight_eq_cocycleVersion_of_finite_support (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base)
    (hx : HasFiniteSupport (fun i ↦ ⌊circleRepresentative (x i) + θ i⌋)) :
    weight θ c x = ProductCocycle.cocycleVersion θ c 1 x := by
  have hnonneg : 0 ≤ ∑' i, c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ) :=
    tsum_nonneg (cost_summand_nonneg θ c hθ hc x)
  unfold weight
  rw [logarithmicCost_eq_ofReal_tsum θ c hθ hc x hx,
    EReal.coe_ennreal_ofReal, max_eq_left hnonneg, ← EReal.coe_neg,
    EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp only [ProductCocycle.cocycleVersion, Int.cast_one, one_mul,
    circleRepresentative, ProductCocycle.representative]

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldWeightedShiftPowers
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
  (ha : ∀ x, ‖a x‖ ≤ C)
  (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ)

theorem fieldOperator_ae (f : Lp Hilbert 2 μ) :
    fieldOperator a C hC ha hm f =ᵐ[μ] fun x => operator (a x) (f x) := by
  filter_upwards [fieldShift_ae 1 (fieldDiagonal a C hC ha hm f),
    fieldDiagonal_ae a C hC ha hm f] with x hs hd
  change ((shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
    (fieldDiagonal a C hC ha hm f)) x = operator (a x) (f x)
  rw [hs, hd]
  rfl

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductQuasinilpotent
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal BigOperators Topology

namespace Invariant233.ProductModel

theorem weight_orbit_product_eq_cocycleVersion
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (s : Set Base) (hinv : ∀ k : ℤ, ProductCocycle.rotate θ k ⁻¹' s = s)
    (hs : ∀ x ∈ s, ∀ k : ℤ, HasFiniteSupport
      (fun i ↦ ⌊ProductCocycle.representative (x i) + (k : ℝ) * θ i⌋))
    (hlaw : ∀ x ∈ s, ∀ k n : ℤ,
      ProductCocycle.cocycleVersion θ c (k + n) x =
        ProductCocycle.cocycleVersion θ c n (ProductCocycle.rotate θ k x) *
          ProductCocycle.cocycleVersion θ c k x)
    (x : Base) (hx : x ∈ s) (n : ℕ) :
    (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ j x)) =
      ProductCocycle.cocycleVersion θ c n x := by
  have hweight (k : ℤ) : weight θ c (rotationIterate θ k x) =
      ProductCocycle.cocycleVersion θ c 1 (ProductCocycle.rotate θ k x) := by
    apply weight_eq_cocycleVersion_of_finite_support θ c hθ0 hc
    have hxk : ProductCocycle.rotate θ k x ∈ s := by
      change x ∈ ProductCocycle.rotate θ k ⁻¹' s
      rw [hinv k]
      exact hx
    simpa only [ProductCocycle.representative, circleRepresentative,
      Int.cast_one, one_mul, rotationIterate, ProductCocycle.rotate] using hs _ hxk 1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, hweight]
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using (hlaw x hx n 1).symm

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductPowerIdentity
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal BigOperators Topology

namespace Invariant233.ProductModel

theorem ae_weight_orbit_product_eq_cocycleVersion
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) (n : ℕ) :
    ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ (k + j) x)) =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k x) := by
  obtain ⟨s, _hsm, hfull, hinv, hs, hlaw⟩ :=
    ProductCocycle.exists_invariant_cocycle_core θ hθ0 hθ
  filter_upwards [hfull] with x hx k
  have hxk : ProductCocycle.rotate θ k x ∈ s := by
    change x ∈ ProductCocycle.rotate θ k ⁻¹' s
    rw [hinv k]
    exact hx
  have hprod := weight_orbit_product_eq_cocycleVersion θ c hθ0 hc s hinv hs
    (fun y hy => hlaw y hy c) (ProductCocycle.rotate θ k x) hxk n
  have hrot (j : ℕ) : rotationIterate θ (k + j) x =
      rotationIterate θ j (ProductCocycle.rotate θ k x) :=
    ProductCocycle.rotate_add θ k j x
  simp_rw [hrot]
  exact hprod

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedOrbitInvariance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.OrbitInvariance
open WeightedShift

theorem endpoint_orthogonality (D : Hilbert →L[ℂ] Hilbert)
    {p q : Hilbert →L[ℂ] Hilbert} (hq : IsSelfAdjoint q)
    (h : (1 - q) * D * p = 0) (ξ η : Hilbert) :
    inner ℂ (D (p ξ)) ((1 - q) η) = 0 := by
  have hq' : ((1 - q : Hilbert →L[ℂ] Hilbert) : Hilbert →ₗ[ℂ] Hilbert).IsSymmetric :=
    LinearMap.IsSymmetric.id.sub hq.isSymmetric
  have hv : (1 - q) (D (p ξ)) = 0 :=
    congrArg (fun A : Hilbert →L[ℂ] Hilbert => A ξ) h
  calc
    inner ℂ (D (p ξ)) ((1 - q) η) =
        inner ℂ ((1 - q) (D (p ξ))) η :=
      (hq' _ _).symm
    _ = 0 := by rw [hv, inner_zero_left]

theorem weighted_shift_convolution_hasSum (w r : Weight)
    {p q : Hilbert →L[ℂ] Hilbert} (hq : IsStarProjection q)
    (hT : (1 - q) * operator w * q = 0)
    (hpair : (1 - q) * diagonal r * p = 0)
    (n : ℕ) (ξ η : Hilbert) :
    HasSum (fun v : ℤ =>
      (orbitProduct w n v * r v * p ξ v) * star ((1 - q) η (v + n))) 0 := by
  have hpow : (1 - q) * ((operator w)^n * diagonal r) * p = 0 := by
    simpa only [mul_assoc] using endpoint_inclusion_pow hq.isIdempotentElem hT hpair n
  have horth : inner ℂ ((1 - q) η) (((operator w)^n) (diagonal r (p ξ))) = 0 :=
    inner_eq_zero_symm.mp (endpoint_orthogonality ((operator w)^n * diagonal r)
      hq.isSelfAdjoint hpow ξ η)
  have hs := lp.hasSum_inner (𝕜 := ℂ) ((1 - q) η)
    (((operator w)^n) (diagonal r (p ξ)))
  rw [horth] at hs
  have hs' := (Equiv.addRight (n : ℤ)).hasSum_iff.mpr hs
  change HasSum (fun v : ℤ => inner ℂ (((1 - q) η) (v + n))
    ((((operator w)^n) (diagonal r (p ξ))) (v + n))) 0 at hs'
  simpa only [RCLike.inner_apply,
    starRingEnd_apply, operator_pow_apply_add, diagonal_apply,
    orbitProduct_apply, mul_assoc] using hs'

theorem cocycle_coefficients_hasSum (w r : Weight) (Fx Fy : ℤ → ℝ)
    {p q : Hilbert →L[ℂ] Hilbert} (hq : IsStarProjection q)
    (hT : (1 - q) * operator w * q = 0)
    (hpair : (1 - q) * diagonal r * p = 0)
    (n : ℕ) (ξ η : Hilbert)
    (hratio : ∀ v : ℤ, orbitProduct w n v * r v =
      (Fy (v + n) : ℂ) / (Fx v : ℂ)) :
    let A : ℤ → ℂ := fun v => p ξ v / (Fx v : ℂ)
    let B : ℤ → ℂ := fun v => (Fy (-v) : ℂ) * star ((1 - q) η (-v))
    HasSum (fun v : ℤ => A v * B (-(n : ℤ) - v)) 0 := by
  dsimp only
  apply (weighted_shift_convolution_hasSum w r hq hT hpair n ξ η).congr_fun
  intro v
  have hindex : -(-(n : ℤ) - v) = v + n := by omega
  rw [hindex, hratio v]
  simp only [div_eq_mul_inv]
  ring

theorem cocycle_coefficients_absolute_and_zero (w r : Weight) (Fx Fy : ℤ → ℝ)
    {p q : Hilbert →L[ℂ] Hilbert} (hq : IsStarProjection q)
    (hT : (1 - q) * operator w * q = 0)
    (hpair : (1 - q) * diagonal r * p = 0)
    (n : ℕ) (ξ η : Hilbert)
    (hratio : ∀ v : ℤ, orbitProduct w n v * r v =
      (Fy (v + n) : ℂ) / (Fx v : ℂ)) :
    let A : ℤ → ℂ := fun v => p ξ v / (Fx v : ℂ)
    let B : ℤ → ℂ := fun v => (Fy (-v) : ℂ) * star ((1 - q) η (-v))
    (Summable (fun v : ℤ => ‖A v * B (-(n : ℤ) - v)‖)) ∧
      (∑' v : ℤ, A v * B (-(n : ℤ) - v)) = 0 := by
  have hs := cocycle_coefficients_hasSum w r Fx Fy hq hT hpair n ξ η hratio
  exact ⟨hs.summable.norm, hs.tsum_eq⟩

end Invariant233.OrbitInvariance

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductOrbitPair
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel

theorem weightedOperator_ae_actualWeightField (θ c : ℕ → ℝ) (f : Hilbert) :
    weightedOperator θ c f =ᵐ[baseMeasure] fun x =>
      WeightedShift.operator (actualWeightField θ c x) (f x) := by
  have ha (x : Base) : ‖actualWeightField θ c x‖ ≤ 1 :=
    lp.norm_le_of_forall_le (by norm_num) (fun k => by
      simpa only [actualWeightField_apply, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (weight_mem_Icc θ c _).1] using (weight_mem_Icc θ c _).2)
  have hm (k : ℤ) : AEStronglyMeasurable
      (fun x => actualWeightField θ c x k) baseMeasure :=
    ((measurable_weight θ c).complex_ofReal.comp
      (rotationIterate_measurePreserving θ k).measurable).aestronglyMeasurable
  exact WeightedShift.fieldOperator_ae (actualWeightField θ c) 1 (by norm_num) ha hm f

theorem ae_actualWeightField_invariant (θ c : ℕ → ℝ)
    (p : Hilbert →L[ℂ] Hilbert) (F : Base → Fiber →L[ℂ] Fiber)
    (hrep : ∀ f : Hilbert, p f =ᵐ[baseMeasure] fun x => F x (f x))
    (hinv : (1 - p) * weightedOperator θ c * p = 0) :
    ∀ᵐ x ∂baseMeasure,
      (1 - F x) * WeightedShift.operator (actualWeightField θ c x) * F x = 0 :=
  L2Multiplication.ae_invariance_of_represented
    (default : HilbertBasis ℤ ℂ Fiber) p (weightedOperator θ c) F
    (fun x => WeightedShift.operator (actualWeightField θ c x))
    hrep (weightedOperator_ae_actualWeightField θ c) hinv

theorem boundedDiagonal_weight (w : WeightedShift.Weight) :
    SequenceHilbert.boundedDiagonal (fun k : ℤ => w k) = WeightedShift.diagonal w := by
  ext v k
  rw [SequenceHilbert.boundedDiagonal_apply_of_bound _ ‖w‖ (norm_nonneg w)
    (fun i => lp.norm_apply_le_norm (by simp) w i)]
  rfl

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductConvolutionIdentity
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators ComplexConjugate

namespace Invariant233.ProductModel

theorem ae_antitone_cocycleVersion (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    ∀ᵐ x ∂baseMeasure, Antitone (fun k : ℤ => ProductCocycle.cocycleVersion θ c k x) := by
  obtain ⟨s, _hsm, hfull, _hinv, _hs, hlaw⟩ :=
    ProductCocycle.exists_invariant_cocycle_core θ hθ0 hθ
  filter_upwards [hfull] with x hx
  intro a b hab
  have heq := hlaw x hx c a (b - a)
  rw [add_sub_cancel] at heq
  calc
    ProductCocycle.cocycleVersion θ c b x =
        ProductCocycle.cocycleVersion θ c (b - a) (rotationIterate θ a x) *
          ProductCocycle.cocycleVersion θ c a x := heq
    _ ≤ 1 * ProductCocycle.cocycleVersion θ c a x :=
      mul_le_mul_of_nonneg_right
        (ProductCocycle.cocycleVersion_le_one_of_nonneg_time θ c hθ0 hc (b - a)
          (sub_nonneg.mpr hab) _) (ProductCocycle.cocycleVersion_pos θ c a x).le
    _ = _ := one_mul _

theorem ae_convolution_two_ratio_bounds (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (F : Base → Fiber →L[ℂ] Fiber) (ν : Measure EndpointPair)
    (hfst : ν.map Prod.fst ≪ baseMeasure) (hsnd : ν.map Prod.snd ≪ baseMeasure)
    (hpair : ∀ᵐ xy ∂ν, PairIdentity θ c F xy) :
    ∀ᵐ xy ∂ν, ∀ (n : ℕ) (v : ℤ),
      0 < ProductCocycle.cocycleVersion θ c ((n : ℤ) + v) xy.2 /
        ProductCocycle.cocycleVersion θ c v xy.1 ∧
      ProductCocycle.cocycleVersion θ c ((n : ℤ) + v) xy.2 /
          ProductCocycle.cocycleVersion θ c v xy.1 ≤
        min (cocycleRatio θ c xy.1 xy.2 v)
          (cocycleRatio θ c xy.1 xy.2 ((n : ℤ) + v)) ∧
      min (cocycleRatio θ c xy.1 xy.2 v)
        (cocycleRatio θ c xy.1 xy.2 ((n : ℤ) + v)) ≤ 1 := by
  have hmono := ae_antitone_cocycleVersion θ c hθ0 hc hθ
  have hx := ae_of_ae_map measurable_fst.aemeasurable (hfst.ae_le hmono)
  have hy := ae_of_ae_map measurable_snd.aemeasurable (hsnd.ae_le hmono)
  filter_upwards [hx, hy, hpair] with xy hx hy hp n v
  exact InvariantProjection.cocycle_two_ratio_bounds
    (fun k => ProductCocycle.cocycleVersion θ c k xy.1)
    (fun k => ProductCocycle.cocycleVersion θ c k xy.2)
    (fun k => ProductCocycle.cocycleVersion_pos θ c k xy.1)
    (fun k => ProductCocycle.cocycleVersion_pos θ c k xy.2)
    hx hy (fun k => (hp.1 k).2) n v

theorem coefficients_absolute_and_zero_of_pair (θ c : ℕ → ℝ)
    (F : Base → Fiber →L[ℂ] Fiber) (x y : Base)
    (hproj : IsStarProjection (F y))
    (hinv : (1 - F y) * WeightedShift.operator (actualWeightField θ c y) * F y = 0)
    (hpair : PairIdentity θ c F (x, y)) (n : ℕ)
    (hprod : ∀ k : ℤ,
      (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ (k + j) y)) =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k y))
    (hlaw : ∀ k : ℤ,
      ProductCocycle.cocycleVersion θ c (k + n) y =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k y) *
          ProductCocycle.cocycleVersion θ c k y)
    (ξ η : Fiber) :
    let A : ℤ → ℂ := fun v => F x ξ v / (ProductCocycle.cocycleVersion θ c v x : ℂ)
    let B : ℤ → ℂ := fun v => (ProductCocycle.cocycleVersion θ c (-v) y : ℂ) *
      star (((1 - F y) η) (-v))
    (Summable (fun v : ℤ => ‖A v * B (-(n : ℤ) - v)‖)) ∧
      (∑' v : ℤ, A v * B (-(n : ℤ) - v)) = 0 := by
  let r : WeightedShift.Weight := ⟨fun k => (cocycleRatio θ c x y k : ℂ),
    memℓp_infty ⟨1, by
      rintro z ⟨k, rfl⟩
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpair.1 k).1]
        using (hpair.1 k).2⟩⟩
  have hr : WeightedShift.diagonal r = ratioDiagonal θ c x y :=
    (boundedDiagonal_weight r).symm
  have hp : (1 - F y) * WeightedShift.diagonal r * F x = 0 := by
    rw [hr]
    exact hpair.2
  apply OrbitInvariance.cocycle_coefficients_absolute_and_zero
    (actualWeightField θ c y) r
    (fun k => ProductCocycle.cocycleVersion θ c k x)
    (fun k => ProductCocycle.cocycleVersion θ c k y)
    hproj hinv hp n ξ η
  intro v
  change (∏ j ∈ Finset.range n, (weight θ c (rotationIterate θ (v + j) y) : ℂ)) *
    ((ProductCocycle.cocycleVersion θ c v y /
      ProductCocycle.cocycleVersion θ c v x : ℝ) : ℂ) = _
  rw [← Complex.ofReal_prod, hprod v, Complex.ofReal_div, ← mul_div_assoc,
    ← Complex.ofReal_mul, ← hlaw v]

theorem ae_coefficients_absolute_and_zero (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (p : Hilbert →L[ℂ] Hilbert) (F : Base → Fiber →L[ℂ] Fiber)
    (hproj : ∀ x, IsStarProjection (F x))
    (hrep : ∀ f : Hilbert, p f =ᵐ[baseMeasure] fun x => F x (f x))
    (hinv : (1 - p) * weightedOperator θ c * p = 0)
    (ν : Measure EndpointPair) (hsnd : ν.map Prod.snd ≪ baseMeasure)
    (hpair : ∀ᵐ xy ∂ν, PairIdentity θ c F xy) (ξ η : Fiber) :
    ∀ᵐ xy ∂ν, ∀ n : ℕ,
      let A : ℤ → ℂ := fun v => F xy.1 ξ v /
        (ProductCocycle.cocycleVersion θ c v xy.1 : ℂ)
      let B : ℤ → ℂ := fun v => (ProductCocycle.cocycleVersion θ c (-v) xy.2 : ℂ) *
        star (((1 - F xy.2) η) (-v))
      (Summable (fun v : ℤ => ‖A v * B (-(n : ℤ) - v)‖)) ∧
        (∑' v : ℤ, A v * B (-(n : ℤ) - v)) = 0 := by
  have hInv := ae_of_ae_map measurable_snd.aemeasurable
    (hsnd.ae_le (ae_actualWeightField_invariant θ c p F hrep hinv))
  obtain ⟨s, _hsm, hfull, _hinv, _hs, hlaw⟩ :=
    ProductCocycle.exists_invariant_cocycle_core θ hθ0 hθ
  have hcore := ae_of_ae_map measurable_snd.aemeasurable (hsnd.ae_le hfull)
  apply ae_all_iff.mpr
  intro n
  have hProd := ae_of_ae_map measurable_snd.aemeasurable
    (hsnd.ae_le (ae_weight_orbit_product_eq_cocycleVersion θ c hθ0 hc hθ n))
  filter_upwards [hInv, hcore, hProd, hpair] with xy hi hs hp hxy
  exact coefficients_absolute_and_zero_of_pair θ c F xy.1 xy.2 (hproj xy.2)
    hi hxy n hp (fun k => hlaw xy.2 hs c k n) ξ η

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductCouplingCircle
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Invariant233.OrderedProductCoupling

open OneCoordinateCoupling

lemma baseLaw_eq_restrict : baseLaw = volume.restrict (Ico (0 : ℝ) 1) := by
  simp [baseLaw, CouplingMixture.intervalLaw, ProbabilityTheory.cond, Real.volume_Ico]

lemma realEndpoint_measurable : Measurable realEndpoint := by
  apply Measurable.of_eval
  intro i
  exact (CocycleSupport.measurePreserving_circleRepresentative.measurable).comp
    (measurable_pi_apply i)

lemma measurePreserving_circleQuotient :
    MeasurePreserving (fun x : ℝ => (x : Circle)) baseLaw circleMeasure := by
  rw [baseLaw_eq_restrict]
  change MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
    (volume.restrict (Ico 0 1)) volume
  rw [restrict_Ico_eq_restrict_Ioc]
  simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0

lemma measurePreserving_circleEndpoint :
    MeasurePreserving circleEndpoint baseMeasure ProductModel.baseMeasure := by
  refine ⟨circleEndpoint_measurable, ?_⟩
  change (Measure.infinitePi (fun _ : ℕ => baseLaw)).map
    (fun x i => (x i : Circle)) = Measure.infinitePi (fun _ : ℕ => circleMeasure)
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => baseLaw)
    (fun _ => measurePreserving_circleQuotient.measurable)]
  simp_rw [measurePreserving_circleQuotient.map_eq]

lemma measurePreserving_realEndpoint :
    MeasurePreserving realEndpoint ProductModel.baseMeasure baseMeasure := by
  refine ⟨realEndpoint_measurable, ?_⟩
  change (Measure.infinitePi (fun _ : ℕ => circleMeasure)).map
    (fun x i => circleRepresentative (x i)) = Measure.infinitePi (fun _ : ℕ => baseLaw)
  unfold circleRepresentative
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => circleMeasure)
    (fun _ => CocycleSupport.measurePreserving_circleRepresentative.measurable)]
  congr 1
  funext i
  exact CocycleSupport.measurePreserving_circleRepresentative.map_eq.trans
    baseLaw_eq_restrict.symm

lemma realEndpoint_circleEndpoint_of_mem {x : Endpoint}
    (hx : ∀ i, x i ∈ Ico (0 : ℝ) 1) : realEndpoint (circleEndpoint x) = x := by
  funext i
  exact AddCircle.equivIco_coe_of_mem (by simpa using hx i)

lemma ae_realEndpoint_circleEndpoint :
    ∀ᵐ x ∂baseMeasure, realEndpoint (circleEndpoint x) = x := by
  have h : ∀ᵐ x ∂baseMeasure, ∀ i, x i ∈ Ico (0 : ℝ) 1 := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => baseLaw) i).quasiMeasurePreserving.ae
      (CouplingMixture.intervalLaw_ae_mem 0 1)
  exact h.mono (fun _ hx => realEndpoint_circleEndpoint_of_mem hx)

theorem circle_density_transport {g : Endpoint → ℝ} (hg : MemLp g 2 baseMeasure) :
    (baseMeasure.withDensity (fun x => ENNReal.ofReal (g x))).map circleEndpoint =
      ProductModel.baseMeasure.withDensity
        (fun x => ENNReal.ofReal (g (realEndpoint x))) ∧
      eLpNorm (g ∘ realEndpoint) 2 ProductModel.baseMeasure = eLpNorm g 2 baseMeasure :=
  DensityTransport.real_density_transport_ae circleEndpoint_measurable realEndpoint_measurable
    measurePreserving_circleEndpoint.map_eq ae_realEndpoint_circleEndpoint hg.aemeasurable

theorem exists_circle_hybrid_density (P : Parameters) (ε : ℕ → Bool) {C : ℝ}
    (hsum : Summable (energyBound P)) (hC : (∑' i, energyBound P i) ≤ C) :
    ∃ G : ProductModel.Base → ℝ,
      MemLp G 2 ProductModel.baseMeasure ∧ (0 ≤ᵐ[ProductModel.baseMeasure] G) ∧
      (∫ x, G x ∂ProductModel.baseMeasure) = 1 ∧
      eLpNorm G 2 ProductModel.baseMeasure ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (law P).map (circleHybridEndpoint ε) =
        ProductModel.baseMeasure.withDensity (fun x => ENNReal.ofReal (G x)) := by
  obtain ⟨g, hg, hn, hm, hnorm, hlaw⟩ := exists_hybrid_density P ε hsum hC
  have ht := circle_density_transport hg
  refine ⟨g ∘ realEndpoint, hg.comp_measurePreserving measurePreserving_realEndpoint,
    measurePreserving_realEndpoint.quasiMeasurePreserving.ae hn, ?_, ht.2.trans_le hnorm, ?_⟩
  · have hi := integral_map realEndpoint_measurable.aemeasurable
      (show AEStronglyMeasurable g (ProductModel.baseMeasure.map realEndpoint) by
        rw [measurePreserving_realEndpoint.map_eq]
        exact hg.aestronglyMeasurable)
    rw [measurePreserving_realEndpoint.map_eq] at hi
    exact hi.symm.trans hm
  · change (law P).map (circleEndpoint ∘ hybridEndpoint ε) = _
    rw [← Measure.map_map circleEndpoint_measurable (hybridEndpoint_measurable ε), hlaw]
    exact ht.1

end Invariant233.OrderedProductCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductCouplingCircleSource
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace Invariant233.OrderedProductCoupling

theorem exists_source_circle_hybrid_density
    (m : ℕ → ℕ) (a b : ℕ → ℝ) (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (tag : ℕ) (ε : ℕ → Bool) :
    ∃ H : ProductModel.Base → ℝ, MemLp H 2 ProductModel.baseMeasure ∧
      (0 ≤ᵐ[ProductModel.baseMeasure] H) ∧
      (∫ x, H x ∂ProductModel.baseMeasure) = 1 ∧
      eLpNorm H 2 ProductModel.baseMeasure ≤ ENNReal.ofReal (blockDensityBound sourceKappa) ∧
      (law (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm
        ha ha' hb hb' e tag)).map (circleHybridEndpoint ε) =
        ProductModel.baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
  obtain ⟨hs, htotal⟩ := ofBlocks_energy_sum m sourceKappa a b
    sourceKappa_nonneg sourceKappa_le hm ha ha' hb hb' e tag summable_sourceKappa_sq
  have hbound : Real.exp ((20 * (2 * (∑' s, sourceKappa s ^ 2) + 1)) / 2) =
      blockDensityBound sourceKappa := by
    unfold blockDensityBound
    congr 1
    ring
  simpa only [hbound] using exists_circle_hybrid_density
    (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm
      ha ha' hb hb' e tag) ε hs htotal.le

end Invariant233.OrderedProductCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductConditionalData
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.flatten_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingCylinderWeak.quotient_cutCoordinates _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace Invariant233.ProductModel
open OrderedProductCoupling
open InvariantProjection.ConditionalConvolution

theorem conditionalData_of_sourceTail
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s)) (θ : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (P : Parameters) (j : ℕ)
    (A : Hilbert →L[ℂ] Hilbert) (F : Base → Fiber →L[ℂ] Fiber)
    (hF : IsCovariantFieldRepresentation θ A F 1)
    (hproj : ∀ x, IsStarProjection (F x))
    (hinv : (1 - A) * weightedOperator θ (fun i => p.C (e i).1) * A = 0)
    (hfst : (circlePairLaw P).map Prod.fst ≪ baseMeasure)
    (hsnd : (circlePairLaw P).map Prod.snd ≪ baseMeasure)
    (hpair : ∀ᵐ xy ∂circlePairLaw P, PairIdentity θ (fun i => p.C (e i).1) F xy)
    (htail : SourceTailEstimate p e θ j P)
    (E : Set Sample) (hE : MeasurableSet E) (c : ℝ) (hmass : c ≤ (law P).real E)
    (hcoeff : ∀ᵐ ω ∂(law P).restrict E,
      (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
        ‖coeffA (sourceLeftVector F) (sourceLeftCocycle θ (fun i => p.C (e i).1)) ω v‖ ≤ p.coefficientBound j) ∧
      (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
        ‖coeffB (sourceRightVector F) (sourceRightCocycle θ (fun i => p.C (e i).1)) ω v‖ ≤ p.coefficientBound j) ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤
        ‖coeffA (sourceLeftVector F) (sourceLeftCocycle θ (fun i => p.C (e i).1)) ω 0‖ ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤
        ‖coeffB (sourceRightVector F) (sourceRightCocycle θ (fun i => p.C (e i).1)) ω 0‖)
    (htag : ∀ᵐ ω ∂(law P).restrict E,
      ∃ i ∈ ProductPhases.consecutiveBlock p.m j,
        circleRepresentative (circleLeftEndpoint ω i) < 1 / (p.m j : ℝ) ∧
        1 - 1 / (p.m j : ℝ) ≤ circleRepresentative (circleRightEndpoint ω i)) :
    Nonempty (Data Sample (law P) (p.K j) (p.coefficientBound j)
      (1 / ((j + 1 : ℕ) : ℝ)) c (Real.exp (-p.L j)) (Real.exp (-p.L j / 400))) := by
  let costs : ℕ → ℝ := fun i => p.C (e i).1
  have hc : ∀ i, 0 ≤ costs i := fun i => (hp.C_pos (e i).1).le
  have hxy : Measurable (fun ω : Sample => (circleLeftEndpoint ω, circleRightEndpoint ω)) :=
    circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable
  have hz := ae_of_ae_map hxy.aemeasurable
    (ae_coefficients_absolute_and_zero θ costs hθ0 hc hθsum A F hproj hF.2.2.2.1
      hinv (circlePairLaw P) hsnd hpair sourceUnitVector sourceUnitVector)
  have hr := ae_of_ae_map hxy.aemeasurable
    (ae_convolution_two_ratio_bounds θ costs hθ0 hc hθsum F (circlePairLaw P) hfst hsnd hpair)
  obtain ⟨H₁, H₂, hm₁, hm₂, ht⟩ := htail
  have hv : ‖sourceUnitVector‖ = 1 := by simp [sourceUnitVector]
  refine ⟨{
    mX := MeasurableSpace.comap circleLeftEndpoint inferInstance
    mY := MeasurableSpace.comap circleRightEndpoint inferInstance
    mX_le := circleLeftEndpoint_measurable.comap_le
    mY_le := circleRightEndpoint_measurable.comap_le
    ξ := sourceLeftVector F
    γ := sourceRightVector F
    ξ_measurable := ?_
    γ_measurable := ?_
    ξ_unit := ?_
    γ_unit := ?_
    Fx := sourceLeftCocycle θ costs
    Fy := sourceRightCocycle θ costs
    Fx_measurable := fun k => (ProductCocycle.measurable_cocycleVersion θ costs k).comp circleLeftEndpoint_measurable
    Fy_measurable := fun k => (ProductCocycle.measurable_cocycleVersion θ costs k).comp circleRightEndpoint_measurable
    Fx_pos := Filter.Eventually.of_forall (fun ω k => ProductCocycle.cocycleVersion_pos θ costs k _)
    Fy_pos := Filter.Eventually.of_forall (fun ω k => ProductCocycle.cocycleVersion_pos θ costs k _)
    Fx_zero := Filter.Eventually.of_forall (fun ω => ProductCocycle.cocycleVersion_zero θ costs _)
    Fy_zero := Filter.Eventually.of_forall (fun ω => ProductCocycle.cocycleVersion_zero θ costs _)
    zero_convolution := ?_
    ratio_bounds := ?_
    E := E
    E_measurable := hE
    E_mass := hmass
    coefficient_bounds := hcoeff
    H₁ := H₁
    H₂ := H₂
    H₁_measurable := hm₁
    H₂_measurable := hm₂
    attenuation := ?_
    conditional₁ := ?_
    conditional₂ := ?_ }⟩
  · exact (hF.2.2.1 sourceUnitVector).comp_measurable (Measurable.of_comap_le le_rfl)
  · have hs : StronglyMeasurable (fun x : Base => (1 - F x) sourceUnitVector) := by
      convert ((stronglyMeasurable_const : StronglyMeasurable (fun _ : Base => sourceUnitVector)).sub (hF.2.2.1 sourceUnitVector)) using 1
      all_goals try with_reducible_and_instances rfl
      funext x
      simp only [sub_apply, one_apply_eq_self, Pi.sub_apply]
    exact hs.comp_measurable (Measurable.of_comap_le le_rfl)
  · exact Filter.Eventually.of_forall (fun ω => by
      have h := (F (circleLeftEndpoint ω)).le_of_opNorm_le
        (IsStarProjection.norm_le _ (hproj _)) sourceUnitVector
      simpa [sourceLeftVector, hv] using h)
  · exact Filter.Eventually.of_forall (fun ω => by
      have h := (1 - F (circleRightEndpoint ω)).le_of_opNorm_le
        (IsStarProjection.norm_le _ (hproj _).one_sub) sourceUnitVector
      simpa [sourceRightVector, hv] using h)
  · intro n _
    filter_upwards [hz] with ω hω
    exact (hω n).2
  · intro n _
    filter_upwards [hr] with ω hω v
    exact hω n v
  · filter_upwards [ae_restrict_of_ae ht, htag] with ω hω htagω k hk
    have hk' : (p.K j : ℝ) < |(k : ℝ)| := by exact_mod_cast hk
    exact (hω k hk').2.2 htagω
  · intro k hk
    filter_upwards [ht] with ω hω
    exact (hω k (by exact_mod_cast hk)).1
  · intro k hk
    filter_upwards [ht] with ω hω
    exact (hω k (by exact_mod_cast hk)).2.1

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductSourceConditionalData
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.leftTailLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.sourcePairLaw_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductModel
open OrderedProductCoupling
open InvariantProjection.ConditionalConvolution

theorem actualSourcePair_marginals_ac {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ) :
    (circlePairLaw (actualSourceParameters hp e j)).map Prod.fst ≪ baseMeasure ∧
    (circlePairLaw (actualSourceParameters hp e j)).map Prod.snd ≪ baseMeasure := by
  let P := actualSourceParameters hp e j
  have hac (side : Bool) : (law P).map (circleHybridEndpoint (fun _ => side)) ≪ baseMeasure := by
    obtain ⟨g, _, _, _, _, hg⟩ := exists_source_circle_hybrid_density p.m p.a p.b
      hp.m_ge_100 (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
      (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2) e j (fun _ => side)
    change (law P).map (circleHybridEndpoint (fun _ => side)) = _ at hg
    rw [hg]
    exact withDensity_absolutelyContinuous _ _
  have hm : Measurable (fun ω : Sample => (circleLeftEndpoint ω, circleRightEndpoint ω)) :=
    circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable
  constructor
  · change ((law P).map _).map Prod.fst ≪ baseMeasure
    rw [Measure.map_map measurable_fst hm]
    exact hac false
  · change ((law P).map _).map Prod.snd ≪ baseMeasure
    rw [Measure.map_map measurable_snd hm]
    exact hac true

theorem eventually_actualSource_conditionalData_oai
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (hphase : ∀ i, θ i ∈ Set.Icc (1 / p.N (e i).1) (2 / p.N (e i).1))
    (A : Hilbert →L[ℂ] Hilbert) (F : Base → Fiber →L[ℂ] Fiber)
    (hF : IsCovariantFieldRepresentation θ A F 1)
    (hproj : ∀ x, IsStarProjection (F x))
    (hinv : (1 - A) * weightedOperator θ (fun i => p.C (e i).1) * A = 0)
    (hdiag : ∀ᵐ x ∂baseMeasure,
      0 < BlockedProductCoupling.projectionDiagonal F x ∧
      BlockedProductCoupling.projectionDiagonal F x < 1)
    (hpair : ∀ j, ∀ᵐ xy ∂circlePairLaw (actualSourceParameters hp e j),
      PairIdentity θ (fun i => p.C (e i).1) F xy)
    (htail : ∀ᶠ j in atTop,
      SourceTailEstimate p e θ j (actualSourceParameters hp e j)) :
    ∀ᶠ j in atTop,
      Nonempty (Data Sample (law (actualSourceParameters hp e j))
        (p.K j) (p.coefficientBound j) (1 / ((j + 1 : ℕ) : ℝ))
        (Real.exp (-82) / 2) (Real.exp (-p.L j)) (Real.exp (-p.L j / 400))) := by
  have hr : Measurable (BlockedProductCoupling.projectionDiagonal F) := by
    exact Complex.measurable_re.comp
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).continuous.measurable.comp (hF.2.2.1 _).measurable)
  have hmass := BlockedProductCoupling.eventually_flatSourceEvent_mass hp e hr hdiag
  filter_upwards [hmass, htail] with j hj ht
  let E := BlockedProductCoupling.flatSourceEvent p e (BlockedProductCoupling.projectionDiagonal F) j
  have hE : MeasurableSet E := BlockedProductCoupling.measurable_flatSourceEvent p e hr j
  have hb := BlockedProductCoupling.ae_flatSourceEvent_coefficient_properties hp e θ hphase F
    (Filter.Eventually.of_forall hproj) j
  have htag := BlockedProductCoupling.ae_flatSourceEvent_tag_endpoints hp e he
    (BlockedProductCoupling.projectionDiagonal F) j
  have hmem : ∀ᵐ ω ∂(law (actualSourceParameters hp e j)).restrict E, ω ∈ E :=
    ae_restrict_mem hE
  apply conditionalData_of_sourceTail hp e θ hθ0 hθsum (actualSourceParameters hp e j) j A F hF hproj hinv
    (actualSourcePair_marginals_ac hp e j).1 (actualSourcePair_marginals_ac hp e j).2
    (hpair j) ht E hE (Real.exp (-82) / 2) hj
  · filter_upwards [ae_restrict_of_ae hb, hmem] with ω hω hωE
    simpa only [BlockedProductCoupling.sourceCoefficientA, BlockedProductCoupling.sourceCoefficientB,
      BlockedProductCoupling.circleLeftEndpoint_unflatten,
      BlockedProductCoupling.circleRightEndpoint_unflatten,
      coeffA, coeffB, sourceLeftVector, sourceRightVector, sourceLeftCocycle,
      sourceRightCocycle, sourceUnitVector, BlockedProductCoupling.sourceBasisZero] using hω hωE
  · filter_upwards [ae_restrict_of_ae htag, hmem] with ω hω hωE
    exact hω hωE

end Invariant233.ProductModel

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.ProductModel.eventually_actualSource_conditionalData_oai := @OAI.Invariant233.ProductModel.eventually_actualSource_conditionalData_oai
