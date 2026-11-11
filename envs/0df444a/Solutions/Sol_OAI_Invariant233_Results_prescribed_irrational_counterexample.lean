-- Prove2me | solution 1 for OAI.Invariant233.Results.prescribed_irrational_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:27:12.033044+00:00
-- url     : https://prove2.me/submissions/fa1bc35f-2929-429a-96ae-f1eb746967f2

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Logic.Function.Iterate
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalLExpectation
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Piecewise
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003
import Theorems.Thm_OAI_Invariant233_CircleParameterLaws_measurableOperator_hasOnlyTrivialInvariantProjections
import Theorems.Thm_OAI_Invariant233_Rotation_exponentialTransfer_projection_transport
import Theorems.Thm_OAI_Invariant233_exists_circle_parameters

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
/-- Mathlib d13f23b's `spectralRadius_eq_of_unital`: the spectral radius is the supremum of the norms over the spectrum. -/
theorem spectralRadius_eq_of_unital {𝕜 A : Type*} [NormedField 𝕜] [Ring A] [Algebra 𝕜 A] (a : A) :
    spectralRadius 𝕜 a = ⨆ k ∈ spectrum 𝕜 a, (‖k‖₊ : ENNReal) := rfl
end OAICompat434

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BackgroundBumps
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace Invariant233.BackgroundCost

theorem exists_disjoint_closedBalls {ι X : Type*} [Finite ι] [MetricSpace X]
    (f : ι → X) (hf : Function.Injective f) :
    ∃ r : ℝ, 0 < r ∧ Pairwise (fun i j =>
      Disjoint (Metric.closedBall (f i) r) (Metric.closedBall (f j) r)) := by
  have hmul : Tendsto (fun r : ℝ => 2 * r) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => 2 * r) := by fun_prop
    have h := hc.continuousAt (x := 0)
    change Tendsto (fun r : ℝ => 2 * r) (𝓝 0) (𝓝 (2 * 0)) at h
    simpa only [mul_zero] using h
  have he : ∀ᶠ r : ℝ in 𝓝 0, ∀ i j : ι, i ≠ j → 2 * r < dist (f i) (f j) := by
    apply eventually_all.2
    intro i
    apply eventually_all.2
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    · have hd : 0 < dist (f i) (f j) := dist_pos.mpr (hf.ne hij)
      exact (hmul.eventually (eventually_lt_nhds hd)).mono fun _ h _ => h
  have hrpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  have he' : ∀ᶠ r : ℝ in 𝓝[>] 0,
      0 < r ∧ ∀ i j : ι, i ≠ j → 2 * r < dist (f i) (f j) :=
    hrpos.and (he.filter_mono nhdsWithin_le_nhds)
  obtain ⟨r, hr, hsep⟩ := he'.exists
  refine ⟨r, hr, ?_⟩
  intro i j hij
  apply Set.disjoint_left.2
  intro x hxi hxj
  have hi : dist (f i) x ≤ r := by
    simpa only [Metric.mem_closedBall, dist_comm] using hxi
  have hj : dist x (f j) ≤ r := hxj
  have ht := dist_triangle (f i) x (f j)
  have hs := hsep i j hij
  linarith

theorem exists_small_closedBall {X : Type*} [MetricSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.OuterRegular]
    [NullSingletonClass μ] (a : X) {R : ℝ} (hR : 0 < R)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ μ (Metric.closedBall a r) < ε := by
  obtain ⟨U, haU, hU, hμU⟩ :=
    Set.exists_isOpen_lt_of_lt (μ := μ) ({a} : Set X) ε (by simpa using hε)
  have ha : a ∈ U := haU (by simp)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds ha)
  refine ⟨min (δ / 2) (R / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩
  · exact (min_le_right _ _).trans_lt (by linarith)
  · apply lt_of_le_of_lt (measure_mono ?_) hμU
    intro x hx
    apply hδU
    have hd : dist x a ≤ δ / 2 := hx.trans (min_le_left _ _)
    show dist x a < δ
    linarith

theorem exists_tent_bump {X : Type*} [MetricSpace X] (a : X)
    {r : ℝ} (hr : 0 < r) :
    ∃ v : X → ℝ, Continuous v ∧ v a = 1 ∧
      (∀ x, 0 ≤ v x ∧ v x ≤ 1) ∧
      Function.support v ⊆ Metric.closedBall a r := by
  refine ⟨fun x => max (1 - dist x a / r) 0, ?_, ?_, ?_, ?_⟩
  · fun_prop
  · simp
  · intro x
    constructor
    · exact le_max_right _ _
    · apply max_le
      · have hd : 0 ≤ dist x a / r := div_nonneg dist_nonneg hr.le
        linarith
      · norm_num
  · intro x hx
    have hh : 0 < max (1 - dist x a / r) 0 :=
      lt_of_le_of_ne (le_max_right _ _) (Ne.symm hx)
    have hpos : 0 < 1 - dist x a / r := (lt_max_iff.mp hh).resolve_right (lt_irrefl _)
    have hd : dist x a < r := (div_lt_one hr).1 (by linarith)
    exact hd.le

theorem exists_bump_disjoint_images {ι X : Type*} [Finite ι] [MetricSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.OuterRegular]
    [NullSingletonClass μ] (a : X) (T : ι → X → X)
    (hT : ∀ i, Isometry (T i)) (ha : Function.Injective (fun i => T i a))
    {R : ℝ} (hR : 0 < R) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (r : ℝ) (v : X → ℝ), 0 < r ∧ r < R ∧
      μ (Metric.closedBall a r) < ε ∧ Continuous v ∧ v a = 1 ∧
      (∀ x, 0 ≤ v x ∧ v x ≤ 1) ∧
      Function.support v ⊆ Metric.closedBall a r ∧
      Pairwise (fun i j => Disjoint (T i '' Metric.closedBall a r)
        (T j '' Metric.closedBall a r)) := by
  obtain ⟨R₀, hR₀, hsep⟩ := exists_disjoint_closedBalls (fun i => T i a) ha
  obtain ⟨r, hr, hrR, hμr⟩ :=
    exists_small_closedBall μ a (lt_min hR hR₀) hε
  obtain ⟨v, hv, hva, hv01, hsupp⟩ := exists_tent_bump a hr
  refine ⟨r, v, hr, hrR.trans_le (min_le_left _ _), hμr,
    hv, hva, hv01, hsupp, ?_⟩
  have himage : ∀ i, T i '' Metric.closedBall a r ⊆ Metric.closedBall (T i a) R₀ := by
    intro i y hy
    obtain ⟨x, hx, rfl⟩ := hy
    show dist (T i x) (T i a) ≤ R₀
    rw [(hT i).dist_eq]
    exact hx.trans (hrR.le.trans (min_le_right _ _))
  intro i j hij
  exact (hsep hij).mono (himage i) (himage j)

end Invariant233.BackgroundCost

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ContinuityCoboundary
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.Continuity

variable {X : Type*}

theorem backwardSum_succ (σ : X ≃ X) (v : X → ℝ) (n : ℕ) (x : X) :
    backwardSum σ v (n + 1) x =
      backwardSum σ v n x + v ((σ.symm : X → X)^[n + 1] x) := by
  simp [backwardSum, Finset.sum_range_succ]

theorem backwardSum_sub_comp (σ : X ≃ X) (v : X → ℝ) (n : ℕ) (x : X) :
    backwardSum σ v n x - backwardSum σ v n (σ x) =
      v ((σ.symm : X → X)^[n] x) - v x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [backwardSum_succ, backwardSum_succ]
    have hcancel : (σ.symm : X → X)^[n + 1] (σ x) =
        (σ.symm : X → X)^[n] x := by
      rw [Function.iterate_succ_apply]
      simp
    rw [hcancel]
    linarith

theorem relocated_eq_add_coboundary (σ : X ≃ X) (h : X → ℝ)
    (φ : ℕ → X → ℝ) (H : ℕ) (x : X)
    (hpartition : ∑ n ∈ Finset.range (H + 1), φ n x = 1) :
    relocated σ h φ H x = h x + relocationTransfer σ h φ H x -
      relocationTransfer σ h φ H (σ x) := by
  have ht : relocationTransfer σ h φ H x -
      relocationTransfer σ h φ H (σ x) = relocated σ h φ H x - h x := by
    unfold relocationTransfer
    rw [← Finset.sum_sub_distrib]
    simp_rw [backwardSum_sub_comp]
    rw [Finset.sum_sub_distrib]
    change relocated σ h φ H x -
      (∑ n ∈ Finset.range (H + 1), h x * φ n x) = _
    rw [← Finset.mul_sum, hpartition, mul_one]
  linarith

theorem relocationTransfer_eq_zero (σ : X ≃ X) (h : X → ℝ)
    (φ : ℕ → X → ℝ) (H : ℕ) (x : X)
    (hzero : ∀ r, 1 ≤ r → r ≤ H → h ((σ.symm : X → X)^[r] x) = 0) :
    relocationTransfer σ h φ H x = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro r hr
  have hn' : n ≤ H := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have hr' : r + 1 ≤ n := Finset.mem_range.mp hr
  change h ((σ.symm : X → X)^[r + 1] x) *
    φ n ((σ.symm : X → X)^[r + 1] x) = 0
  rw [hzero (r + 1) (by omega) (by omega), zero_mul]

theorem background_coboundary (σ : X ≃ X) (v : X → ℝ)
    (W : ℕ) (hW : W ≠ 0) (x : X) :
    v x - backwardAverage σ v W x =
      backgroundTransfer σ v W (σ x) - backgroundTransfer σ v W x := by
  have ht : (∑ n ∈ Finset.range W, backwardSum σ v (n + 1) x) -
      (∑ n ∈ Finset.range W, backwardSum σ v (n + 1) (σ x)) =
      backwardSum σ v W x - (W : ℝ) * v x := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [backwardSum_sub_comp]
    rw [Finset.sum_sub_distrib]
    simp [backwardSum]
  have hW' : (W : ℝ) ≠ 0 := by exact_mod_cast hW
  unfold backwardAverage backgroundTransfer
  field_simp
  nlinarith

end InvariantProjection.Continuity

namespace InvariantProjection.Continuity

open Function MeasureTheory
open scoped ENNReal

variable {X : Type*}

theorem support_relocationTransfer_subset (σ : X ≃ X) (h : X → ℝ)
    (φ : ℕ → X → ℝ) (H : ℕ) :
    support (relocationTransfer σ h φ H) ⊆
      ⋃ r ∈ Finset.range H, ((σ.symm : X → X)^[r + 1]) ⁻¹' support h := by
  intro x hx
  by_contra hxU
  apply hx
  apply relocationTransfer_eq_zero
  intro r hr hrH
  by_contra hne
  apply hxU
  refine Set.mem_iUnion.mpr ⟨r - 1, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_range.mpr (by omega)
  · change h ((σ.symm : X → X)^[r - 1 + 1] x) ≠ 0
    simpa [Nat.sub_add_cancel hr] using hne

end InvariantProjection.Continuity

namespace InvariantProjection.Continuity

open Function MeasureTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem measure_support_relocationTransfer_le (σ : X ≃ᵐ X)
    (hσ : MeasurePreserving σ μ μ) (h : X → ℝ) (hh : Measurable h)
    (φ : ℕ → X → ℝ) (H : ℕ) :
    μ (support (relocationTransfer σ.toEquiv h φ H)) ≤
      (H : ℝ≥0∞) * μ (support h) := by
  have hb := hσ.symm σ
  calc
    μ (support (relocationTransfer σ.toEquiv h φ H)) ≤
        μ (⋃ r ∈ Finset.range H,
          ((σ.symm : X → X)^[r + 1]) ⁻¹' support h) :=
      measure_mono (support_relocationTransfer_subset σ.toEquiv h φ H)
    _ ≤ ∑ r ∈ Finset.range H,
        μ (((σ.symm : X → X)^[r + 1]) ⁻¹' support h) :=
      measure_biUnion_finset_le _ _
    _ = ∑ _r ∈ Finset.range H, μ (support h) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (hb.iterate (r + 1)).measure_preimage (measurableSet_support hh).nullMeasurableSet
    _ = (H : ℝ≥0∞) * μ (support h) := by simp

end InvariantProjection.Continuity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TransferSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
open MeasureTheory Set Filter

namespace Invariant233.TransferSupport

variable {X : Type*}

variable [MeasurableSpace X] {μ : Measure X}

theorem ae_finite_transfer_support {ι : Type*} [Countable ι] (d : ι → X → ℝ)
    (hd : ∑' i, μ (Function.support (d i)) ≠ ∞) :
    ∀ᵐ x ∂μ, (Function.support (fun i => d i x)).Finite := by
  simpa only [Function.support, Set.mem_ofPred_eq] using
    (ae_finite_setOfPred_mem hd)

theorem ae_finite_transfer_support_pair {ι : Type*} [Countable ι]
    (d : ι → X → ℝ) (hd : ∑' i, μ (Function.support (d i)) ≠ ∞)
    (σ : X → X) (hσ : Measure.QuasiMeasurePreserving σ μ μ) :
    ∀ᵐ x ∂μ, (Function.support (fun i => d i x)).Finite ∧
      (Function.support (fun i => d i (σ x))).Finite := by
  exact (ae_finite_transfer_support d hd).and
    (hσ.ae (ae_finite_transfer_support d hd))

theorem ae_tsum_coboundary {ι : Type*} [Countable ι]
    (h g d : ι → X → ℝ) (σ : X → X)
    (hσ : Measure.QuasiMeasurePreserving σ μ μ)
    (hd : ∑' i, μ (Function.support (d i)) ≠ ∞)
    (hh : ∀ᵐ x ∂μ, Summable (fun i => h i x))
    (heq : ∀ i, g i =ᵐ[μ] fun x => h i x + d i x - d i (σ x)) :
    ∀ᵐ x ∂μ, Summable (fun i => g i x) ∧
      (∑' i, g i x) = (∑' i, h i x) + (∑' i, d i x) - (∑' i, d i (σ x)) := by
  filter_upwards [hh, ae_finite_transfer_support_pair d hd σ hσ,
    ae_all_iff.mpr heq] with x hhx hdx heqx
  have hd0 : Summable (fun i => d i x) := summable_of_hasFiniteSupport hdx.1
  have hd1 : Summable (fun i => d i (σ x)) := summable_of_hasFiniteSupport hdx.2
  have hg : Summable (fun i => g i x) :=
    ((hhx.add hd0).sub hd1).congr (fun i => (heqx i).symm)
  refine ⟨hg, ?_⟩
  calc
    (∑' i, g i x) = ∑' i, (h i x + d i x - d i (σ x)) := tsum_congr heqx
    _ = (∑' i, h i x) + (∑' i, d i x) - (∑' i, d i (σ x)) := by
      rw [(hhx.add hd0).tsum_sub hd1, hhx.tsum_add hd0]

theorem tsum_measure_support_add_ne_top {ι : Type*} [Countable ι]
    (d e : ι → X → ℝ)
    (hd : ∑' i, μ (Function.support (d i)) ≠ ∞)
    (he : ∑' i, μ (Function.support (e i)) ≠ ∞) :
    ∑' i, μ (Function.support (fun x => d i x + e i x)) ≠ ∞ := by
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hd, he⟩)
  calc
    _ ≤ ∑' i, (μ (Function.support (d i)) + μ (Function.support (e i))) := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact (measure_mono (Function.support_add _ _)).trans (measure_union_le _ _)
    _ = (∑' i, μ (Function.support (d i))) + ∑' i, μ (Function.support (e i)) :=
      ENNReal.tsum_add

theorem assemble_continuous_coboundary {ι : Type*} [Countable ι]
    (cost moved d e : ι → X → ℝ) (g₀ b₀ : X → ℝ) (σ : X → X)
    (hσ : Measure.QuasiMeasurePreserving σ μ μ)
    (hmb₀ : Measurable b₀) (hmd : ∀ i, Measurable (d i))
    (hme : ∀ i, Measurable (e i))
    (hd : ∑' i, μ (Function.support (d i)) ≠ ∞)
    (he : ∑' i, μ (Function.support (e i)) ≠ ∞)
    (hcost : ∀ᵐ x ∂μ, Summable (fun i => cost i x))
    (hmoved : ∀ i, moved i =ᵐ[μ] fun x => cost i x +
      (d i x + e i x) - (d i (σ x) + e i (σ x)))
    (hbackground : g₀ =ᵐ[μ] fun x => 1 + b₀ (σ x) - b₀ x) :
    ∃ b : X → ℝ, Measurable b ∧
      (∀ x, b x = b₀ x - ∑' i, (d i x + e i x)) ∧
      ∀ᵐ x ∂μ, g₀ x + (∑' i, moved i x) =
        (∑' i, cost i x) + 1 + b (σ x) - b x := by
  let D : ι → X → ℝ := fun i x => d i x + e i x
  have hD : ∑' i, μ (Function.support (D i)) ≠ ∞ :=
    tsum_measure_support_add_ne_top d e hd he
  refine ⟨fun x => b₀ x - ∑' i, D i x,
    hmb₀.sub (Measurable.tsum fun i => (hmd i).add (hme i)), fun _ => rfl, ?_⟩
  filter_upwards [ae_tsum_coboundary cost moved D σ hσ hD hcost hmoved,
    hbackground] with x hsum hbg
  rw [hsum.2, hbg]
  ring

end Invariant233.TransferSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BackgroundTransfer
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter Function
open scoped ENNReal

namespace InvariantProjection.Continuity

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem measurable_backgroundTransfer (σ : X ≃ᵐ X) (v : X → ℝ)
    (W : ℕ) (hv : Measurable v) :
    Measurable (backgroundTransfer σ.toEquiv v W) := by
  unfold backgroundTransfer backwardSum
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro n hn
  apply Finset.measurable_sum
  intro r hr
  exact hv.comp (σ.symm.measurable.iterate (r + 1))

omit [MeasurableSpace X] in

theorem support_backgroundTransfer_subset (σ : X ≃ X) (v : X → ℝ) (W : ℕ) :
    support (backgroundTransfer σ v W) ⊆
      ⋃ r ∈ Finset.range W, ((σ.symm : X → X)^[r + 1]) ⁻¹' support v := by
  intro x hx
  have hsum : (∑ n ∈ Finset.range W, backwardSum σ v (n + 1) x) ≠ 0 :=
    (mul_ne_zero_iff.mp hx).2
  obtain ⟨n, hn, hnx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  obtain ⟨r, hr, hrx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnx
  refine Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨?_, hrx⟩⟩
  apply Finset.mem_range.mpr
  have hn' := Finset.mem_range.mp hn
  have hr' := Finset.mem_range.mp hr
  omega

theorem measure_support_backgroundTransfer_le (σ : X ≃ᵐ X)
    (hσ : MeasurePreserving σ μ μ) (v : X → ℝ) (W : ℕ) :
    μ (support (backgroundTransfer σ.toEquiv v W)) ≤
      (W : ℝ≥0∞) * μ (support v) := by
  calc
    _ ≤ μ (⋃ r ∈ Finset.range W,
        ((σ.symm : X → X)^[r + 1]) ⁻¹' support v) :=
      measure_mono (support_backgroundTransfer_subset σ.toEquiv v W)
    _ ≤ ∑ r ∈ Finset.range W,
        μ (((σ.symm : X → X)^[r + 1]) ⁻¹' support v) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _r ∈ Finset.range W, μ (support v) := by
      exact Finset.sum_le_sum fun r _ => ((hσ.symm σ).iterate (r + 1)).measure_preimage_le _
    _ = _ := by simp

end InvariantProjection.Continuity

namespace Invariant233.BackgroundCost

open InvariantProjection.Continuity Invariant233.TransferSupport

variable {θ : ℝ} (d : BackgroundBumpData θ)

theorem tsum_measure_backgroundTransfer_support_ne_top :
    (∑' n, circleMeasure (support (backgroundTransfer
      (Equiv.addRight (θ : Circle)) (d.bump n) (2 ^ (n + 2))))) ≠ ∞ := by
  apply ne_top_of_le_ne_top (show (1 / 2 : ℝ≥0∞) ≠ ∞ by norm_num)
  apply le_trans _ d.weighted_support_bound
  apply ENNReal.tsum_le_tsum
  intro n
  calc
    _ ≤ ((2 ^ (n + 2) : ℕ) : ℝ≥0∞) * circleMeasure (support (d.bump n)) :=
      measure_support_backgroundTransfer_le (MeasurableEquiv.addRight (θ : Circle))
        (measurePreserving_add_right volume _) _ _
    _ ≤ (2 : ℝ≥0∞) ^ (n + 2) * circleMeasure (Metric.closedBall 0 (d.radius n)) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        mul_le_mul_right (measure_mono (d.bump_support n))
          (((2 ^ (n + 2) : ℕ) : ℝ≥0∞))

theorem tsum_measure_backgroundBump_support_ne_top :
    (∑' n, circleMeasure (support (d.bump n))) ≠ ∞ := by
  apply ne_top_of_le_ne_top (show (1 / 2 : ℝ≥0∞) ≠ ∞ by norm_num)
  apply le_trans _ d.weighted_support_bound
  apply ENNReal.tsum_le_tsum
  intro n
  calc
    _ ≤ circleMeasure (Metric.closedBall 0 (d.radius n)) := measure_mono (d.bump_support n)
    _ ≤ (2 : ℝ≥0∞) ^ (n + 2) * circleMeasure (Metric.closedBall 0 (d.radius n)) := by
      exact le_mul_of_one_le_left' (one_le_pow₀ (by norm_num))

theorem measurable_backgroundTransferSum : Measurable (backgroundTransferSum d) := by
  apply Measurable.tsum
  intro n
  exact measurable_backgroundTransfer (MeasurableEquiv.addRight (θ : Circle))
    _ _ (d.continuous_bump n).measurable

theorem backgroundCost_ae_coboundary :
    backgroundCost d =ᵐ[circleMeasure] fun x =>
      1 + backgroundTransferSum d (x + (θ : Circle)) - backgroundTransferSum d x := by
  have hsum : ∀ᵐ x ∂circleMeasure, Summable (fun n => d.bump n x) :=
    (ae_finite_transfer_support _ (tsum_measure_backgroundBump_support_ne_top d)).mono
      (fun _ hx => summable_of_hasFiniteSupport hx)
  have hneg := ae_tsum_coboundary d.bump (backgroundNegative d)
    (fun n => backgroundTransfer (Equiv.addRight (θ : Circle)) (d.bump n) (2 ^ (n + 2)))
    (fun x : Circle => x + (θ : Circle))
    (measurePreserving_add_right volume _).quasiMeasurePreserving
    (tsum_measure_backgroundTransfer_support_ne_top d) hsum (fun n => by
      apply Eventually.of_forall
      intro x
      have h := background_coboundary (Equiv.addRight (θ : Circle)) (d.bump n)
        (2 ^ (n + 2)) (pow_ne_zero _ (by norm_num)) x
      change backgroundNegative d n x = _
      change d.bump n x - backgroundNegative d n x = _ at h
      change d.bump n x - backgroundNegative d n x =
        backgroundTransfer (Equiv.addRight (θ : Circle)) (d.bump n) (2 ^ (n + 2))
          (x + (θ : Circle)) -
        backgroundTransfer (Equiv.addRight (θ : Circle)) (d.bump n) (2 ^ (n + 2)) x at h
      linarith)
  filter_upwards [hneg] with x hx
  unfold backgroundCost backgroundTransferSum
  rw [hx.2]
  ring

end Invariant233.BackgroundCost

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_SawtoothSmoothing
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.InvariantProjection.Continuity.circleSmoothSawtooth_coe _root_.OAI.InvariantProjection.Continuity.circleSmoothedDrop_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.Continuity

open MeasureTheory Set

theorem continuous_smoothedDrop (C a δ : ℝ) : Continuous (smoothedDrop C a δ) := by
  unfold smoothedDrop
  exact continuous_const.mul ((continuous_const.add (continuous_smoothSawtooth δ)).sub
    ((continuous_smoothSawtooth δ).comp (continuous_id.add_const a)))

theorem smoothSawtooth_eq_fract_of_middle {δ u : ℝ} (hδ : 0 < δ)
    (hlo : δ ≤ Int.fract u) (hhi : Int.fract u + δ < 1) :
    smoothSawtooth δ u = Int.fract u := by
  have hi : (∫ t in -δ..δ, Int.fract (u + t)) =
      ∫ t in -δ..δ, Int.fract u + t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith : -δ ≤ δ)] at ht
    change Int.fract (u + t) = Int.fract u + t
    rw [← fract_fract_add]
    apply Int.fract_eq_self.mpr
    constructor <;> linarith [ht.1, ht.2]
  unfold smoothSawtooth
  rw [hi, intervalIntegral.integral_add
    (f := fun _ : ℝ => Int.fract u) (g := fun t : ℝ => t)
    intervalIntegrable_const (continuous_id.intervalIntegrable (-δ) δ),
    intervalIntegral.integral_const, integral_id]
  simp only [smul_eq_mul]
  field_simp
  ring

theorem smoothingTransfer_eq_zero_of_middle {δ u : ℝ} (C : ℝ)
    (hδ : 0 < δ) (hlo : δ ≤ Int.fract u) (hhi : Int.fract u + δ < 1) :
    smoothingTransfer C δ u = 0 := by
  simp [smoothingTransfer, smoothSawtooth_eq_fract_of_middle hδ hlo hhi]

theorem smoothedDrop_eq_zero_of_middle {a δ u : ℝ} (C : ℝ)
    (ha : 0 ≤ a) (hδ : 0 < δ) (hlo : δ ≤ Int.fract u)
    (hhi : Int.fract u + a + δ < 1) : smoothedDrop C a δ u = 0 := by
  rw [smoothedDrop_eq_average C a δ u hδ.ne']
  have hi : (∫ t in -δ..δ, (⌊Int.fract (u + t) + a⌋ : ℝ)) = 0 := by
    calc
      _ = ∫ _t in -δ..δ, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith : -δ ≤ δ)] at ht
        have hf : Int.fract (u + t) = Int.fract u + t := by
          rw [← fract_fract_add]
          apply Int.fract_eq_self.mpr
          constructor <;> linarith [ht.1, ht.2]
        have hz : ⌊Int.fract (u + t) + a⌋ = 0 := by
          rw [hf, Int.floor_eq_iff]
          constructor <;> norm_num <;> linarith [ht.1, ht.2]
        change (⌊Int.fract (u + t) + a⌋ : ℝ) = 0
        rw [hz, Int.cast_zero]
      _ = 0 := by simp
  rw [hi, mul_zero]

theorem measure_smoothingTransfer_support_le {δ : ℝ} (C : ℝ) (hδ : 0 < δ) :
    volume {u : ℝ | u ∈ Ico 0 1 ∧ smoothingTransfer C δ u ≠ 0} ≤
      ENNReal.ofReal (2 * δ) := by
  have hsub : {u : ℝ | u ∈ Ico 0 1 ∧ smoothingTransfer C δ u ≠ 0} ⊆
      Icc 0 δ ∪ Icc (1 - δ) 1 := by
    intro u hu
    by_contra hout
    have hfrac : Int.fract u = u := Int.fract_eq_self.mpr hu.1
    have hleft : δ < u := by
      by_contra hn
      exact hout (Or.inl ⟨hu.1.1, le_of_not_gt hn⟩)
    have hright : u < 1 - δ := by
      by_contra hn
      exact hout (Or.inr ⟨le_of_not_gt hn, hu.1.2.le⟩)
    apply hu.2
    apply smoothingTransfer_eq_zero_of_middle C hδ
    · simpa [hfrac] using hleft.le
    · rw [hfrac]
      linarith
  calc
    _ ≤ volume (Icc 0 δ ∪ Icc (1 - δ) 1) := measure_mono hsub
    _ ≤ volume (Icc 0 δ) + volume (Icc (1 - δ) 1) := measure_union_le _ _
    _ = ENNReal.ofReal δ + ENNReal.ofReal δ := by simp
    _ = ENNReal.ofReal (2 * δ) := by
      rw [← ENNReal.ofReal_add hδ.le hδ.le]
      congr 1
      ring

theorem measure_smoothedDrop_support_le {a δ : ℝ} (C : ℝ)
    (ha : 0 ≤ a) (hδ : 0 < δ) :
    volume {u : ℝ | u ∈ Ico 0 1 ∧ smoothedDrop C a δ u ≠ 0} ≤
      ENNReal.ofReal (a + 2 * δ) := by
  have hsub : {u : ℝ | u ∈ Ico 0 1 ∧ smoothedDrop C a δ u ≠ 0} ⊆
      Icc 0 δ ∪ Icc (1 - a - δ) 1 := by
    intro u hu
    by_contra hout
    have hfrac : Int.fract u = u := Int.fract_eq_self.mpr hu.1
    have hleft : δ < u := by
      by_contra hn
      exact hout (Or.inl ⟨hu.1.1, le_of_not_gt hn⟩)
    have hright : u < 1 - a - δ := by
      by_contra hn
      exact hout (Or.inr ⟨le_of_not_gt hn, hu.1.2.le⟩)
    apply hu.2
    apply smoothedDrop_eq_zero_of_middle C ha hδ
    · simpa [hfrac] using hleft.le
    · rw [hfrac]
      linarith
  calc
    _ ≤ volume (Icc 0 δ ∪ Icc (1 - a - δ) 1) := measure_mono hsub
    _ ≤ volume (Icc 0 δ) + volume (Icc (1 - a - δ) 1) := measure_union_le _ _
    _ = ENNReal.ofReal δ + ENNReal.ofReal (a + δ) := by
      rw [Real.volume_Icc, Real.volume_Icc]
      congr 1 <;> congr 1 <;> ring
    _ = ENNReal.ofReal (a + 2 * δ) := by
      rw [← ENNReal.ofReal_add hδ.le (by linarith)]
      congr 1
      ring

end InvariantProjection.Continuity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleCharacterDynamics
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
namespace CircleCharacterDynamics

local notation "Circle" => AddCircle (1 : ℝ)
local notation "rep" => (fun x : Circle => (AddCircle.equivIco (1 : ℝ) 0 x : ℝ))

theorem coe_representative (x : Circle) : ((rep x : ℝ) : Circle) = x :=
  AddCircle.coe_equivIco

theorem representative_add_real (x : Circle) (t : ℝ) :
    rep (x + (t : Circle)) = Int.fract (rep x + t) := by
  rw [← representative_coe]
  congr 1
  rw [AddCircle.coe_add, coe_representative]

theorem zsmul_real_phase (q : ℤ) (θ : ℝ) :
    q • (θ : Circle) = ((Int.fract ((q : ℝ) * θ) : ℝ) : Circle) := by
  rw [AddCircle.coe_fract]
  simpa only [zsmul_eq_mul] using
    (AddCircle.coe_zsmul (p := (1 : ℝ)) (n := q) (x := θ)).symm

theorem character_orbit_representative (q v : ℤ) (θ : ℝ) (x : Circle) :
    rep (q • (x + v • (θ : Circle))) =
      Int.fract (rep (q • x) + (v : ℝ) * Int.fract ((q : ℝ) * θ)) := by
  rw [zsmul_add, smul_comm q v, zsmul_real_phase]
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  exact representative_add_real _ _

end CircleCharacterDynamics
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleSmoothing
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.Continuity

open MeasureTheory Set
local notation "Circle" => AddCircle (1 : ℝ)
local notation "rep" => (fun x : Circle => (AddCircle.equivIco (1 : ℝ) 0 x : ℝ))

theorem circleSmoothingTransfer_eq_representative (C δ : ℝ) (x : Circle) :
    circleSmoothingTransfer C δ x = smoothingTransfer C δ (rep x) := by
  unfold circleSmoothingTransfer smoothingTransfer
  have hs : circleSmoothSawtooth δ x = smoothSawtooth δ (rep x) := by
    rw [← circleSmoothSawtooth_coe]
    exact congrArg (circleSmoothSawtooth δ) AddCircle.coe_equivIco.symm
  rw [hs]
  have hr : Int.fract (rep x) = rep x :=
    Int.fract_eq_self.mpr (by simpa using (AddCircle.equivIco 1 0 x).property)
  rw [hr]

theorem circleSmoothedDrop_eq_add_coboundary (C a δ : ℝ) (x : Circle) :
    circleSmoothedDrop C a δ x = C * (⌊rep x + a⌋ : ℝ) +
      circleSmoothingTransfer C δ x -
        circleSmoothingTransfer C δ (x + (a : Circle)) := by
  unfold circleSmoothedDrop circleSmoothingTransfer
  have hf : (⌊rep x + a⌋ : ℝ) = a + rep x - rep (x + (a : Circle)) := by
    rw [Invariant233.CircleCharacterDynamics.representative_add_real]
    have ht := Int.floor_add_fract (rep x + a)
    linarith
  rw [hf]
  ring

theorem measurable_circleSmoothingTransfer (C δ : ℝ) :
    Measurable (circleSmoothingTransfer C δ) := by
  unfold circleSmoothingTransfer
  exact measurable_const.mul ((continuous_circleSmoothSawtooth δ).measurable.sub
    Invariant233.CocycleSupport.measurePreserving_circleRepresentative.measurable)

theorem measure_circleSmoothingTransfer_support_le {δ : ℝ} (C : ℝ)
    (hδ : 0 < δ) :
    volume (Function.support (circleSmoothingTransfer C δ)) ≤ ENNReal.ofReal (2 * δ) := by
  have hm : Measurable (smoothingTransfer C δ) := by
    unfold smoothingTransfer
    exact measurable_const.mul ((continuous_smoothSawtooth δ).measurable.sub measurable_fract)
  have hs : MeasurableSet (Function.support (smoothingTransfer C δ)) := measurableSet_support hm
  have he := Invariant233.CocycleSupport.measurePreserving_circleRepresentative.measure_preimage
    hs.nullMeasurableSet
  rw [Measure.restrict_apply hs] at he
  have hsupp : Function.support (circleSmoothingTransfer C δ) =
      rep ⁻¹' Function.support (smoothingTransfer C δ) := by
    ext x
    simp only [Function.mem_support, Set.mem_preimage, circleSmoothingTransfer_eq_representative]
  rw [hsupp, he]
  convert measure_smoothingTransfer_support_le C hδ using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext u
  simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_ofPred_eq, and_comm]

theorem measure_circleSmoothedDrop_support_le {a δ : ℝ} (C : ℝ)
    (ha : 0 ≤ a) (hδ : 0 < δ) :
    volume (Function.support (circleSmoothedDrop C a δ)) ≤
      ENNReal.ofReal (a + 2 * δ) := by
  have hs : MeasurableSet (Function.support (smoothedDrop C a δ)) :=
    measurableSet_support (continuous_smoothedDrop C a δ).measurable
  have he := Invariant233.CocycleSupport.measurePreserving_circleRepresentative.measure_preimage
    hs.nullMeasurableSet
  rw [Measure.restrict_apply hs] at he
  have hsupp : Function.support (circleSmoothedDrop C a δ) =
      rep ⁻¹' Function.support (smoothedDrop C a δ) := by
    ext x
    simp only [Function.mem_support, Set.mem_preimage, circleSmoothedDrop_eq_representative]
  rw [hsupp, he]
  convert measure_smoothedDrop_support_le C ha hδ using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext u
  simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_ofPred_eq, and_comm]

theorem measure_characterSmoothedDrop_support_le {a δ : ℝ} (C : ℝ)
    (ha : 0 ≤ a) (hδ : 0 < δ) {q : ℤ} (hq : q ≠ 0) :
    volume (Function.support (fun x : Circle => circleSmoothedDrop C a δ (q • x))) ≤
      ENNReal.ofReal (a + 2 * δ) := by
  have hp := Measure.measurePreserving_zsmul (volume : Measure Circle) hq
  have hs := measurableSet_support (continuous_circleSmoothedDrop C a δ).measurable
  change volume ((fun x : Circle => q • x) ⁻¹' Function.support (circleSmoothedDrop C a δ)) ≤ _
  rw [hp.measure_preimage hs.nullMeasurableSet]
  exact measure_circleSmoothedDrop_support_le C ha hδ

theorem measure_characterSmoothingTransfer_support_le {δ : ℝ} (C : ℝ)
    (hδ : 0 < δ) {q : ℤ} (hq : q ≠ 0) :
    volume (Function.support (fun x : Circle => circleSmoothingTransfer C δ (q • x))) ≤
      ENNReal.ofReal (2 * δ) := by
  have hp := Measure.measurePreserving_zsmul (volume : Measure Circle) hq
  have hm : Measurable (circleSmoothingTransfer C δ) := by
    unfold circleSmoothingTransfer
    exact measurable_const.mul ((continuous_circleSmoothSawtooth δ).measurable.sub
      Invariant233.CocycleSupport.measurePreserving_circleRepresentative.measurable)
  change volume ((fun x : Circle => q • x) ⁻¹' Function.support (circleSmoothingTransfer C δ)) ≤ _
  rw [hp.measure_preimage (measurableSet_support hm).nullMeasurableSet]
  exact measure_circleSmoothingTransfer_support_le C hδ

theorem characterSmoothedDrop_eq_add_coboundary (C θ δ : ℝ) (q : ℤ) (x : Circle) :
    circleSmoothedDrop C (Int.fract ((q : ℝ) * θ)) δ (q • x) =
      C * (⌊rep (q • x) + Int.fract ((q : ℝ) * θ)⌋ : ℝ) +
      circleSmoothingTransfer C δ (q • x) -
      circleSmoothingTransfer C δ (q • (x + (θ : Circle))) := by
  rw [zsmul_add, Invariant233.CircleCharacterDynamics.zsmul_real_phase]
  exact circleSmoothedDrop_eq_add_coboundary C (Int.fract ((q : ℝ) * θ)) δ (q • x)

end InvariantProjection.Continuity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ParameterTails
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.ParameterTails

theorem summable_partition_cost {K h : ℕ → ℝ} (hK : ∀ n, 0 < K n)
    (hdouble : ∀ n, 2 * K n ≤ K (n + 1)) (hh : ∀ n, 0 ≤ h n)
    (hheight : ∀ n, h (n + 1) / K (n + 1) ≤ (1 / 2 : ℝ) ^ n) :
    Summable (fun n => (1 + h n) / K n) := by
  have hsum : Summable (fun n => h n / K n) := by
    apply (summable_nat_add_iff 1).mp
    exact Summable.of_nonneg_of_le
      (fun n => div_nonneg (hh (n + 1)) (hK (n + 1)).le)
      hheight summable_geometric_two
  simpa only [add_div] using (summable_reciprocal hK hdouble).add hsum

end Invariant233.ParameterTails

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleParameterConsequences
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.CircleParameterData.blockEnd_zero _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
open Filter
open scoped Topology

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem shifted_K_pos (n : ℕ) : 0 < (p.K (n + 1) : ℝ) := by
  exact_mod_cast hp.K_pos (n + 1) (by omega)

theorem shifted_K_double (n : ℕ) :
    2 * (p.K (n + 1) : ℝ) ≤ (p.K (n + 1 + 1) : ℝ) := by
  exact_mod_cast (hp.K_double (n + 1) (by omega)).le

theorem summable_reciprocal : Summable (fun n : ℕ => 1 / (p.K (n + 1) : ℝ)) :=
  ParameterTails.summable_reciprocal hp.shifted_K_pos hp.shifted_K_double

theorem summable_partition_cost :
    Summable (fun n : ℕ => (1 + (p.height (n + 1) : ℝ)) / p.K (n + 1)) := by
  apply ParameterTails.summable_partition_cost hp.shifted_K_pos hp.shifted_K_double
    (fun n => Nat.cast_nonneg (p.height (n + 1)))
  intro n
  have hh := hp.continuity_height (n + 1) (by omega)
  have hpow : (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ n := by
    rw [pow_succ]
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) n]
  exact hh.trans hpow

end CircleParameterLaws
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CirclePhaseSummability
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
open scoped BigOperators ENNReal

namespace CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem block_phase_sum_le (j : ℕ) (hj : 1 ≤ j) :
    (∑ i ∈ p.block j, p.alpha θ i) ≤ 2 / (p.K j : ℝ) := by
  have hm : (p.m j : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos j hj).ne'
  have hK : (p.K j : ℝ) ≠ 0 := by exact_mod_cast (hp.K_pos j hj).ne'
  calc
    (∑ i ∈ p.block j, p.alpha θ i) ≤ ∑ i ∈ p.block j, 2 / p.N j := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hp.phase_bounds j hj i hi).2.le
    _ = ((p.block j).card : ℝ) * (2 / p.N j) := by simp
    _ = 2 / (p.K j : ℝ) := by
      rw [p.card_block j hj]
      simp only [CircleParameterData.N]
      field_simp

theorem summable_block_phases :
    Summable (fun n : ℕ => ∑ i ∈ p.block (n + 1), p.alpha θ i) := by
  apply Summable.of_nonneg_of_le
    (fun n => Finset.sum_nonneg (fun i _ => Int.fract_nonneg _))
    (fun n => hp.block_phase_sum_le (n + 1) (by omega))
  simpa only [mul_one_div] using hp.summable_reciprocal.mul_left 2

end CircleParameterLaws
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ParameterSmoothing
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233

open MeasureTheory Set InvariantProjection.Continuity
open scoped ENNReal

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

omit hp in

theorem measurable_smoothBlockTransfer (p : CircleParameterData) (θ : ℝ) (j : ℕ) :
    Measurable (p.smoothBlockTransfer θ j) := by
  unfold CircleParameterData.smoothBlockTransfer
  apply Finset.measurable_sum
  intro i _hi
  exact (measurable_circleSmoothingTransfer _ _).comp
    (continuous_id.zsmul (p.q i : ℤ)).measurable

omit hp in

theorem smoothBlock_eq_add_coboundary (j : ℕ) (x : Circle) :
    p.smoothBlock θ j x = p.rawBlock θ j x + p.smoothBlockTransfer θ j x -
      p.smoothBlockTransfer θ j (x + (θ : Circle)) := by
  unfold CircleParameterData.smoothBlock CircleParameterData.rawBlock
    CircleParameterData.smoothBlockTransfer
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  convert characterSmoothedDrop_eq_add_coboundary (p.C j) θ (p.alpha θ i / 4)
    (p.q i : ℤ) x using 1 <;>
    simp only [CircleParameterData.alpha, CircleParameterData.coordinate,
      CircleParameterData.rep, Int.cast_natCast, natCast_zsmul]

theorem relocatedBlock_eq_add_coboundary (j : ℕ) (hj : 1 ≤ j) (x : Circle) :
    p.relocatedBlock θ j x = p.smoothBlock θ j x + p.relocatedBlockTransfer θ j x -
      p.relocatedBlockTransfer θ j (x + (θ : Circle)) := by
  exact relocated_eq_add_coboundary _ _ _ _ x (hp.partition_sum j hj x)

omit hp in
private theorem measure_support_finsetSum_le {ι : Type*} (s : Finset ι)
    (f : ι → Circle → ℝ) :
    volume (Function.support (fun x => ∑ i ∈ s, f i x)) ≤
      ∑ i ∈ s, volume (Function.support (f i)) := by
  have hsub : Function.support (fun x => ∑ i ∈ s, f i x) ⊆
      ⋃ i ∈ s, Function.support (f i) := by
    intro x hx
    by_contra hn
    apply hx
    apply Finset.sum_eq_zero
    intro i hi
    by_contra hne
    exact hn (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hne⟩⟩)
  exact (measure_mono hsub).trans (measure_biUnion_finset_le s _)

theorem measure_smoothBlock_support_le (j : ℕ) (hj : 1 ≤ j) :
    volume (Function.support (p.smoothBlock θ j)) ≤ ENNReal.ofReal (3 / (p.K j : ℝ)) := by
  have hα (i : ℕ) (hi : i ∈ p.block j) := hp.block_phase_pos j hj i hi
  calc
    _ ≤ ∑ i ∈ p.block j, volume (Function.support (fun x : Circle =>
        circleSmoothedDrop (p.C j) (p.alpha θ i) (p.alpha θ i / 4) ((p.q i : ℤ) • x))) :=
      measure_support_finsetSum_le _ _
    _ ≤ ∑ i ∈ p.block j, ENNReal.ofReal (p.alpha θ i + 2 * (p.alpha θ i / 4)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact measure_characterSmoothedDrop_support_le _ (hα i hi).le
        (div_pos (hα i hi) (by norm_num)) (by exact_mod_cast (hp.q_pos i).ne')
    _ = ENNReal.ofReal (∑ i ∈ p.block j, (p.alpha θ i + 2 * (p.alpha θ i / 4))) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro i hi
      have := (hα i hi).le
      positivity
    _ ≤ ENNReal.ofReal (3 / (p.K j : ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = (3 / 2 : ℝ) * ∑ i ∈ p.block j, p.alpha θ i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ (3 / 2 : ℝ) * (2 / (p.K j : ℝ)) :=
          mul_le_mul_of_nonneg_left (hp.block_phase_sum_le j hj) (by norm_num)
        _ = _ := by ring

theorem measure_smoothBlockTransfer_support_le (j : ℕ) (hj : 1 ≤ j) :
    volume (Function.support (p.smoothBlockTransfer θ j)) ≤
      ENNReal.ofReal (1 / (p.K j : ℝ)) := by
  have hα (i : ℕ) (hi : i ∈ p.block j) := hp.block_phase_pos j hj i hi
  calc
    _ ≤ ∑ i ∈ p.block j, volume (Function.support (fun x : Circle =>
        circleSmoothingTransfer (p.C j) (p.alpha θ i / 4) ((p.q i : ℤ) • x))) :=
      measure_support_finsetSum_le _ _
    _ ≤ ∑ i ∈ p.block j, ENNReal.ofReal (2 * (p.alpha θ i / 4)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact measure_characterSmoothingTransfer_support_le _
        (div_pos (hα i hi) (by norm_num)) (by exact_mod_cast (hp.q_pos i).ne')
    _ = ENNReal.ofReal (∑ i ∈ p.block j, 2 * (p.alpha θ i / 4)) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro i hi
      have := (hα i hi).le
      positivity
    _ ≤ ENNReal.ofReal (1 / (p.K j : ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = (1 / 2 : ℝ) * ∑ i ∈ p.block j, p.alpha θ i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ (1 / 2 : ℝ) * (2 / (p.K j : ℝ)) :=
          mul_le_mul_of_nonneg_left (hp.block_phase_sum_le j hj) (by norm_num)
        _ = _ := by ring

theorem tsum_smoothBlock_support_ne_top :
    (∑' n : ℕ, volume (Function.support (p.smoothBlock θ (n + 1)))) ≠ ⊤ := by
  have hsum := (hp.summable_reciprocal.mul_left 3).tsum_ofReal_ne_top
  apply ne_top_of_le_ne_top hsum
  apply ENNReal.tsum_le_tsum
  intro n
  simpa only [mul_one_div] using hp.measure_smoothBlock_support_le (n + 1) (by omega)

theorem tsum_smoothBlockTransfer_support_ne_top :
    (∑' n : ℕ, volume (Function.support (p.smoothBlockTransfer θ (n + 1)))) ≠ ⊤ := by
  apply ne_top_of_le_ne_top hp.summable_reciprocal.tsum_ofReal_ne_top
  exact ENNReal.tsum_le_tsum (fun n =>
    hp.measure_smoothBlockTransfer_support_le (n + 1) (by omega))

theorem tsum_height_mul_smoothBlock_support_ne_top :
    (∑' n : ℕ, (p.height (n + 1) : ℝ≥0∞) *
      volume (Function.support (p.smoothBlock θ (n + 1)))) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (hp.summable_partition_cost.mul_left 3).tsum_ofReal_ne_top
  apply ENNReal.tsum_le_tsum
  intro n
  have hK : 0 < (p.K (n + 1) : ℝ) := hp.shifted_K_pos n
  calc
    _ ≤ (p.height (n + 1) : ℝ≥0∞) * ENNReal.ofReal (3 / (p.K (n + 1) : ℝ)) :=
      mul_le_mul_right (hp.measure_smoothBlock_support_le (n + 1) (by omega)) _
    _ = ENNReal.ofReal (3 * ((p.height (n + 1) : ℝ) / p.K (n + 1))) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (3 * ((1 + (p.height (n + 1) : ℝ)) / p.K (n + 1))) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_right (by linarith) hK.le

theorem tsum_relocatedBlockTransfer_support_ne_top :
    (∑' n : ℕ, volume (Function.support (p.relocatedBlockTransfer θ (n + 1)))) ≠ ⊤ := by
  apply ne_top_of_le_ne_top hp.tsum_height_mul_smoothBlock_support_ne_top
  apply ENNReal.tsum_le_tsum
  intro n
  exact measure_support_relocationTransfer_le (MeasurableEquiv.addRight (θ : Circle))
    (measurePreserving_add_right volume _) _ (continuous_smoothBlock p θ (n + 1)).measurable _ _

theorem ae_finite_smoothing_and_relocation_support :
    ∀ᵐ x : Circle, (Function.support (fun n : ℕ => p.smoothBlock θ (n + 1) x)).Finite ∧
      (Function.support (fun n : ℕ => p.smoothBlockTransfer θ (n + 1) x)).Finite ∧
      (Function.support (fun n : ℕ => p.relocatedBlockTransfer θ (n + 1) x)).Finite := by
  have h1 := ae_finite_setOfPred_mem hp.tsum_smoothBlock_support_ne_top
  have h2 := ae_finite_setOfPred_mem hp.tsum_smoothBlockTransfer_support_ne_top
  have h3 := ae_finite_setOfPred_mem hp.tsum_relocatedBlockTransfer_support_ne_top
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  exact ⟨hx1, hx2, hx3⟩

end CircleParameterLaws
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_RelocationSeries
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ENNReal BigOperators
open MeasureTheory Function

namespace InvariantProjection.Continuity

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem measurable_relocationTransfer (σ : X ≃ᵐ X) (h : X → ℝ)
    (φ : ℕ → X → ℝ) (H : ℕ) (hh : Measurable h)
    (hφ : ∀ n, Measurable (φ n)) :
    Measurable (relocationTransfer σ.toEquiv h φ H) := by
  unfold relocationTransfer backwardSum
  apply Finset.measurable_sum
  intro n hn
  apply Finset.measurable_sum
  intro r hr
  exact (hh.comp (σ.symm.measurable.iterate (r + 1))).mul
    ((hφ n).comp (σ.symm.measurable.iterate (r + 1)))

end InvariantProjection.Continuity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ContinuousConstruction
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Function Set
open scoped ENNReal

namespace Invariant233.CircleParameterLaws

open InvariantProjection.Continuity TransferSupport

variable {θ : ℝ} {p : CircleParameterData}

theorem measurable_relocatedBlockTransfer (j : ℕ) :
    Measurable (p.relocatedBlockTransfer θ j) :=
  measurable_relocationTransfer (MeasurableEquiv.addRight (θ : Circle)) _ _ _
    (continuous_smoothBlock p θ j).measurable (fun n => (p.partition j n).measurable)

theorem measurable_continuousTransfer (d : BackgroundBumpData θ) :
    Measurable (p.continuousTransfer θ d) :=
  (BackgroundCost.measurable_backgroundTransferSum d).sub (Measurable.tsum fun n =>
    (measurable_smoothBlockTransfer p θ (n + 1)).add
      (measurable_relocatedBlockTransfer (p := p) (θ := θ) (n + 1)))

variable (hp : CircleParameterLaws θ p)
include hp

theorem ae_summable_rawBlock :
    ∀ᵐ x ∂circleMeasure, Summable (fun n : ℕ => p.rawBlock θ (n + 1) x) := by
  have hfin := hp.ae_finite_smoothing_and_relocation_support
  have hfinshift := (measurePreserving_add_right (volume : Measure Circle)
    (θ : Circle)).quasiMeasurePreserving.ae hfin
  filter_upwards [hfin, hfinshift] with x hx hxσ
  have hs : Summable (fun n : ℕ => p.smoothBlock θ (n + 1) x) :=
    summable_of_hasFiniteSupport hx.1
  have hd : Summable (fun n : ℕ => p.smoothBlockTransfer θ (n + 1) x) :=
    summable_of_hasFiniteSupport hx.2.1
  have hdσ : Summable (fun n : ℕ => p.smoothBlockTransfer θ (n + 1) (x + (θ : Circle))) :=
    summable_of_hasFiniteSupport hxσ.2.1
  apply ((hs.sub hd).add hdσ).congr
  intro n
  have h := smoothBlock_eq_add_coboundary (p := p) (θ := θ) (n + 1) x
  linarith

theorem relocatedBlock_eq_raw_add_coboundary (j : ℕ) (hj : 1 ≤ j) (x : Circle) :
    p.relocatedBlock θ j x = p.rawBlock θ j x +
      (p.smoothBlockTransfer θ j x + p.relocatedBlockTransfer θ j x) -
      (p.smoothBlockTransfer θ j (x + (θ : Circle)) +
        p.relocatedBlockTransfer θ j (x + (θ : Circle))) := by
  rw [hp.relocatedBlock_eq_add_coboundary j hj x,
    smoothBlock_eq_add_coboundary j x]
  ring

theorem continuousCost_ae_coboundary (d : BackgroundBumpData θ) :
    p.continuousCost θ d =ᵐ[circleMeasure] fun x => p.rawCost θ x + 1 +
      p.continuousTransfer θ d (x + (θ : Circle)) - p.continuousTransfer θ d x := by
  obtain ⟨b, hb, hformula, heq⟩ := assemble_continuous_coboundary
    (fun n => p.rawBlock θ (n + 1)) (fun n => p.relocatedBlock θ (n + 1))
    (fun n => p.smoothBlockTransfer θ (n + 1))
    (fun n => p.relocatedBlockTransfer θ (n + 1))
    (backgroundCost d) (backgroundTransferSum d) (fun x : Circle => x + (θ : Circle))
    (measurePreserving_add_right volume _).quasiMeasurePreserving
    (BackgroundCost.measurable_backgroundTransferSum d)
    (fun n => measurable_smoothBlockTransfer p θ (n + 1))
    (fun n => measurable_relocatedBlockTransfer (n + 1))
    hp.tsum_smoothBlockTransfer_support_ne_top hp.tsum_relocatedBlockTransfer_support_ne_top
    hp.ae_summable_rawBlock
    (fun n => Eventually.of_forall (hp.relocatedBlock_eq_raw_add_coboundary (n + 1) (by omega)))
    (BackgroundCost.backgroundCost_ae_coboundary d)
  have hbdef : b = p.continuousTransfer θ d := funext hformula
  filter_upwards [heq] with x hx
  simpa only [hbdef, CircleParameterData.continuousCost, CircleParameterData.rawCost] using hx

end Invariant233.CircleParameterLaws

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_InvariantConull
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped ENNReal

namespace Invariant233

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem measurePreserving_equiv_zpow (σ : X ≃ᵐ X)
    (hσ : MeasurePreserving σ μ μ) (n : ℤ) :
    MeasurePreserving (σ.toEquiv ^ n) μ μ := by
  cases n with
  | ofNat n =>
      change MeasurePreserving (σ.toEquiv ^ (n : ℤ)) μ μ
      simpa only [zpow_natCast, Equiv.Perm.coe_pow, MeasurableEquiv.coe_toEquiv] using
        hσ.iterate n
  | negSucc n =>
      rw [zpow_negSucc, ← inv_pow]
      simpa only [Equiv.Perm.coe_pow, Equiv.Perm.inv_def,
        MeasurableEquiv.coe_toEquiv_symm] using
        (hσ.symm σ).iterate (n + 1)

theorem ae_forall_equiv_zpow (σ : X ≃ᵐ X) (hσ : MeasurePreserving σ μ μ)
    {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂μ, ∀ n : ℤ, P ((σ.toEquiv ^ n) x) := by
  exact ae_all_iff.mpr fun n =>
    (measurePreserving_equiv_zpow σ hσ n).quasiMeasurePreserving.ae hP

theorem exists_invariant_conull_subset_equiv (σ : X ≃ᵐ X)
    (hσ : MeasurePreserving σ μ μ) {s : Set X} (hs : MeasurableSet s)
    (hae : ∀ᵐ x ∂μ, x ∈ s) :
    ∃ t : Set X, MeasurableSet t ∧ t ⊆ s ∧ μ tᶜ = 0 ∧
      ∀ n : ℤ, (σ.toEquiv ^ n) ⁻¹' t = t := by
  let t : Set X := ⋂ n : ℤ, (σ.toEquiv ^ n) ⁻¹' s
  have htm : MeasurableSet t := MeasurableSet.iInter fun n =>
    hs.preimage (measurePreserving_equiv_zpow σ hσ n).measurable
  have ht : ∀ᵐ x ∂μ, x ∈ t := by
    simpa only [t, mem_iInter, mem_preimage] using ae_forall_equiv_zpow σ hσ hae
  refine ⟨t, htm, ?_, ?_, ?_⟩
  · intro x hx
    have hx0 := Set.mem_iInter.mp hx 0
    simpa only [mem_preimage, zpow_zero, Equiv.Perm.one_apply] using hx0
  · exact mem_ae_iff.mp ht
  · intro n
    ext x
    simp only [t, mem_preimage, mem_iInter]
    constructor
    · intro hx k
      have h := hx (k - n)
      simpa only [← Equiv.Perm.mul_apply, ← zpow_add, sub_add_cancel] using h
    · intro hx k
      simpa only [← Equiv.Perm.mul_apply, ← zpow_add] using hx (k + n)

theorem exists_invariant_exponential_coboundary_domain (σ : X ≃ᵐ X)
    (hσ : MeasurePreserving σ μ μ) (g gstar b : X → ℝ)
    (hg : Measurable g) (hgs : Measurable gstar) (hb : Measurable b)
    (heq : g =ᵐ[μ] fun x => gstar x + 1 + b (σ x) - b x) :
    ∃ s : Set X, MeasurableSet s ∧ μ sᶜ = 0 ∧
      (∀ n : ℤ, (σ.toEquiv ^ n) ⁻¹' s = s) ∧
      ∀ x ∈ s, ∀ k : ℤ,
        Real.exp (b ((σ.toEquiv ^ (k + 1)) x)) *
            Real.exp (-g ((σ.toEquiv ^ k) x)) =
          Real.exp (-1) * Real.exp (-gstar ((σ.toEquiv ^ k) x)) *
            Real.exp (b ((σ.toEquiv ^ k) x)) := by
  have hmeas : MeasurableSet {x | g x = gstar x + 1 + b (σ x) - b x} :=
    measurableSet_eq_fun hg (((hgs.add_const 1).add (hb.comp σ.measurable)).sub hb)
  obtain ⟨s, hsm, hsub, hnull, hinv⟩ := exists_invariant_conull_subset_equiv σ hσ hmeas heq
  refine ⟨s, hsm, hnull, hinv, ?_⟩
  intro x hx k
  have hxk : (σ.toEquiv ^ k) x ∈ s := by
    change x ∈ (σ.toEquiv ^ k) ⁻¹' s
    rwa [hinv k]
  have hrel := hsub hxk
  have hnext : (σ.toEquiv ^ (k + 1)) x = σ ((σ.toEquiv ^ k) x) := by
    rw [show k + 1 = 1 + k by omega, zpow_add, zpow_one, Equiv.Perm.mul_apply]
    rfl
  rw [hnext, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  change g ((σ.toEquiv ^ k) x) =
    gstar ((σ.toEquiv ^ k) x) + 1 + b (σ ((σ.toEquiv ^ k) x)) -
      b ((σ.toEquiv ^ k) x) at hrel
  linarith

theorem exists_invariant_weight_coboundary_domain (σ : X ≃ᵐ X)
    (hσ : MeasurePreserving σ μ μ) (g gstar b f fstar : X → ℝ)
    (hg : Measurable g) (hgs : Measurable gstar) (hb : Measurable b)
    (hmf : Measurable f) (hmfs : Measurable fstar)
    (heq : g =ᵐ[μ] fun x => gstar x + 1 + b (σ x) - b x)
    (hf : f =ᵐ[μ] fun x => Real.exp (-g x))
    (hfs : fstar =ᵐ[μ] fun x => Real.exp (-gstar x)) :
    ∃ s : Set X, MeasurableSet s ∧ μ sᶜ = 0 ∧
      (∀ n : ℤ, (σ.toEquiv ^ n) ⁻¹' s = s) ∧
      ∀ x ∈ s, ∀ k : ℤ,
        Real.exp (b ((σ.toEquiv ^ (k + 1)) x)) * f ((σ.toEquiv ^ k) x) =
          Real.exp (-1) * fstar ((σ.toEquiv ^ k) x) *
            Real.exp (b ((σ.toEquiv ^ k) x)) := by
  obtain ⟨s₀, hs₀, hn₀, hi₀, hscalar⟩ :=
    exists_invariant_exponential_coboundary_domain σ hσ g gstar b hg hgs hb heq
  have hm : MeasurableSet {x | f x = Real.exp (-g x) ∧
      fstar x = Real.exp (-gstar x)} :=
    (measurableSet_eq_fun hmf (Real.continuous_exp.measurable.comp hg.neg)).inter
      (measurableSet_eq_fun hmfs (Real.continuous_exp.measurable.comp hgs.neg))
  obtain ⟨t, htm, hsub, htn, hti⟩ :=
    exists_invariant_conull_subset_equiv σ hσ hm (hf.and hfs)
  refine ⟨s₀ ∩ t, hs₀.inter htm, ?_, ?_, ?_⟩
  · rw [Set.compl_inter]
    exact measure_union_null hn₀ htn
  · intro n
    rw [Set.preimage_inter, hi₀ n, hti n]
  · intro x hx k
    have hxk : (σ.toEquiv ^ k) x ∈ t := by
      change x ∈ (σ.toEquiv ^ k) ⁻¹' t
      rw [hti k]
      exact hx.2
    obtain ⟨hfx, hfsx⟩ := hsub hxk
    rw [hfx, hfsx]
    exact hscalar x hx.1 k

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TruncatedLogIntegral
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem lintegral_cost_eq_iSup_truncations (g : X → ℝ) (hm : Measurable g) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂μ) =
      ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (g x) (n : ℝ)) ∂μ := by
  have hsup (x : X) :
      (⨆ n : ℕ, ENNReal.ofReal (min (g x) (n : ℝ))) = ENNReal.ofReal (g x) := by
    apply le_antisymm
    · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · obtain ⟨n, hn⟩ := exists_nat_gt (g x)
      exact le_iSup_of_le n (by rw [min_eq_left hn.le])
  rw [← lintegral_iSup]
  · exact lintegral_congr (fun x => (hsup x).symm)
  · intro n
    exact (hm.min measurable_const).ennreal_ofReal
  · intro n m hnm x
    exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hnm))

theorem integrable_min_nat_cost [IsFiniteMeasure μ]
    (g : X → ℝ) (hm : Measurable g) (hg : ∀ x, 0 ≤ g x) (n : ℕ) :
    Integrable (fun x => min (g x) (n : ℝ)) μ := by
  refine (integrable_const (μ := μ) (n : ℝ)).mono'
    (hm.min measurable_const).aestronglyMeasurable ?_
  exact ae_of_all μ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hg x) (Nat.cast_nonneg n))]
    exact min_le_right _ _

theorem exists_integral_truncation_gt [IsFiniteMeasure μ]
    (g : X → ℝ) (hm : Measurable g) (hg : ∀ x, 0 ≤ g x)
    (hinf : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ∞) (A : ℝ) :
    ∃ n : ℕ, A < ∫ x, min (g x) (n : ℝ) ∂μ := by
  have hs : (⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (g x) (n : ℝ)) ∂μ) = ∞ := by
    rw [← lintegral_cost_eq_iSup_truncations g hm, hinf]
  have ht : ENNReal.ofReal A <
      ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (g x) (n : ℝ)) ∂μ := by
    rw [hs]
    exact ENNReal.ofReal_lt_top
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp ht
  refine ⟨n, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_min_nat_cost g hm hg n)
    (ae_of_all μ fun x => le_min (hg x) (Nat.cast_nonneg n))] at hn
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp hn).1

theorem log_max_exp_neg (g M : ℝ) :
    Real.log (max (Real.exp (-g)) (Real.exp (-M))) = -min g M := by
  rcases le_total g M with h | h
  · rw [max_eq_left (Real.exp_le_exp.mpr (neg_le_neg h)), Real.log_exp, min_eq_left h]
  · rw [max_eq_right (Real.exp_le_exp.mpr (neg_le_neg h)), Real.log_exp, min_eq_right h]

theorem integral_truncated_log_eq_neg_cost
    (f g : X → ℝ) (hfg : f =ᵐ[μ] fun x => Real.exp (-g x)) (M : ℝ) :
    (∫ x, Real.log (max (f x) (Real.exp (-M))) ∂μ) =
      -(∫ x, min (g x) M ∂μ) := by
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx, log_max_exp_neg]

theorem exists_truncated_log_integral_lt_of_cost [IsFiniteMeasure μ]
    (f g : X → ℝ) (hm : Measurable g) (hg : ∀ x, 0 ≤ g x)
    (hfg : f =ᵐ[μ] fun x => Real.exp (-g x))
    (hinf : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ∞) (A : ℝ) :
    ∃ n : ℕ, (∫ x, Real.log (max (f x) (Real.exp (-(n : ℝ)))) ∂μ) < -A := by
  obtain ⟨n, hn⟩ := exists_integral_truncation_gt g hm hg hinf A
  refine ⟨n, ?_⟩
  rw [integral_truncated_log_eq_neg_cost f g hfg]
  exact neg_lt_neg hn

theorem exists_truncated_log_integral_lt [IsFiniteMeasure μ]
    (f : X → ℝ) (hm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hpos : ∀ᵐ x ∂μ, 0 < f x)
    (hinf : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ) = ∞) (A : ℝ) :
    ∃ n : ℕ, (∫ x, Real.log (max (f x) (Real.exp (-(n : ℝ)))) ∂μ) < -A := by
  refine exists_truncated_log_integral_lt_of_cost f (fun x => -Real.log (f x))
    hm.log.neg (fun x => neg_nonneg.mpr (Real.log_nonpos (hf0 x) (hf1 x))) ?_ hinf A
  filter_upwards [hpos] with x hx
  simp [Real.exp_log hx]

theorem tendsto_integral_truncations_atTop [IsFiniteMeasure μ]
    (g : X → ℝ) (hm : Measurable g) (hg : ∀ x, 0 ≤ g x)
    (hinf : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ∞) :
    Tendsto (fun n : ℕ => ∫ x, min (g x) (n : ℝ) ∂μ) atTop atTop := by
  apply tendsto_atTop.2
  intro A
  obtain ⟨n, hn⟩ := exists_integral_truncation_gt g hm hg hinf A
  filter_upwards [eventually_ge_atTop n] with m hnm
  refine hn.le.trans (integral_mono (integrable_min_nat_cost g hm hg n)
    (integrable_min_nat_cost g hm hg m) ?_)
  intro x
  exact min_le_min (le_refl (g x)) (Nat.cast_le.mpr hnm)

theorem tendsto_truncated_log_integrals_atBot [IsFiniteMeasure μ]
    (f : X → ℝ) (hm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hpos : ∀ᵐ x ∂μ, 0 < f x)
    (hinf : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ) = ∞) :
    Tendsto (fun n : ℕ => ∫ x, Real.log (max (f x) (Real.exp (-(n : ℝ)))) ∂μ)
      atTop atBot := by
  have hfg : f =ᵐ[μ] fun x => Real.exp (-(-Real.log (f x))) := by
    filter_upwards [hpos] with x hx
    simp [Real.exp_log hx]
  have h := tendsto_neg_atTop_atBot.comp
    (tendsto_integral_truncations_atTop (fun x => -Real.log (f x)) hm.log.neg
      (fun x => neg_nonneg.mpr (Real.log_nonpos (hf0 x) (hf1 x))) hinf)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact integral_truncated_log_eq_neg_cost f (fun x => -Real.log (f x)) hfg (n : ℝ)

theorem exists_pos_truncated_log_integral_lt [IsFiniteMeasure μ]
    (f : X → ℝ) (hm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hpos : ∀ᵐ x ∂μ, 0 < f x)
    (hinf : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ) = ∞) (a : ℝ) :
    ∃ M : ℝ, 0 < M ∧
      (∫ x, Real.log (max (f x) (Real.exp (-M))) ∂μ) < -2 * a := by
  have hlim := tendsto_truncated_log_integrals_atBot f hm hf0 hf1 hpos hinf
  have hneg : ∀ᶠ n : ℕ in atTop,
      (∫ x, Real.log (max (f x) (Real.exp (-(n : ℝ)))) ∂μ) < -2 * a :=
    hlim.eventually (eventually_lt_atBot (-2 * a))
  obtain ⟨n, hn, hnint⟩ := ((eventually_gt_atTop (0 : ℕ)).and hneg).exists
  exact ⟨n, Nat.cast_pos.mpr hn, hnint⟩

theorem continuous_truncated_log {Y : Type*} [TopologicalSpace Y]
    (f : Y → ℝ) (hf : Continuous f) (M : ℝ) :
    Continuous (fun x => Real.log (max (f x) (Real.exp (-M)))) := by
  apply (hf.max continuous_const).log
  intro x
  exact ne_of_gt ((Real.exp_pos (-M)).trans_le (le_max_right _ _))

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_AnalyticWeightBridge
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem IsContinuousCircleWeight.ae_pos {f : Circle → ℝ}
    (hf : IsContinuousCircleWeight f) : ∀ᵐ x ∂circleMeasure, 0 < f x := by
  apply ae_pos_of_nonneg_singleton_zero f 0
  · simp only [circleMeasure_singleton]
  · exact fun x => (hf.2.1 x).1
  · exact hf.2.2.1

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleBackgroundBumps
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Invariant233.BackgroundCost

local instance circleBackgroundBumpsFactOnePos : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem circleMeasure_singleton (x : Circle) : circleMeasure {x} = 0 := by
  change volume ({x} : Set (AddCircle (1 : ℝ))) = 0
  rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
  norm_num

theorem exists_backgroundBumpData (θ : ℝ) (hθ : Irrational θ) :
    Nonempty (BackgroundBumpData θ) := by
  classical
  let : NullSingletonClass circleMeasure := ⟨circleMeasure_singleton⟩
  let : circleMeasure.OuterRegular := by
    change (volume : Measure (AddCircle (1 : ℝ))).OuterRegular
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hinfinite : ¬ IsOfFinAddOrder (θ : Circle) := by
    rw [AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div]
    rintro ⟨q, hq⟩
    exact hθ.ne_rat q (by simpa using hq.symm)
  have hinj : Function.Injective (fun n : ℕ => n • (θ : Circle)) :=
    injective_nsmul_iff_not_isOfFinAddOrder.2 hinfinite
  have hchoice (n : ℕ) := exists_bump_disjoint_images circleMeasure (0 : Circle)
    (fun (i : Fin (2 ^ (n + 2))) (x : Circle) => x + ((i : ℕ) + 1) • (θ : Circle))
    (fun i => isometry_add_right _) (by
      intro i j hij
      apply Fin.ext
      have he : (i : ℕ) + 1 = (j : ℕ) + 1 := hinj (by simpa using hij)
      omega)
    (R := 1 / ((n : ℝ) + 1)) (by positivity)
    (ε := (1 / 2 : ℝ≥0∞) ^ (n + 2) / (2 : ℝ≥0∞) ^ (n + 2))
    (ENNReal.div_pos (pow_ne_zero _ (by simp)) (by finiteness))
  choose r v hr hcap hμ hv hva hbounds hsupp hdisj using hchoice
  refine ⟨{
    radius := r
    bump := v
    radius_pos := hr
    radius_lt := hcap
    continuous_bump := hv
    bump_zero := hva
    bump_bounds := hbounds
    bump_support := hsupp
    disjoint_translates := hdisj
    weighted_support_bound := ?_ }⟩
  have hterm (n : ℕ) :
      (2 : ℝ≥0∞) ^ (n + 2) * circleMeasure (Metric.closedBall 0 (r n)) ≤
        (1 / 2 : ℝ≥0∞) ^ (n + 2) := by
    calc
      _ ≤ (2 : ℝ≥0∞) ^ (n + 2) *
          ((1 / 2 : ℝ≥0∞) ^ (n + 2) / (2 : ℝ≥0∞) ^ (n + 2)) :=
        mul_le_mul_right (hμ n).le _
      _ = _ := ENNReal.mul_div_cancel (by positivity) (by finiteness)
  calc
    _ ≤ ∑' n : ℕ, (1 / 2 : ℝ≥0∞) ^ (n + 2) := ENNReal.tsum_le_tsum hterm
    _ = 1 / 2 := by
      simp_rw [pow_add]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
      norm_num
      rw [pow_two, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]

end Invariant233.BackgroundCost

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleBackgroundCost
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
open InvariantProjection.Continuity

namespace Invariant233.BackgroundCost

local instance instNullSingletonClassCircleCircleMeasure_r251b68_1 : NullSingletonClass circleMeasure := ⟨circleMeasure_singleton⟩
local instance instFactLtRealOfNat_solutions_r251b68_1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance instIsFiniteMeasureCircleCircleMeasure_r251b68_1 : IsFiniteMeasure circleMeasure := by
  change IsFiniteMeasure (volume : Measure (AddCircle (1 : ℝ)))
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
theorem measurable_backgroundCost {θ : ℝ} (d : BackgroundBumpData θ) :
    Measurable (backgroundCost d) := by
  exact (measurable_const.add
    (Measurable.tsum (fun n => (d.continuous_bump n).measurable))).sub
    (Measurable.tsum (fun n => (continuous_backgroundNegative d n).measurable))

end Invariant233.BackgroundCost

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ContinuousWeightAssembly
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Function Set
open scoped ENNReal Topology

namespace Invariant233.CircleParameterLaws

open InvariantProjection.Continuity

variable {θ : ℝ} {p : CircleParameterData}

theorem measurable_rawBlock (j : ℕ) : Measurable (p.rawBlock θ j) := by
  have heq : p.rawBlock θ j = fun x => p.smoothBlock θ j x -
      p.smoothBlockTransfer θ j x + p.smoothBlockTransfer θ j (x + (θ : Circle)) := by
    funext x
    have h := smoothBlock_eq_add_coboundary (p := p) (θ := θ) j x
    linarith
  rw [heq]
  exact ((continuous_smoothBlock p θ j).measurable.sub
    (measurable_smoothBlockTransfer p θ j)).add
    ((measurable_smoothBlockTransfer p θ j).comp (measurable_id.add_const (θ : Circle)))

theorem measurable_rawCost : Measurable (p.rawCost θ) :=
  Measurable.tsum (fun n => measurable_rawBlock (n + 1))

theorem measurable_continuousCost (d : BackgroundBumpData θ) :
    Measurable (p.continuousCost θ d) :=
  (BackgroundCost.measurable_backgroundCost d).add
    (Measurable.tsum (fun n => (continuous_relocatedBlock (p := p) (θ := θ) (n + 1)).measurable))

variable (hp : CircleParameterLaws θ p)
include hp

omit hp in
theorem continuousWeight_ae_exp_neg (d : BackgroundBumpData θ) :
    p.continuousWeight θ d =ᵐ[circleMeasure] fun x => Real.exp (-p.continuousCost θ d x) := by
  have hne : ∀ᵐ x ∂circleMeasure, x ≠ (0 : Circle) := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using circleMeasure_singleton 0
  filter_upwards [hne] with x hx
  exact Function.update_of_ne hx _ _

theorem exists_continuousWeight_factor_domain (d : BackgroundBumpData θ)
    (fstar : Circle → ℝ) (hmfstar : Measurable fstar)
    (hfstar : fstar =ᵐ[circleMeasure] fun x => Real.exp (-p.rawCost θ x)) :
    ∃ s : Set Circle, MeasurableSet s ∧ circleMeasure sᶜ = 0 ∧
      (∀ n : ℤ, ((Equiv.addRight (θ : Circle)) ^ n) ⁻¹' s = s) ∧
      ∀ x ∈ s, ∀ k : ℤ,
        Real.exp (p.continuousTransfer θ d (((Equiv.addRight (θ : Circle)) ^ (k + 1)) x)) *
          p.continuousWeight θ d (((Equiv.addRight (θ : Circle)) ^ k) x) =
        Real.exp (-1) * fstar (((Equiv.addRight (θ : Circle)) ^ k) x) *
          Real.exp (p.continuousTransfer θ d (((Equiv.addRight (θ : Circle)) ^ k) x)) := by
  exact exists_invariant_weight_coboundary_domain (MeasurableEquiv.addRight (θ : Circle))
    (measurePreserving_add_right volume _) (p.continuousCost θ d) (p.rawCost θ)
    (p.continuousTransfer θ d) (p.continuousWeight θ d) fstar
    (measurable_continuousCost d) measurable_rawCost (measurable_continuousTransfer d)
    (hp.isContinuousCircleWeight_continuousWeight d).1.measurable hmfstar
    (hp.continuousCost_ae_coboundary d) (continuousWeight_ae_exp_neg d) hfstar

end Invariant233.CircleParameterLaws

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FiniteSupportWeights
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal

namespace Invariant233.FiniteSupportWeights

variable {X ι κ : Type*} [MeasurableSpace X]

theorem ae_mem_integerCore (μ : Measure X) (σ : ℤ → X → X) (s : Set X)
    (hσ : ∀ n, MeasurePreserving (σ n) μ μ) (hs : ∀ᵐ x ∂μ, x ∈ s) :
    ∀ᵐ x ∂μ, x ∈ integerCore σ s := by
  exact ae_all_iff.mpr fun n => (hσ n).quasiMeasurePreserving.ae hs

theorem measurableSet_integerCore (σ : ℤ → X → X) (s : Set X)
    (hσ : ∀ n, Measurable (σ n)) (hs : MeasurableSet s) :
    MeasurableSet (integerCore σ s) := by
  have heq : integerCore σ s = ⋂ n : ℤ, σ n ⁻¹' s := by
    ext x
    simp [integerCore]
  rw [heq]
  exact MeasurableSet.iInter fun n => hs.preimage (hσ n)

omit [MeasurableSpace X] in

theorem integerCore_subset (σ : ℤ → X → X) (s : Set X)
    (hzero : ∀ x, σ 0 x = x) : integerCore σ s ⊆ s := by
  intro x hx
  simpa only [hzero] using hx 0

omit [MeasurableSpace X] in

theorem mem_integerCore_translate_iff (σ : ℤ → X → X) (s : Set X)
    (hadd : ∀ m n x, σ (m + n) x = σ m (σ n x)) (n : ℤ) (x : X) :
    σ n x ∈ integerCore σ s ↔ x ∈ integerCore σ s := by
  constructor
  · intro hx m
    have hm := hx (m - n)
    simpa only [← hadd, sub_add_cancel] using hm
  · intro hx m
    simpa only [← hadd] using hx (m + n)

theorem uniform_nonzero_floor_of_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) {u | Int.floor (u + t) ≠ 0} =
      ENNReal.ofReal t := by
  have hmeas : MeasurableSet {u : ℝ | Int.floor (u + t) ≠ 0} :=
    (measurableSet_eq_fun (measurable_id.add_const t).floor measurable_const).compl
  rw [Measure.restrict_apply hmeas]
  have hset : {u : ℝ | Int.floor (u + t) ≠ 0} ∩ Set.Ico 0 1 =
      Set.Ico (1 - t) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ne_eq, Int.floor_eq_zero_iff,
      Set.mem_Ico]
    constructor
    · rintro ⟨hn, hu0, hu1⟩
      refine ⟨?_, hu1⟩
      by_contra h
      apply hn
      constructor <;> linarith
    · rintro ⟨hu0, hu1⟩
      refine ⟨?_, ?_, hu1⟩
      · intro h
        linarith [h.2]
      · linarith
  rw [hset, Real.volume_Ico]
  congr 1
  ring

theorem uniform_nonzero_floor_of_nonpos {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 0) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) {u | Int.floor (u + t) ≠ 0} =
      ENNReal.ofReal (-t) := by
  have hmeas : MeasurableSet {u : ℝ | Int.floor (u + t) ≠ 0} :=
    (measurableSet_eq_fun (measurable_id.add_const t).floor measurable_const).compl
  rw [Measure.restrict_apply hmeas]
  have hset : {u : ℝ | Int.floor (u + t) ≠ 0} ∩ Set.Ico 0 1 =
      Set.Ico 0 (-t) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ne_eq, Int.floor_eq_zero_iff,
      Set.mem_Ico]
    constructor
    · rintro ⟨hn, hu0, hu1⟩
      refine ⟨hu0, ?_⟩
      by_contra h
      apply hn
      constructor <;> linarith
    · rintro ⟨hu0, hu1⟩
      refine ⟨?_, hu0, ?_⟩
      · intro h
        linarith [h.1]
      · linarith
  rw [hset, Real.volume_Ico, sub_zero]

theorem uniform_nonzero_floor_le (t : ℝ) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) {u | Int.floor (u + t) ≠ 0} ≤
      ENNReal.ofReal |t| := by
  by_cases ht : |t| ≤ 1
  · have ht' := abs_le.mp ht
    rcases le_total 0 t with hpos | hneg
    · rw [uniform_nonzero_floor_of_nonneg hpos ht'.2, abs_of_nonneg hpos]
    · rw [uniform_nonzero_floor_of_nonpos ht'.1 hneg, abs_of_nonpos hneg]
  · calc
      _ ≤ (volume.restrict (Set.Ico (0 : ℝ) 1)) Set.univ := measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal |t| := ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_not_ge ht))

theorem measure_nonzero_floor_le (μ : Measure X) (u : X → ℝ)
    (hu : MeasurePreserving u μ (volume.restrict (Set.Ico (0 : ℝ) 1))) (t : ℝ) :
    μ {x | Int.floor (u x + t) ≠ 0} ≤ ENNReal.ofReal |t| := by
  have hmeas : MeasurableSet {v : ℝ | Int.floor (v + t) ≠ 0} :=
    (measurableSet_eq_fun (measurable_id.add_const t).floor measurable_const).compl
  change μ (u ⁻¹' {v : ℝ | Int.floor (v + t) ≠ 0}) ≤ _
  rw [hu.measure_preimage hmeas.nullMeasurableSet]
  exact uniform_nonzero_floor_le t

theorem measurableSet_finite_support {R : Type*} [MeasurableSpace R]
    [MeasurableSingletonClass R] [Zero R] [Countable ι]
    (a : ι → X → R) (ha : ∀ i, Measurable (a i)) :
    MeasurableSet {x | (Function.support (fun i => a i x)).Finite} := by
  classical
  have heq : {x | (Function.support (fun i => a i x)).Finite} =
      ⋃ s : Finset ι, ⋂ i : ι, ⋂ (_ : i ∉ s), {x | a i x = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · intro hx
      refine ⟨hx.toFinset, ?_⟩
      intro i hi
      by_contra hne
      exact hi (hx.mem_toFinset.mpr hne)
    · rintro ⟨s, hs⟩
      apply s.finite_toSet.subset
      intro i hi
      by_contra his
      exact hi (hs i his)
  rw [heq]
  refine MeasurableSet.iUnion fun s => MeasurableSet.iInter fun i =>
    MeasurableSet.iInter fun _ => ?_
  exact (ha i) (measurableSet_singleton 0)

theorem ae_finite_floor_support [Countable ι] (μ : Measure X) (u : ι → X → ℝ)
    (hu : ∀ i, MeasurePreserving (u i) μ (volume.restrict (Set.Ico (0 : ℝ) 1)))
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) (k : ℤ) :
    ∀ᵐ x ∂μ, (Function.support (fun i => Int.floor (u i x + (k : ℝ) * α i))).Finite := by
  have hs : Summable (fun i => |(k : ℝ)| * α i) := hα.mul_left _
  have hbound : (∑' i, μ {x | Int.floor (u i x + (k : ℝ) * α i) ≠ 0}) ≤
      ∑' i, ENNReal.ofReal (|(k : ℝ)| * α i) := by
    apply ENNReal.tsum_le_tsum
    intro i
    simpa only [abs_mul, abs_of_nonneg (hα0 i)] using
      measure_nonzero_floor_le μ (u i) (hu i) ((k : ℝ) * α i)
  exact ae_finite_setOfPred_mem (lt_of_le_of_lt hbound hs.tsum_ofReal_lt_top).ne

theorem ae_all_finite_floor_support [Countable ι] (μ : Measure X) (u : ι → X → ℝ)
    (hu : ∀ i, MeasurePreserving (u i) μ (volume.restrict (Set.Ico (0 : ℝ) 1)))
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) :
    ∀ᵐ x ∂μ, ∀ k : ℤ,
      (Function.support (fun i => Int.floor (u i x + (k : ℝ) * α i))).Finite := by
  exact ae_all_iff.mpr fun k => ae_finite_floor_support μ u hu α hα0 hα k

theorem exists_invariant_conull_floor_support [Countable ι]
    (μ : Measure X) (σ : ℤ → X → X)
    (hσ : ∀ n, MeasurePreserving (σ n) μ μ)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ m n x, σ (m + n) x = σ m (σ n x))
    (u : ι → X → ℝ)
    (hu : ∀ i, MeasurePreserving (u i) μ (volume.restrict (Set.Ico (0 : ℝ) 1)))
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) :
    ∃ s : Set X, MeasurableSet s ∧ (∀ᵐ x ∂μ, x ∈ s) ∧
      (∀ n x, σ n x ∈ s ↔ x ∈ s) ∧
      ∀ x ∈ s, ∀ k : ℤ,
        (Function.support (fun i => Int.floor (u i x + (k : ℝ) * α i))).Finite := by
  let a : ℤ → ι → X → ℤ := fun k i x => Int.floor (u i x + (k : ℝ) * α i)
  let s₀ : Set X := {x | ∀ k : ℤ, (Function.support (fun i => a k i x)).Finite}
  have hs₀ : MeasurableSet s₀ := by
    have heq : s₀ = ⋂ k : ℤ, {x | (Function.support (fun i => a k i x)).Finite} := by
      ext x
      simp [s₀]
    rw [heq]
    exact MeasurableSet.iInter fun k => measurableSet_finite_support (a k)
      (fun i => ((hu i).measurable.add_const _).floor)
  refine ⟨integerCore σ s₀,
    measurableSet_integerCore σ s₀ (fun n => (hσ n).measurable) hs₀, ?_, ?_, ?_⟩
  · exact ae_mem_integerCore μ σ s₀ hσ (ae_all_finite_floor_support μ u hu α hα0 hα)
  · exact mem_integerCore_translate_iff σ s₀ hadd
  · intro x hx
    exact integerCore_subset σ s₀ hzero hx

end Invariant233.FiniteSupportWeights

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleWeightSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.CircleWeightSupport

theorem exists_invariant_conull_floor_support {ι : Type*} [Countable ι]
    (θ : ℝ) (q : ι → ℤ) (hq : ∀ i, q i ≠ 0)
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) :
    ∃ s : Set UnitAddCircle, MeasurableSet s ∧ (∀ᵐ x ∂volume, x ∈ s) ∧
      (∀ (n : ℤ) x, x + n • (θ : UnitAddCircle) ∈ s ↔ x ∈ s) ∧
      ∀ x ∈ s, ∀ k : ℤ,
        (Function.support (fun i =>
          Int.floor (((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ) +
            (k : ℝ) * α i))).Finite := by
  apply FiniteSupportWeights.exists_invariant_conull_floor_support
    (volume : Measure UnitAddCircle) (fun n x => x + n • (θ : UnitAddCircle))
    (fun n => measurePreserving_add_right volume (n • (θ : UnitAddCircle)))
    (by intro x; simp)
    (by intro m n x; simp [add_zsmul, add_comm, add_left_comm])
    (fun i x => ((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ))
    (fun i => measurePreserving_characterRepresentative (q i) (hq i)) α hα0 hα

end Invariant233.CircleWeightSupport

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

end Invariant233.FiniteSupportCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function

namespace Invariant233.CircleWeights

variable {ι : Type*}

theorem coordinate_rotate (θ : ℝ) (q : ι → ℤ) (i : ι)
    (k : ℤ) (x : UnitAddCircle) :
    coordinate q i (rotate θ k x) =
      Int.fract (coordinate q i x + (k : ℝ) * phase θ q i) := by
  exact CircleCharacterDynamics.character_orbit_representative (q i) k θ x

theorem exists_cocycle_set [Countable ι]
    (θ : ℝ) (q : ι → ℤ) (hq : ∀ i, q i ≠ 0) (c : ι → ℝ)
    (hphase : Summable (phase θ q)) :
    ∃ s : Set UnitAddCircle, MeasurableSet s ∧ (∀ᵐ x ∂volume, x ∈ s) ∧
      (∀ (k : ℤ) x, rotate θ k x ∈ s ↔ x ∈ s) ∧
      (∀ x ∈ s, ∀ k : ℤ,
        HasFiniteSupport (fun i => Int.floor (coordinate q i x + (k : ℝ) * phase θ q i))) ∧
      (∀ x ∈ s, ∀ k n : ℤ,
        cocycle θ q c (k + n) x =
          cocycle θ q c n (rotate θ k x) * cocycle θ q c k x) := by
  obtain ⟨s, hs, hfull, hinv, hfinite⟩ :=
    CircleWeightSupport.exists_invariant_conull_floor_support θ q hq
      (phase θ q) (phase_nonneg θ q) hphase
  refine ⟨s, hs, hfull, hinv, hfinite, ?_⟩
  intro x hx k n
  have hk : HasFiniteSupport
      (fun i => Int.floor (coordinate q i x + (k : ℝ) * phase θ q i)) := hfinite x hx k
  have hn : HasFiniteSupport (fun i =>
      Int.floor (Int.fract (coordinate q i x + (k : ℝ) * phase θ q i) +
        (n : ℝ) * phase θ q i)) := by
    have h := hfinite (rotate θ k x) ((hinv k x).mpr hx) n
    change HasFiniteSupport (fun i =>
      Int.floor (coordinate q i (rotate θ k x) + (n : ℝ) * phase θ q i)) at h
    simpa only [coordinate_rotate] using h
  simpa only [cocycle, floorCost, coordinate_rotate] using
    FiniteSupportCocycle.exp_tsum_floor_cocycle
      (fun i => coordinate q i x) (phase θ q) c k n hk hn

end Invariant233.CircleWeights

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ParameterCircleCocycle
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function
open scoped BigOperators ENNReal

namespace Invariant233

namespace CircleParameterData

theorem coord_phase_eq (p : CircleParameterData) (θ : ℝ) (i : p.Coord) :
    CircleWeights.phase θ p.coordFrequency i = p.alpha θ i.2 := by
  simp only [CircleWeights.phase, coordFrequency, alpha, Int.cast_natCast]

theorem coord_coordinate_eq (p : CircleParameterData) (i : p.Coord) (x : Circle) :
    CircleWeights.coordinate p.coordFrequency i x = p.coordinate i.2 x := by
  simp only [CircleWeights.coordinate, CircleWeights.representative,
    coordFrequency, coordinate, rep, natCast_zsmul]

theorem floorCocycle_eq_block_sum (p : CircleParameterData) (θ : ℝ) (k : ℤ)
    (x : Circle) (hx : HasFiniteSupport (fun i : p.Coord =>
      Int.floor (p.coordinate i.2 x + (k : ℝ) * p.alpha θ i.2))) :
    p.floorCocycle θ k x = Real.exp (-(∑' j : ℕ, p.C (j + 1) *
      ∑ i ∈ p.block (j + 1),
        (Int.floor (p.coordinate i x + (k : ℝ) * p.alpha θ i) : ℝ))) := by
  unfold floorCocycle CircleWeights.cocycle CircleWeights.floorCost
  simp_rw [p.coord_phase_eq, p.coord_coordinate_eq]
  congr 2
  rw [(FiniteSupportCocycle.summable_weighted_int p.coordCost hx).tsum_sigma]
  apply tsum_congr
  intro j
  simp only [coordCost, tsum_fintype]
  rw [Finset.mul_sum]
  exact Finset.sum_attach (p.block (j + 1))
    (fun i => p.C (j + 1) *
      (Int.floor (p.coordinate i x + (k : ℝ) * p.alpha θ i) : ℝ))

end CircleParameterData

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem summable_coord_phases : Summable (CircleWeights.phase θ p.coordFrequency) := by
  rw [show CircleWeights.phase θ p.coordFrequency =
    (fun i : p.Coord => p.alpha θ i.2) from funext (p.coord_phase_eq θ)]
  apply (summable_sigma_of_nonneg (fun i => Int.fract_nonneg _)).mpr
  constructor
  · intro j
    exact (hasSum_fintype _).summable
  · apply hp.summable_block_phases.congr
    intro j
    simp only [tsum_fintype]
    exact (Finset.sum_attach (p.block (j + 1)) (p.alpha θ)).symm

theorem exists_parameter_cocycle_set :
    ∃ s : Set Circle, MeasurableSet s ∧ (∀ᵐ x ∂circleMeasure, x ∈ s) ∧
      (∀ (k : ℤ) x, CircleWeights.rotate θ k x ∈ s ↔ x ∈ s) ∧
      (∀ x ∈ s, ∀ k : ℤ,
        HasFiniteSupport (fun i : p.Coord =>
          Int.floor (p.coordinate i.2 x + (k : ℝ) * p.alpha θ i.2))) ∧
      (∀ x ∈ s, ∀ k n : ℤ,
        p.floorCocycle θ (k + n) x =
          p.floorCocycle θ n (CircleWeights.rotate θ k x) * p.floorCocycle θ k x) := by
  simpa only [circleMeasure, CircleParameterData.floorCocycle,
    p.coord_phase_eq, p.coord_coordinate_eq] using
    CircleWeights.exists_cocycle_set θ p.coordFrequency hp.coordFrequency_ne_zero
      p.coordCost hp.summable_coord_phases

end CircleParameterLaws
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ContinuousWeightParameterBridge
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem measurableWeight_ae_exp_neg_rawCost :
    p.measurableWeight θ =ᵐ[circleMeasure] fun x => Real.exp (-p.rawCost θ x) := by
  obtain ⟨s, hs, hfull, hinv, hfinite, hcoc⟩ := hp.exists_parameter_cocycle_set
  filter_upwards [hfull] with x hx
  have h := p.floorCocycle_eq_block_sum θ 1 x (hfinite x hx 1)
  change p.floorCocycle θ 1 x = _
  simpa only [Int.cast_one, one_mul, Finset.mul_sum,
    CircleParameterData.rawCost, CircleParameterData.rawBlock] using h

theorem exists_continuousWeight_parameter_factor_domain (d : BackgroundBumpData θ) :
    ∃ s : Set Circle, MeasurableSet s ∧ circleMeasure sᶜ = 0 ∧
      (∀ n : ℤ, ((Equiv.addRight (θ : Circle)) ^ n) ⁻¹' s = s) ∧
      ∀ x ∈ s, ∀ k : ℤ,
        Real.exp (p.continuousTransfer θ d (((Equiv.addRight (θ : Circle)) ^ (k + 1)) x)) *
          p.continuousWeight θ d (((Equiv.addRight (θ : Circle)) ^ k) x) =
        Real.exp (-1) * p.measurableWeight θ (((Equiv.addRight (θ : Circle)) ^ k) x) *
          Real.exp (p.continuousTransfer θ d (((Equiv.addRight (θ : Circle)) ^ k) x)) :=
  hp.exists_continuousWeight_factor_domain d (p.measurableWeight θ)
    hp.measurable_parameter_weight hp.measurableWeight_ae_exp_neg_rawCost

end Invariant233.CircleParameterLaws

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

theorem operator_pow_apply (w : Weight) (n : ℕ) (ξ : Hilbert) (k : ℤ) :
    (((operator w)^n) ξ) k =
      (∏ j ∈ Finset.range n, w (k - n + j)) * ξ (k - n) := by
  simpa using operator_pow_apply_add w n ξ (k - n)

theorem norm_operator_pow_le (w : Weight) (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hprod : ∀ k : ℤ, ‖∏ j ∈ Finset.range n, w (k + j)‖ ≤ B) :
    ‖(operator w)^n‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro ξ
  calc
    ‖((operator w)^n) ξ‖ ≤ ‖B • shift (n : ℤ) ξ‖ := by
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro k
      simp only [operator_pow_apply, norm_mul, lp.coeFn_smul, Pi.smul_apply,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hB, shift_apply]
      exact mul_le_mul_of_nonneg_right (hprod (k - n)) (norm_nonneg _)
    _ = B * ‖ξ‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hB,
      (shift (n : ℤ)).norm_map]

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
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

theorem norm_fieldDiagonal_le : ‖fieldDiagonal a C hC ha hm‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

variable {a C hC ha hm}

theorem fieldShift_ae (m : ℤ) (f : Lp Hilbert 2 μ) :
    (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f =ᵐ[μ]
      fun x => shift m (f x) :=
  ContinuousLinearMap.coeFn_compLp _ f

theorem fieldShift_add (m n : ℤ) :
    (shift (m + n)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ =
      (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ *
        (shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ := by
  ext f
  filter_upwards [fieldShift_ae (m + n) f,
    fieldShift_ae m ((shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f),
    fieldShift_ae n f] with x hmn hm hn
  change ((shift (m + n)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x =
    ((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
      ((shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f)) x
  rw [hmn, hm, hn]
  exact congrArg (fun A : Hilbert →L[ℂ] Hilbert => A (f x)) (shift_add m n)

theorem fieldShift_zero :
    (shift 0).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ = 1 := by
  ext f
  filter_upwards [fieldShift_ae 0 f] with x hx
  change ((shift 0).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x = f x
  rw [hx]
  change (shift 0).toLinearIsometry.toContinuousLinearMap (f x) = f x
  rw [shift_zero]
  rfl

theorem fieldShift_norm_map (m : ℤ) (f : Lp Hilbert 2 μ) :
    ‖(shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f‖ = ‖f‖ := by
  have hnorm : ∀ᵐ x ∂μ,
      ‖((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x‖ = ‖f x‖ := by
    filter_upwards [fieldShift_ae m f] with x hx
    rw [hx, (shift m).norm_map]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.symm.le))

theorem fieldShift_mem_unitary (m : ℤ) :
    (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ ∈
      unitary (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) := by
  let A := (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
  let B := (shift (-m)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
  have hAB : A * B = 1 := by
    dsimp [A, B]
    rw [← fieldShift_add]
    simpa using (fieldShift_zero (μ := μ))
  have hBA : B * A = 1 := by
    dsimp [A, B]
    rw [← fieldShift_add]
    simpa using (fieldShift_zero (μ := μ))
  have hA : IsUnit A := ⟨⟨A, B, hAB, hBA⟩, rfl⟩
  apply hA.mem_unitary_iff_star_mul_self.mpr
  change ContinuousLinearMap.adjoint A ∘L A = 1
  exact A.norm_map_iff_adjoint_comp_self.mp (fieldShift_norm_map m)

theorem fieldDiagonal_norm_map
    (hunit : ∀ᵐ x ∂μ, ∀ k, ‖a x k‖ = 1) (f : Lp Hilbert 2 μ) :
    ‖fieldDiagonal a C hC ha hm f‖ = ‖f‖ := by
  have hnorm : ∀ᵐ x ∂μ, ‖fieldDiagonal a C hC ha hm f x‖ = ‖f x‖ := by
    filter_upwards [fieldDiagonal_coordinate_ae a C hC ha hm f, hunit] with x hx hu
    have hcoord : ∀ k, ‖fieldDiagonal a C hC ha hm f x k‖ = ‖f x k‖ := by
      intro k
      rw [hx, norm_mul, hu, one_mul]
    exact le_antisymm (lp.norm_mono (by norm_num) fun k => (hcoord k).le)
      (lp.norm_mono (by norm_num) fun k => (hcoord k).symm.le)
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.symm.le))

theorem fieldDiagonal_mem_unitary
    (hunit : ∀ᵐ x ∂μ, ∀ k, ‖a x k‖ = 1) :
    fieldDiagonal a C hC ha hm ∈ unitary (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) := by
  have hb : ∀ x, ‖star (a x)‖ ≤ C := by simpa using ha
  have hn : ∀ k, AEStronglyMeasurable (fun x => star (a x) k) μ := by
    intro k
    simpa only [lp.coeFn_star, Pi.star_apply] using
      continuous_star.comp_aestronglyMeasurable (hm k)
  have hstar : fieldDiagonal (fun x => star (a x)) C hC hb hn =
      star (fieldDiagonal a C hC ha hm) :=
    fieldDiagonal_star_of_eq (Filter.Eventually.of_forall fun _ => rfl)
  have hunitstar : ∀ᵐ x ∂μ, ∀ k, ‖star (a x) k‖ = 1 := by
    simpa only [lp.coeFn_star, Pi.star_apply, norm_star] using hunit
  apply Unitary.mem_iff.mpr
  constructor
  · change ContinuousLinearMap.adjoint (fieldDiagonal a C hC ha hm) ∘L
      fieldDiagonal a C hC ha hm = 1
    exact ContinuousLinearMap.norm_map_iff_adjoint_comp_self _ |>.mp
      (fieldDiagonal_norm_map hunit)
  · have hh := ContinuousLinearMap.norm_map_iff_adjoint_comp_self
      (star (fieldDiagonal a C hC ha hm)) |>.mp (fun f => by
        rw [← hstar]
        exact fieldDiagonal_norm_map hunitstar f)
    change star (star (fieldDiagonal a C hC ha hm)) *
      star (fieldDiagonal a C hC ha hm) = 1 at hh
    simpa only [star_star] using hh

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ContinuousCircleImage
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set

namespace Invariant233.ContinuousCircleImage

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fourier_natCast (n : ℕ) :
    (fourier (n : ℤ) : C(AddCircle (1 : ℝ), ℂ)) = fourier 1 ^ n := by
  induction n with
  | zero =>
    ext x
    simp only [Nat.cast_zero, pow_zero, ContinuousMap.one_apply]
    exact fourier_zero
  | succ n ih =>
    ext x
    rw [Nat.cast_succ]
    change fourier ((n : ℤ) + 1) x = (fourier 1 ^ (n + 1)) x
    rw [fourier_add, pow_succ, ContinuousMap.mul_apply, ← ih]

theorem isClosed_vonNeumannAlgebra (M : VonNeumannAlgebra H) :
    IsClosed (M : Set (H →L[ℂ] H)) := by
  rw [← M.centralizer_centralizer]
  exact Set.isClosed_centralizer _

theorem image_mem
    (Φ : C(AddCircle (1 : ℝ), ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (hΦ : Continuous Φ)
    (M : VonNeumannAlgebra H) (hV : Φ (fourier 1) ∈ M)
    (f : C(AddCircle (1 : ℝ), ℂ)) : Φ f ∈ M := by
  have hNat : ∀ n : ℕ, Φ (fourier (n : ℤ)) ∈ M := by
    intro n
    rw [fourier_natCast, map_pow]
    exact pow_mem hV n
  have hFourier : ∀ n : ℤ, Φ (fourier n) ∈ M := by
    intro n
    cases n with
    | ofNat n => exact hNat n
    | negSucc n =>
      have heq : (fourier (Int.negSucc n) : C(AddCircle (1 : ℝ), ℂ)) =
          star (fourier ((n + 1 : ℕ) : ℤ)) := by
        ext x
        change fourier (-((n + 1 : ℕ) : ℤ)) x = star (fourier ((n + 1 : ℕ) : ℤ) x)
        exact fourier_neg
      rw [heq, map_star]
      exact star_mem (hNat (n + 1))
  let K : Submodule ℂ C(AddCircle (1 : ℝ), ℂ) :=
    M.toStarSubalgebra.toSubalgebra.toSubmodule.comap Φ.toAlgHom.toLinearMap
  have hK : IsClosed (K : Set C(AddCircle (1 : ℝ), ℂ)) :=
    (isClosed_vonNeumannAlgebra M).preimage hΦ
  have hspan : Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact hFourier n
  have hclosure := (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure_minimal hspan hK
  rw [span_fourier_closure_eq_top] at hclosure
  exact hclosure (Submodule.mem_top : f ∈ (⊤ : Submodule ℂ C(AddCircle (1 : ℝ), ℂ)))

end Invariant233.ContinuousCircleImage

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_Rotation
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.Rotation

theorem representation_norm_le (θ : ℝ) (a : C(Circle, ℂ)) :
    ‖representation θ a‖ ≤ ‖a‖ := by
  unfold representation
  exact WeightedShift.norm_fieldDiagonal_le _ _ _ _ _

theorem representation_continuous (θ : ℝ) : Continuous (representation θ) := by
  let L := (representationStarAlgHom θ).toAlgHom.toLinearMap
  have hL : ∀ a : C(Circle, ℂ), ‖L a‖ ≤ (1 : ℝ) * ‖a‖ := by
    intro a
    change ‖representation θ a‖ ≤ (1 : ℝ) * ‖a‖
    simpa only [one_mul] using representation_norm_le θ a
  exact (L.mkContinuous 1 hL).continuous

theorem U_mem_unitary : U ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  WeightedShift.fieldShift_mem_unitary 1

theorem V_mem_unitary (θ : ℝ) : V θ ∈ unitary (Hilbert →L[ℂ] Hilbert) := by
  unfold V representation
  apply WeightedShift.fieldDiagonal_mem_unitary
  exact Filter.Eventually.of_forall fun x k => character_norm (action θ k x)

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationAlgebra
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.Rotation

theorem U_mem_algebra (θ : ℝ) : U ∈ algebra θ :=
  subset_vonNeumannGenerated _ (Set.mem_insert U _)

theorem V_mem_algebra (θ : ℝ) : V θ ∈ algebra θ :=
  subset_vonNeumannGenerated _ (Set.mem_insert_of_mem U (Set.mem_singleton _))

theorem representation_mem_algebra (θ : ℝ) (a : C(Circle, ℂ)) :
    representation θ a ∈ algebra θ :=
  ContinuousCircleImage.image_mem (representationStarAlgHom θ) (representation_continuous θ)
    (algebra θ) (V_mem_algebra θ) a

theorem weighted_mem_algebra (θ : ℝ) (a : C(Circle, ℂ)) :
    weighted θ a ∈ algebra θ :=
  mul_mem (U_mem_algebra θ) (representation_mem_algebra θ a)

theorem weightedReal_mem_algebra (θ : ℝ) (f : C(Circle, ℝ)) :
    weightedReal θ f ∈ algebra θ :=
  weighted_mem_algebra θ (complexWeight f)

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldUnboundedMultiplier
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem field_multiplier_intertwines
    (h f g : X → ℤ → ℂ) (c : ℂ)
    (A B : FieldHilbert μ →L[ℂ] FieldHilbert μ)
    (hA : ∀ ξ, ∀ᵐ x ∂μ, ∀ k, A ξ x k = f x (k - 1) * ξ x (k - 1))
    (hB : ∀ ξ, ∀ᵐ x ∂μ, ∀ k, B ξ x k = g x (k - 1) * ξ x (k - 1))
    (hfg : ∀ᵐ x ∂μ, ∀ k, h x (k + 1) * f x k = c * g x k * h x k)
    (ξ : (fieldUnboundedMultiplier μ h).domain) :
    fieldUnboundedMultiplier μ h
      ⟨A ξ.val, field_operator_mem_multiplierDomain h f g c A B hA hB hfg ξ⟩ =
        c • B (fieldUnboundedMultiplier μ h ξ) := by
  apply fieldUnboundedMultiplier_eq_of_ae
  filter_upwards [hA ξ.val, hB (fieldUnboundedMultiplier μ h ξ),
    fieldUnboundedMultiplier_apply_ae h ξ, hfg,
    Lp.coeFn_smul c (B (fieldUnboundedMultiplier μ h ξ))]
    with x hA hB hH hfg hsmul
  intro k
  rw [hsmul]
  change c * B (fieldUnboundedMultiplier μ h ξ) x k = h x k * A ξ.val x k
  rw [hA, hB, hH]
  have hk := hfg (k - 1)
  simp only [sub_add_cancel] at hk
  rw [← mul_assoc (h x k), hk]
  ring

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationTransferIntertwining
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Invariant233.Rotation

theorem exponentialTransfer_weightedReal
    (θ : ℝ) (b : Circle → ℝ) (f : C(Circle, ℝ))
    (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) (c : ℂ)
    (hfactor : ∀ᵐ x ∂circleMeasure,
      (Real.exp (b (x + (θ : Circle))) : ℂ) * (f x : ℂ) =
        c * g x * (Real.exp (b x) : ℂ))
    (ξ : (exponentialTransfer θ b).domain) :
    exponentialTransfer θ b
      ⟨weightedReal θ f ξ.val,
        weightedReal_mem_exponentialTransfer_domain θ b f g C hC hg hb c hfactor ξ⟩ =
      c • (U * measurableRepresentation θ g C hC hg hb) (exponentialTransfer θ b ξ) := by
  exact WeightedShift.field_multiplier_intertwines
    (fun x k => (Real.exp (b (action θ k x)) : ℂ))
    (fun x k => ((f (action θ k x)) : ℂ))
    (fun x k => g (action θ k x)) c
    (weightedReal θ f) (U * measurableRepresentation θ g C hC hg hb)
    (weighted_coordinates_ae θ (complexWeight f))
    (U_mul_measurableRepresentation_coordinates_ae θ g C hC hg hb)
    (ae_all_action_factor θ b (fun x => (f x : ℂ)) g c hfactor) ξ

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ContinuousWeightOperatorBridge
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem continuousWeight_parameter_factor_ae (d : BackgroundBumpData θ) :
    ∀ᵐ x ∂circleMeasure,
      (Real.exp (p.continuousTransfer θ d (x + (θ : Circle))) : ℂ) *
        (p.continuousWeight θ d x : ℂ) =
      (Real.exp (-1) : ℂ) * (p.measurableWeight θ x : ℂ) *
        (Real.exp (p.continuousTransfer θ d x) : ℂ) := by
  obtain ⟨s, _hs, hfull, _hinv, hfactor⟩ :=
    hp.exists_continuousWeight_parameter_factor_domain d
  have hae : ∀ᵐ x ∂circleMeasure, x ∈ s := ae_iff.mpr hfull
  filter_upwards [hae] with x hx
  have hreal := hfactor x hx (0 : ℤ)
  simp only [zero_add, zpow_one, zpow_zero, Equiv.Perm.one_apply, Equiv.coe_addRight] at hreal
  exact_mod_cast hreal

theorem continuousWeight_natural_intertwining (d : BackgroundBumpData θ) :
    let f : C(Circle, ℝ) :=
      ⟨p.continuousWeight θ d, (hp.isContinuousCircleWeight_continuousWeight d).1⟩
    let H := Rotation.exponentialTransfer θ (p.continuousTransfer θ d)
    let Tstar := Rotation.U * Rotation.measurableRepresentation θ
      (fun x => (p.measurableWeight θ x : ℂ)) 1 zero_le_one
      hp.measurable_complexParameterWeight hp.norm_complexParameterWeight_le_one
    ∀ ξ : H.domain, ∃ hD : Rotation.weightedReal θ f ξ.val ∈ H.domain,
      H ⟨Rotation.weightedReal θ f ξ.val, hD⟩ =
        (Real.exp (-1) : ℂ) • Tstar (H ξ) := by
  dsimp only
  intro ξ
  let f : C(Circle, ℝ) :=
    ⟨p.continuousWeight θ d, (hp.isContinuousCircleWeight_continuousWeight d).1⟩
  refine ⟨Rotation.weightedReal_mem_exponentialTransfer_domain θ
    (p.continuousTransfer θ d) f (fun x => (p.measurableWeight θ x : ℂ)) 1
    zero_le_one hp.measurable_complexParameterWeight hp.norm_complexParameterWeight_le_one
    (Real.exp (-1) : ℂ) (hp.continuousWeight_parameter_factor_ae d) ξ, ?_⟩
  exact Rotation.exponentialTransfer_weightedReal θ (p.continuousTransfer θ d) f
    (fun x => (p.measurableWeight θ x : ℂ)) 1 zero_le_one
    hp.measurable_complexParameterWeight hp.norm_complexParameterWeight_le_one
    (Real.exp (-1) : ℂ) (hp.continuousWeight_parameter_factor_ae d) ξ

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_HilbertModelSize
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.HilbertModelSize

open TopologicalSpace MeasureTheory
open scoped lp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem not_finiteDimensional_of_infinite_orthonormal {ι : Type*} [Infinite ι]
    {v : ι → E} (hv : Orthonormal ℂ v) : ¬ FiniteDimensional ℂ E := by
  intro h
  let := h
  have : Finite ι := hv.linearIndependent.finite
  exact not_finite ι

theorem not_finiteDimensional_l2 (ι : Type*) [Infinite ι] :
    ¬ FiniteDimensional ℂ (ℓ²(ι, ℂ)) :=
  not_finiteDimensional_of_infinite_orthonormal
    (default : HilbertBasis ι ℂ (ℓ²(ι, ℂ))).orthonormal

section BochnerLp

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem not_finiteDimensional_L2 (hE : ¬ FiniteDimensional ℂ E) :
    ¬ FiniteDimensional ℂ (Lp E 2 μ) := by
  intro h
  let := h
  exact hE (FiniteDimensional.of_injective (constL2Isometry μ).toLinearMap
    (constL2Isometry μ).injective)

theorem not_finiteDimensional_L2_l2 (ι : Type*) [Infinite ι] :
    ¬ FiniteDimensional ℂ (Lp (ℓ²(ι, ℂ)) 2 μ) :=
  not_finiteDimensional_L2 μ (not_finiteDimensional_l2 ι)

end BochnerLp

theorem circleMeasure_isProbabilityMeasure : IsProbabilityMeasure circleMeasure := by
  constructor
  change (volume : Measure Circle) Set.univ = 1
  simp [AddCircle.measure_univ]

theorem circle_representation_not_finiteDimensional :
    ¬ FiniteDimensional ℂ (Lp (ℓ²(ℤ, ℂ)) 2 circleMeasure) := by
  let := circleMeasure_isProbabilityMeasure
  exact not_finiteDimensional_L2_l2 circleMeasure ℤ

end Invariant233.HilbertModelSize

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldCovariance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace Invariant233.FieldTraceCyclic

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in

theorem commute_shiftedPullback_of_covariance
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (S : E →L[ℂ] E) (σ : Ω → Ω) (hσ : MeasurePreserving σ μ μ)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hcov : ∀ᵐ x ∂μ, A x * S = S * A (σ x)) :
    Commute T (DirectIntegral.shiftedPullback S σ hσ) := by
  change T * DirectIntegral.shiftedPullback S σ hσ =
    DirectIntegral.shiftedPullback S σ hσ * T
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [hT (DirectIntegral.shiftedPullback S σ hσ ξ),
    shiftedPullback_ae S σ hσ ξ, shiftedPullback_ae S σ hσ (T ξ),
    hσ.quasiMeasurePreserving.ae (hT ξ), hcov] with x hTx hJx hJTx hTσx hcovx
  change (T (DirectIntegral.shiftedPullback S σ hσ ξ)) x =
    (DirectIntegral.shiftedPullback S σ hσ (T ξ)) x
  rw [hTx, hJx, hJTx, hTσx]
  exact congrArg (fun R : E →L[ℂ] E => R (ξ (σ x))) hcovx

end Invariant233.FieldTraceCyclic

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationFields
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

theorem commute_star_left_of_mem_unitary {A B : Hilbert →L[ℂ] Hilbert}
    (hA : A ∈ unitary (Hilbert →L[ℂ] Hilbert)) (hAB : Commute A B) :
    Commute (star A) B := by
  obtain ⟨h₁, h₂⟩ := Unitary.mem_iff.mp hA
  show star A * B = B * star A
  calc
    star A * B = star A * (B * (A * star A)) := by rw [h₂, mul_one]
    _ = star A * ((A * B) * star A) := by rw [← mul_assoc B A, ← hAB.eq]
    _ = (star A * A) * (B * star A) := by simp only [mul_assoc]
    _ = B * star A := by rw [h₁, one_mul]

theorem U_commutes_multiplier (g : Lp ℂ ∞ circleMeasure) :
    Commute U (L2Multiplication.multiplier (E := Fiber) g) := by
  show U * L2Multiplication.multiplier g = L2Multiplication.multiplier g * U
  apply operator_ext_of_coordinates
  intro ξ
  filter_upwards [U_coordinates_ae (L2Multiplication.multiplier g ξ),
    L2Multiplication.multiplier_coe g ξ, L2Multiplication.multiplier_coe g (U ξ),
    U_coordinates_ae ξ] with x hU hM hMU hUξ
  intro k
  change U (L2Multiplication.multiplier g ξ) x k =
    L2Multiplication.multiplier g (U ξ) x k
  rw [hU k, hM, hMU]
  change g x * ξ x (k - 1) = g x * U ξ x k
  rw [hUξ k]

theorem representation_commutes_multiplier (θ : ℝ) (a : C(Circle, ℂ))
    (g : Lp ℂ ∞ circleMeasure) :
    Commute (representation θ a) (L2Multiplication.multiplier (E := Fiber) g) := by
  show representation θ a * L2Multiplication.multiplier g =
    L2Multiplication.multiplier g * representation θ a
  apply operator_ext_of_coordinates
  intro ξ
  filter_upwards [representation_coordinates_ae θ a (L2Multiplication.multiplier g ξ),
    L2Multiplication.multiplier_coe g ξ,
    L2Multiplication.multiplier_coe g (representation θ a ξ),
    representation_coordinates_ae θ a ξ] with x ha hM hMa haξ
  intro k
  change representation θ a (L2Multiplication.multiplier g ξ) x k =
    L2Multiplication.multiplier g (representation θ a ξ) x k
  rw [ha k, hM, hMa]
  change a (action θ k x) * (g x * ξ x k) =
    g x * representation θ a ξ x k
  rw [haξ k]
  ring

theorem multiplier_mem_commutant (θ : ℝ) (g : Lp ℂ ∞ circleMeasure) :
    L2Multiplication.multiplier (E := Fiber) g ∈ (algebra θ).commutant := by
  apply (mem_commutant_vonNeumannGenerated_iff _ _).mpr
  intro A hA
  rcases Set.mem_insert_iff.mp hA with rfl | hA
  · exact ⟨(U_commutes_multiplier g).eq,
      (commute_star_left_of_mem_unitary U_mem_unitary (U_commutes_multiplier g)).eq⟩
  · have hAV : A = V θ := Set.mem_singleton_iff.mp hA
    subst A
    have hcomm := representation_commutes_multiplier θ character g
    exact ⟨hcomm.eq,
      (commute_star_left_of_mem_unitary (V_mem_unitary θ) hcomm).eq⟩

theorem algebra_commutes_multiplier (θ : ℝ) {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ algebra θ) (g : Lp ℂ ∞ circleMeasure) :
    Commute T (L2Multiplication.multiplier (E := Fiber) g) := by
  exact (VonNeumannAlgebra.mem_commutant_iff.mp (multiplier_mem_commutant θ g)) T hT

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationFieldRepresentation
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.Rotation

theorem exists_unique_field {θ : ℝ} {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ algebra θ) :
    ∃ F : Circle → Fiber →L[ℂ] Fiber,
      (∀ x, ‖F x‖ ≤ ‖T‖) ∧
      (∀ v : Fiber, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Hilbert, T ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      (∀ G : Circle → Fiber →L[ℂ] Fiber,
        (∀ ξ : Hilbert, T ξ =ᵐ[circleMeasure] fun x => G x (ξ x)) →
          F =ᵐ[circleMeasure] G) :=
  L2Multiplication.exists_unique_field_of_commutes
    (default : HilbertBasis ℤ ℂ Fiber) T (algebra_commutes_multiplier θ hT)

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationHilbert
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.Rotation

theorem hilbert_not_finiteDimensional : ¬ FiniteDimensional ℂ Hilbert :=
  HilbertModelSize.circle_representation_not_finiteDimensional

instance hilbert_nontrivial : Nontrivial Hilbert := by
  cases subsingleton_or_nontrivial Hilbert with
  | inl h =>
    let : Subsingleton Hilbert := h
    exact False.elim (hilbert_not_finiteDimensional inferInstance)
  | inr h => exact h

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationTrace
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

theorem algebra_commutes_shiftedPullback_int (θ : ℝ) (r : ℤ)
    (T : Hilbert →L[ℂ] Hilbert) (hT : T ∈ algebra θ) :
    Commute T (DirectIntegral.shiftedPullback
      (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap
      (action θ r) (action_measurePreserving θ r)) := by
  let S := (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap
  let S₁ := (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap
  let J := DirectIntegral.shiftedPullback S (action θ r) (action_measurePreserving θ r)
  have hUJ : Commute U J := by
    apply FieldTraceCyclic.commute_shiftedPullback_of_covariance U (fun _ => S₁)
      S (action θ r) (action_measurePreserving θ r) U_ae
    apply Filter.Eventually.of_forall
    intro x
    dsimp [S, S₁]
    rw [← WeightedShift.shift_add, ← WeightedShift.shift_add, add_comm (1 : ℤ) r]
  have hVJ : Commute (V θ) J := by
    apply FieldTraceCyclic.commute_shiftedPullback_of_covariance (V θ)
      (fun x => WeightedShift.diagonal (orbitWeight θ character x))
      S (action θ r) (action_measurePreserving θ r) (representation_ae θ character)
    apply Filter.Eventually.of_forall
    intro x
    ext v k
    change character (action θ k x) * v (k - r) =
      character (action θ (k - r) (action θ r x)) * v (k - r)
    simp only [action_add, sub_add_cancel]
  have hJ : J ∈ (algebra θ).commutant := by
    apply (mem_commutant_vonNeumannGenerated_iff _ _).mpr
    intro A hA
    rcases Set.mem_insert_iff.mp hA with rfl | hA
    · exact ⟨hUJ.eq, (commute_star_left_of_mem_unitary U_mem_unitary hUJ).eq⟩
    · have hAV : A = V θ := Set.mem_singleton_iff.mp hA
      subst A
      exact ⟨hVJ.eq, (commute_star_left_of_mem_unitary (V_mem_unitary θ) hVJ).eq⟩
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hJ) T hT

theorem vacuum_faithfulTracial (θ : ℝ) :
    IsFaithfulTracialVector (algebra θ) vacuum := by
  let b : HilbertBasis ℤ ℂ Fiber :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fiber)
  have hb (k : ℤ) : b k = lp.single 2 k 1 := by
    rw [← HilbertBasis.repr_symm_single]
    rfl
  have hshift (r k : ℤ) :
      (WeightedShift.shift r).toLinearIsometry (b k) = b (k + r) := by
    rw [hb, hb]
    ext j
    change (lp.single 2 k (1 : ℂ) : Fiber) (j-r) = (lp.single 2 (k+r) (1 : ℂ) : Fiber) j
    simp only [lp.single_apply]
    simp only [Pi.single_apply]
    by_cases h : j - r = k
    · have h' : j = k + r := by omega
      rw [ite_eq_left h, ite_eq_left h']
    · have h' : j ≠ k + r := by omega
      rw [ite_eq_right h, ite_eq_right h']
  have h := FieldTraceCyclic.faithfulTracialVector_of_commuting_shiftedPullbacks
    b (algebra θ) (action θ) (action_measurePreserving θ)
    (fun r => (WeightedShift.shift r).toLinearIsometry) hshift
    (fun T hT r => algebra_commutes_shiftedPullback_int θ r T hT) ?_
  · simpa only [hb, vacuum] using h
  · intro T hT
    obtain ⟨A, hbound, hm, hrep, _⟩ := exists_unique_field hT
    exact ⟨A, hrep, fun r => (hm (b r)).aestronglyMeasurable,
      Filter.Eventually.of_forall hbound⟩

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationProjectionTransport
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton _root_.OAI.Invariant233.vectorTraceCLM_apply _root_.OAI.Invariant233.vectorTraceContinuousLinearMap_apply _root_.OAI.Invariant233.vonNeumannVectorTraceCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233

theorem hasOnlyTrivialInvariantProjections_smul_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) (c : ℂ) (hc : c ≠ 0) :
    HasOnlyTrivialInvariantProjections M (c • T) ↔ HasOnlyTrivialInvariantProjections M T := by
  constructor
  · intro h p hp hpP hTp
    apply h p hp hpP
    simp only [mul_smul_comm, smul_mul_assoc, hTp, smul_zero]
  · intro h p hp hpP hTp
    apply h p hp hpP
    simpa only [mul_smul_comm, smul_mul_assoc, smul_eq_zero, hc, false_or] using hTp

namespace Rotation

theorem hasOnlyTrivialInvariantProjections_of_exponentialTransfer
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b)
    (A B : Hilbert →L[ℂ] Hilbert)
    (hD : ∀ ξ : (exponentialTransfer θ b).domain,
      A ξ.val ∈ (exponentialTransfer θ b).domain)
    (hI : ∀ ξ : (exponentialTransfer θ b).domain,
      exponentialTransfer θ b ⟨A ξ.val, hD ξ⟩ = B (exponentialTransfer θ b ξ))
    (hB : HasOnlyTrivialInvariantProjections (algebra θ) B) :
    HasOnlyTrivialInvariantProjections (algebra θ) A := by
  intro p hp hpP hAp
  obtain ⟨hPm, hPP, hPB, htrace⟩ :=
    exponentialTransfer_projection_transport θ hb A B p hp hpP hAp hD hI
  let P := (InvariantRotation.AffiliatedTransport.transported
    (exponentialTransfer θ b) p.range).starProjection
  have hfaith := (vacuum_faithfulTracial θ).2.2
  rcases hB P hPm hPP hPB with hP | hP
  · left
    apply hfaith p hp (ContinuousLinearMap.IsPositive.of_isStarProjection hpP)
    rw [← htrace]
    change vectorTrace vacuum P = 0
    rw [hP]
    simp [vectorTrace]
  · right
    have hc : vectorTrace vacuum (1 - p) = 0 := by
      have he : vectorTrace vacuum (1 - p) =
          vectorTrace vacuum 1 - vectorTrace vacuum p := by
        simp only [vectorTrace, sub_apply, inner_sub_right]
      rw [he, ← htrace]
      change vectorTrace vacuum 1 - vectorTrace vacuum P = 0
      rw [hP, sub_self]
    have hz := hfaith (1 - p) ((algebra θ).sub_mem (algebra θ).one_mem hp)
      (ContinuousLinearMap.IsPositive.of_isStarProjection hpP.one_sub) hc
    exact (sub_eq_zero.mp hz).symm

theorem hasOnlyTrivialInvariantProjections_of_scaled_exponentialTransfer
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b)
    (A B : Hilbert →L[ℂ] Hilbert) (c : ℂ) (hc : c ≠ 0)
    (hD : ∀ ξ : (exponentialTransfer θ b).domain,
      A ξ.val ∈ (exponentialTransfer θ b).domain)
    (hI : ∀ ξ : (exponentialTransfer θ b).domain,
      exponentialTransfer θ b ⟨A ξ.val, hD ξ⟩ = c • B (exponentialTransfer θ b ξ))
    (hB : HasOnlyTrivialInvariantProjections (algebra θ) B) :
    HasOnlyTrivialInvariantProjections (algebra θ) A := by
  apply hasOnlyTrivialInvariantProjections_of_exponentialTransfer θ hb A (c • B) hD hI
  exact (hasOnlyTrivialInvariantProjections_smul_iff (algebra θ) B c hc).mpr hB

end Rotation
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_ContinuousProjectionTransport
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem continuousWeight_hasOnlyTrivialInvariantProjections
    (d : BackgroundBumpData θ)
    (hstar : HasOnlyTrivialInvariantProjections (Rotation.algebra θ)
      (Rotation.U * Rotation.measurableRepresentation θ
        (fun x => (p.measurableWeight θ x : ℂ)) 1 zero_le_one
        hp.measurable_complexParameterWeight hp.norm_complexParameterWeight_le_one)) :
    HasOnlyTrivialInvariantProjections (Rotation.algebra θ)
      (Rotation.weightedReal θ
        ⟨p.continuousWeight θ d, (hp.isContinuousCircleWeight_continuousWeight d).1⟩) := by
  let f : C(Circle, ℝ) :=
    ⟨p.continuousWeight θ d, (hp.isContinuousCircleWeight_continuousWeight d).1⟩
  let H := Rotation.exponentialTransfer θ (p.continuousTransfer θ d)
  let Tstar := Rotation.U * Rotation.measurableRepresentation θ
    (fun x => (p.measurableWeight θ x : ℂ)) 1 zero_le_one
    hp.measurable_complexParameterWeight hp.norm_complexParameterWeight_le_one
  have h := hp.continuousWeight_natural_intertwining d
  let hD : ∀ ξ : H.domain, Rotation.weightedReal θ f ξ.val ∈ H.domain :=
    fun ξ => (h ξ).choose
  have hI : ∀ ξ : H.domain, H ⟨Rotation.weightedReal θ f ξ.val, hD ξ⟩ =
      (Real.exp (-1) : ℂ) • Tstar (H ξ) := fun ξ => (h ξ).choose_spec
  exact Rotation.hasOnlyTrivialInvariantProjections_of_scaled_exponentialTransfer θ
    (measurable_continuousTransfer d) (Rotation.weightedReal θ f) Tstar
    (Real.exp (-1) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) hD hI hstar

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationDiagonalState
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.hilbert_nontrivial _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.WeightedShift.diagonalAlgHom_apply _root_.OAI.Invariant233.WeightedShift.diagonal_add _root_.OAI.Invariant233.WeightedShift.diagonal_apply _root_.OAI.Invariant233.WeightedShift.diagonal_mul _root_.OAI.Invariant233.WeightedShift.diagonal_one _root_.OAI.Invariant233.WeightedShift.diagonal_smul _root_.OAI.Invariant233.WeightedShift.diagonal_star _root_.OAI.Invariant233.WeightedShift.diagonal_zero _root_.OAI.Invariant233.WeightedShift.operator_apply _root_.OAI.Invariant233.WeightedShift.orbitProduct_apply _root_.OAI.Invariant233.WeightedShift.reindex_apply _root_.OAI.Invariant233.WeightedShift.shift_apply _root_.OAI.Invariant233.WeightedShift.shift_zero _root_.OAI.Invariant233.WeightedShift.translate_add _root_.OAI.Invariant233.WeightedShift.translate_apply _root_.OAI.Invariant233.WeightedShift.translate_zero _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

theorem vacuumFunctional_representation (θ : ℝ) (a : C(Circle, ℂ)) :
    vacuumFunctional (representation θ a) = ∫ x, a x ∂circleMeasure := by
  change inner ℂ vacuum (representation θ a vacuum) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  have hv : vacuum =ᵐ[circleMeasure]
      fun _ => lp.single 2 (0 : ℤ) (1 : ℂ) := Lp.coeFn_const 2 circleMeasure _
  have hp : representation θ a vacuum =ᵐ[circleMeasure]
      fun x => WeightedShift.diagonal (orbitWeight θ a x) (vacuum x) := by
    unfold representation WeightedShift.fieldDiagonal WeightedShift.fieldDiagonalLinear
    exact WeightedShift.fieldDiagonalVec_ae (orbitWeight θ a) ‖a‖ (norm_nonneg a)
      (fun x => lp.norm_le_of_forall_le (norm_nonneg a) (fun k => a.norm_coe_le_norm _))
      (fun k => (a.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
      vacuum
  filter_upwards [hv, hp] with x hv hp
  rw [hp, hv, lp.inner_single_left]
  change inner ℂ (1 : ℂ) (a (action θ 0 x) * 1) = a x
  simp [action]

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ScalarDeterminantZero
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Invariant233.ScalarDeterminant

theorem log_sq_add_sq_le {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    Real.log (a ^ 2 + t ^ 2) ≤ Real.log 2 + 2 * Real.log (max a t) := by
  have hm : 0 < max a t := ht.trans_le (le_max_right a t)
  have ha2 := pow_le_pow_left₀ ha (le_max_left a t) 2
  have ht2 := pow_le_pow_left₀ ht.le (le_max_right a t) 2
  have hlog : Real.log (a ^ 2 + t ^ 2) ≤ Real.log (2 * (max a t) ^ 2) :=
    Real.log_le_log (by positivity) (by linarith)
  calc
    _ ≤ Real.log (2 * (max a t) ^ 2) := hlog
    _ = _ := by rw [Real.log_mul (by norm_num) (pow_ne_zero _ hm.ne'), Real.log_pow]; norm_num

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem integrable_regularized_log {f : X → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x => Real.log (f x ^ 2 + ε)) μ := by
  refine (integrable_const (|Real.log ε| + |Real.log (1 + ε)|)).mono'
    ((hf.pow_const 2 |>.add_const ε).log.aestronglyMeasurable) ?_
  filter_upwards [] with x
  have hx := hbound x
  have hlo : Real.log ε ≤ Real.log (f x ^ 2 + ε) :=
    Real.log_le_log hε (le_add_of_nonneg_left (sq_nonneg _))
  have hhi : Real.log (f x ^ 2 + ε) ≤ Real.log (1 + ε) := by
    apply Real.log_le_log (by positivity)
    nlinarith
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := neg_abs_le (Real.log ε)
    have := abs_nonneg (Real.log (1 + ε))
    linarith
  · have := le_abs_self (Real.log (1 + ε))
    have := abs_nonneg (Real.log ε)
    linarith

theorem integrable_truncated_log {f : X → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {M : ℝ} (hM : 0 < M) :
    Integrable (fun x => Real.log (max (f x) (Real.exp (-M)))) μ := by
  refine (integrable_const M).mono'
    ((hf.max measurable_const).log.aestronglyMeasurable) ?_
  filter_upwards [] with x
  have hp : 0 < max (f x) (Real.exp (-M)) :=
    (Real.exp_pos _).trans_le (le_max_right _ _)
  have hlo : -M ≤ Real.log (max (f x) (Real.exp (-M))) := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos (-M)) (le_max_right (f x) (Real.exp (-M)))
  have hhi : Real.log (max (f x) (Real.exp (-M))) ≤ 0 := by
    apply Real.log_nonpos hp.le
    exact max_le (hbound x).2 (Real.exp_le_one_iff.mpr (by linarith))
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨hlo, hhi.trans hM.le⟩

variable [IsProbabilityMeasure μ]

theorem integral_regularized_log_le {f : X → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {M : ℝ} (hM : 0 < M) :
    (∫ x, Real.log (f x ^ 2 + (Real.exp (-M)) ^ 2) ∂μ) ≤
      Real.log 2 + 2 * ∫ x, Real.log (max (f x) (Real.exp (-M))) ∂μ := by
  have hint := integrable_truncated_log (μ := μ) hf hbound hM
  calc
    _ ≤ ∫ x, Real.log 2 + 2 * Real.log (max (f x) (Real.exp (-M))) ∂μ :=
      integral_mono (integrable_regularized_log hf hbound (sq_pos_of_pos (Real.exp_pos _)))
        ((integrable_const _).add (hint.const_mul 2))
        (fun x => log_sq_add_sq_le (hbound x).1 (Real.exp_pos _))
    _ = _ := by
      rw [integral_add (integrable_const _) (hint.const_mul 2), integral_const_mul]
      simp

theorem regularized_determinant_eq_zero {f : X → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (htrunc : ∀ B : ℝ, ∃ M : ℝ, 0 < M ∧
      (∫ x, Real.log (max (f x) (Real.exp (-M))) ∂μ) < B) :
    (⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
      (Real.exp ((∫ x, Real.log (f x ^ 2 + ε.val) ∂μ) / 2))) = 0 := by
  apply le_antisymm _ bot_le
  have hlow (n : ℕ) :
      (⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
        (Real.exp ((∫ x, Real.log (f x ^ 2 + ε.val) ∂μ) / 2))) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
    obtain ⟨M, hM, hsmall⟩ := htrunc (-(n : ℝ) - Real.log 2 / 2)
    have hint := integral_regularized_log_le (μ := μ) hf hbound hM
    calc
      _ ≤ ENNReal.ofReal (Real.exp
          ((∫ x, Real.log (f x ^ 2 + (Real.exp (-M)) ^ 2) ∂μ) / 2)) :=
        iInf_le _ (⟨(Real.exp (-M)) ^ 2, sq_pos_of_pos (Real.exp_pos _)⟩ : {r : ℝ // 0 < r})
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        linarith
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(n : ℝ))))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop)
  exact ge_of_tendsto' hlim hlow


end Invariant233.ScalarDeterminant

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_SpectralNaturality
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal CStarAlgebra

namespace Invariant233

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma regularizedNormSquare_spectrum_pos (a : A) (ε : ℝ) (hε : 0 < ε) :
    ∀ x ∈ spectrum ℝ (star a * a + ε • (1 : A)), 0 < x := by
  intro x hx
  rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.add_singleton_eq] at hx
  obtain ⟨y, hy, t, ht, rfl⟩ := Set.mem_add.mp hx
  have ht' : t = ε := Set.mem_singleton_iff.mp ht
  subst t
  linarith [spectrum_star_mul_self_nonneg y hy]

lemma regularizedLog_map (φ : A →⋆ₐ[ℂ] B) (a : A) (ε : ℝ) (hε : 0 < ε) :
    φ (CFC.log (star a * a + ε • (1 : A))) =
      CFC.log (star (φ a) * φ a + ε • (1 : B)) := by
  have hp := regularizedNormSquare_spectrum_pos a ε hε
  have hc : ContinuousOn Real.log (spectrum ℝ (star a * a + ε • (1 : A))) := by
    apply Real.continuousOn_log.mono
    intro x hx
    exact ne_of_gt (hp x hx)
  have hs : IsSelfAdjoint (star a * a + ε • (1 : A)) := by
    simp [IsSelfAdjoint]
  have hφs : IsSelfAdjoint (φ (star a * a + ε • (1 : A))) := by
    change star (φ _) = φ _
    rw [← map_star, hs.star_eq]
  have hsmul : φ (ε • (1 : A)) = ε • (1 : B) := by
    calc
      φ (ε • (1 : A)) = ε • φ 1 := φ.toAlgHom.map_smul_of_tower ε 1
      _ = ε • (1 : B) := by rw [map_one]
  rw [CFC.log, φ.map_cfc Real.log _ hc (by fun_prop) hs hφs]
  simp only [map_add, map_mul, map_star, hsmul, CFC.log]

lemma regularizedLog_complex (z : ℂ) (ε : ℝ) :
    CFC.log (star z * z + ε • (1 : ℂ)) =
      (Real.log (‖z‖ ^ 2 + ε) : ℂ) := by
  have h : star z * z + ε • (1 : ℂ) =
      algebraMap ℝ ℂ (‖z‖ ^ 2 + ε) := by
    simp only [Complex.star_def, Complex.conj_mul', Complex.real_smul, mul_one,
      Complex.coe_algebraMap, Complex.ofReal_add, Complex.ofReal_pow]
  rw [h, CFC.log_algebraMap]
  rfl

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_DeterminantWeightBridge
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.Rotation.hilbert_nontrivial _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233

theorem ScalarDeterminant.regularized_determinant_eq_zero_of_log_integral
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hm : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hpos : ∀ᵐ x ∂μ, 0 < f x) (hinf : HasNegInfiniteLogIntegral μ f) :
    (⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
      (Real.exp ((∫ x, Real.log (f x ^ 2 + ε.val) ∂μ) / 2))) = 0 := by
  apply ScalarDeterminant.regularized_determinant_eq_zero hm hbound
  intro B
  obtain ⟨M, hM, hlt⟩ := exists_pos_truncated_log_integral_lt f hm
    (fun x => (hbound x).1) (fun x => (hbound x).2) hpos
    ((hasNegInfiniteLogIntegral_iff_of_ae_pos f hpos).mp hinf) (-B / 2)
  refine ⟨M, hM, ?_⟩
  linarith

theorem IsContinuousCircleWeight.regularized_determinant_eq_zero
    {f : Circle → ℝ} (hf : IsContinuousCircleWeight f) :
    (⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
      (Real.exp ((∫ x, Real.log (f x ^ 2 + ε.val) ∂circleMeasure) / 2))) = 0 := by
  let : IsProbabilityMeasure circleMeasure := ⟨by
    simp only [circleMeasure, AddCircle.measure_univ, ENNReal.ofReal_one]⟩
  exact ScalarDeterminant.regularized_determinant_eq_zero_of_log_integral
    hf.1.measurable hf.2.1 hf.ae_pos hf.2.2.2

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ExponentialDecay
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology
open scoped BigOperators ENNReal

namespace Invariant233

theorem tendsto_root_zero_of_exponential_decay (u : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n)
    (hdecay : ∀ a : ℝ, 0 < a → ∀ᶠ n : ℕ in atTop,
      u n ≤ Real.exp (-a * (n : ℝ))) :
    Tendsto (fun n : ℕ => (u n) ^ (1 / (n : ℝ))) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact Filter.Eventually.of_forall fun n =>
      hc.trans_le (Real.rpow_nonneg (hu n) _)
  · intro ε hε
    have he : ∀ᶠ a : ℝ in atTop, Real.exp (-a) < ε :=
      (tendsto_order.mp Real.tendsto_exp_neg_atTop_nhds_zero).2 ε hε
    obtain ⟨a, ha, hae⟩ := ((eventually_gt_atTop (0 : ℝ)).and he).exists
    filter_upwards [hdecay a ha, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    have hnzero : n ≠ 0 := Nat.ne_of_gt hnpos
    have hroot := Real.rpow_le_rpow (hu n) hn (by positivity : 0 ≤ 1 / (n : ℝ))
    have heq : Real.exp (-a * (n : ℝ)) = (Real.exp (-a)) ^ n := by
      rw [mul_comm, Real.exp_nat_mul]
    rw [heq, one_div, Real.pow_rpow_inv_natCast (Real.exp_nonneg _) hnzero] at hroot
    simpa only [one_div] using hroot.trans_lt hae

theorem norm_quasinilpotent_of_exponential_decay {A : Type*} [NormedRing A]
    (T : A)
    (hdecay : ∀ a : ℝ, 0 < a → ∀ᶠ n : ℕ in atTop,
      ‖T ^ n‖ ≤ Real.exp (-a * (n : ℝ))) :
    Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0) :=
  tendsto_root_zero_of_exponential_decay (fun n => ‖T ^ n‖)
    (fun _ => norm_nonneg _) hdecay

theorem spectralRadius_zero_of_norm_root_tendsto_zero {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (T : A)
    (hroot : Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0)) :
    spectralRadius ℂ T = 0 := by
  have hzero : Tendsto
      (fun n : ℕ => ENNReal.ofReal (‖T ^ n‖ ^ (1 / (n : ℝ))))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hroot
  exact tendsto_nhds_unique
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius T) hzero

theorem spectrum_subset_zero_of_spectralRadius_zero {𝕜 A : Type*}
    [NormedField 𝕜] [Ring A] [Algebra 𝕜 A] (T : A)
    (hzero : spectralRadius 𝕜 T = 0) :
    spectrum 𝕜 T ⊆ {0} := by
  intro z hz
  have hnorm : (‖z‖₊ : ℝ≥0∞) ≤ spectralRadius 𝕜 T := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup₂ (f := fun scalar (_ : scalar ∈ spectrum 𝕜 T) =>
      (‖scalar‖₊ : ℝ≥0∞)) z hz
  rw [hzero] at hnorm
  simpa using hnorm

theorem spectrum_eq_zero_of_spectralRadius_zero {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (T : A)
    (hzero : spectralRadius ℂ T = 0) : spectrum ℂ T = {0} := by
  have hsub := spectrum_subset_zero_of_spectralRadius_zero T hzero
  apply Set.Subset.antisymm hsub
  obtain ⟨z, hz⟩ := spectrum.nonempty T
  have hz0 : z = 0 := hsub hz
  simpa only [Set.singleton_subset_iff, hz0] using hz

theorem spectrum_eq_zero_of_norm_root_tendsto_zero {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (T : A)
    (hroot : Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0)) :
    spectrum ℂ T = {0} :=
  spectrum_eq_zero_of_spectralRadius_zero T
    (spectralRadius_zero_of_norm_root_tendsto_zero T hroot)

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldPowerBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal

namespace InvariantProjection.FieldPowerBounds

variable {X E : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {μ : Measure X}

theorem ae_pow_apply (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : X → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ⇑(T ξ) =ᵐ[μ] fun x => A x (ξ x))
    (n : ℕ) (ξ : Lp E 2 μ) :
    ⇑((T ^ n) ξ) =ᵐ[μ] fun x => (A x ^ n) (ξ x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    filter_upwards [hT ((T ^ n) ξ), ih] with x hx hix
    rw [hx, hix, pow_succ', mul_apply_eq_comp]

theorem norm_pow_le (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : X → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ⇑(T ξ) =ᵐ[μ] fun x => A x (ξ x))
    (n : ℕ) {B : ℝ} (hB : 0 ≤ B) (hA : ∀ᵐ x ∂μ, ‖A x ^ n‖ ≤ B) :
    ‖T ^ n‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro ξ
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [ae_pow_apply T A hT n ξ, hA] with x hx hAx
  rw [hx]
  exact ((A x ^ n).le_opNorm (ξ x)).trans
    (mul_le_mul_of_nonneg_right hAx (norm_nonneg _))

theorem all_rates_norm_decay (T : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (A : X → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ⇑(T ξ) =ᵐ[μ] fun x => A x (ξ x))
    (hA : ∀ a : ℝ, 0 < a → ∀ᶠ (n : ℕ) in atTop,
      ∀ᵐ x ∂μ, ‖A x ^ n‖ ≤ Real.exp (-a * n)) :
    ∀ a : ℝ, 0 < a → ∀ᶠ (n : ℕ) in atTop,
      ‖T ^ n‖ ≤ Real.exp (-a * n) := by
  intro a ha
  filter_upwards [hA a ha] with n hn
  exact norm_pow_le T A hT n (Real.exp_nonneg _) hn

end InvariantProjection.FieldPowerBounds

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationDecay
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open Filter Finset

namespace InvariantProjection.RotationDecay

variable {X : Type*}

lemma le_exp_truncatedLog (f : X → ℝ) (M : ℝ) (x : X) :
    f x ≤ Real.exp (truncatedLog f M x) := by
  rw [truncatedLog, Real.exp_log (lt_of_lt_of_le (Real.exp_pos (-M)) (le_max_right _ _))]
  exact le_max_left _ _

lemma orbitProduct_le_exp_sum_truncatedLog {σ : X → X} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) (M : ℝ) (n : ℕ) (x : X) :
    orbitProduct σ f n x ≤
      Real.exp (∑ k ∈ range n, truncatedLog f M (σ^[k] x)) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod (fun k _ => hf (σ^[k] x))
    (fun k _ => le_exp_truncatedLog f M (σ^[k] x))

lemma orbitProduct_le_exp_of_sum_le {σ : X → X} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) (M a : ℝ) (n : ℕ) (x : X)
    (h : (∑ k ∈ range n, truncatedLog f M (σ^[k] x)) ≤ -a * n) :
    orbitProduct σ f n x ≤ Real.exp (-a * n) :=
  (orbitProduct_le_exp_sum_truncatedLog hf M n x).trans (Real.exp_le_exp.mpr h)

lemma orbitProduct_le_exp_of_average_le {σ : X → X} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) (M a : ℝ) {n : ℕ} (hn : 0 < n) (x : X)
    (h : birkhoffAverage ℝ σ (truncatedLog f M) n x ≤ -a) :
    orbitProduct σ f n x ≤ Real.exp (-a * n) := by
  apply orbitProduct_le_exp_of_sum_le hf M a n x
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  change (n : ℝ)⁻¹ * (∑ k ∈ range n, truncatedLog f M (σ^[k] x)) ≤ -a at h
  have h' := mul_le_mul_of_nonneg_left h hn'.le
  simpa [← mul_assoc, mul_inv_cancel₀ hn'.ne', mul_comm (n : ℝ) (-a)] using h'

lemma eventually_orbitProduct_le_exp {σ : X → X} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) (M a I : ℝ) (ha : 0 < a) (hI : I < -2 * a)
    (havg : TendstoUniformly
      (fun n x => birkhoffAverage ℝ σ (truncatedLog f M) n x)
      (fun _ => I) atTop) :
    ∀ᶠ n in atTop, ∀ x, orbitProduct σ f n x ≤ Real.exp (-a * n) := by
  have hclose := (Metric.tendstoUniformly_iff.mp havg) a ha
  filter_upwards [hclose, eventually_gt_atTop 0] with n hn hnpos
  intro x
  apply orbitProduct_le_exp_of_average_le hf M a hnpos x
  have hx := hn x
  rw [Real.dist_eq] at hx
  have hx' := (abs_lt.mp hx).1
  linarith

theorem all_rates_orbitProduct_decay {σ : X → X} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x)
    (hmean : ∀ a : ℝ, 0 < a → ∃ M I : ℝ, I < -2 * a ∧
      TendstoUniformly
        (fun n x => birkhoffAverage ℝ σ (truncatedLog f M) n x)
        (fun _ => I) atTop) :
    ∀ a : ℝ, 0 < a →
      ∀ᶠ n in atTop, ∀ x, orbitProduct σ f n x ≤ Real.exp (-a * n) := by
  intro a ha
  obtain ⟨M, I, hI, havg⟩ := hmean a ha
  exact eventually_orbitProduct_le_exp hf M a I ha hI havg

end InvariantProjection.RotationDecay

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_UniformRotationAverage
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Finset MeasureTheory
open scoped Topology BigOperators

namespace InvariantProjection.UniformRotationAverage

attribute [local instance] OAI.InvariantProjection.UniformRotationAverage.instFactLtRealOfNat_solutions
lemma norm_averageL_apply_le (a : Circle) (n : ℕ) (f : CSpace) :
    ‖averageL a n f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  rw [averageL_apply, norm_mul, norm_inv]
  have hsum : ‖∑ k ∈ range n, f (x + k • a)‖ ≤ n * ‖f‖ := by
    calc
      _ ≤ ∑ k ∈ range n, ‖f (x + k • a)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ range n, ‖f‖ := sum_le_sum fun k _ => f.norm_coe_le_norm _
      _ = n * ‖f‖ := by simp
  have hcast : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  rw [hcast]
  calc
    _ ≤ (n : ℝ)⁻¹ * (n * ‖f‖) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ ≤ ‖f‖ := by
      by_cases hn : n = 0
      · simp [hn]
      · rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]

lemma averageL_lipschitz (a : Circle) (n : ℕ) : LipschitzWith 1 (averageL a n) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub] using
    norm_averageL_apply_le a n (f - g)

lemma isClosed_convergentSubmodule (a : Circle) :
    IsClosed (convergentSubmodule a : Set CSpace) := by
  exact (LipschitzWith.uniformEquicontinuous (fun n => averageL a n) 1
    (averageL_lipschitz a)).equicontinuous.isClosed_setOfPred_tendsto meanL.continuous

lemma fourier_translate (m : ℤ) (a x : Circle) (k : ℕ) :
    fourier m (x + k • a) = fourier m x * (fourier m a) ^ k := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, _root_.Circle.coe_mul]
  rw [smul_comm m k a, AddCircle.toCircle_nsmul, _root_.Circle.coe_pow]

lemma averageL_fourier (a : Circle) (n : ℕ) (m : ℤ) :
    averageL a n (fourier m) =
      ((n : ℂ)⁻¹ * ∑ k ∈ range n, (fourier m a) ^ k) • fourier m := by
  apply ContinuousMap.ext
  intro x
  simp only [averageL_apply, fourier_translate, ← mul_sum,
    ContinuousMap.smul_apply, smul_eq_mul]
  ring

lemma norm_geometric_sum_le {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) (n : ℕ) :
    ‖∑ k ∈ range n, z ^ k‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hne, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

lemma tendsto_averageL_fourier_zero {a : Circle} {m : ℤ}
    (hne : fourier m a ≠ 1) :
    Tendsto (fun n => averageL a n (fourier m)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun n : ℕ => (n : ℝ)⁻¹ * (2 / ‖fourier m a - 1‖))
  · intro n
    rw [averageL_fourier, norm_smul, fourier_norm, mul_one, norm_mul, norm_inv]
    have hcast : ‖(n : ℂ)‖ = (n : ℝ) := by simp
    rw [hcast]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
    exact norm_geometric_sum_le (_root_.Circle.norm_coe _) hne n
  · simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
      (2 / ‖fourier m a - 1‖)

lemma fourier_ne_one_of_irrational {θ : ℝ} (hθ : Irrational θ)
    {m : ℤ} (hm : m ≠ 0) : fourier m (θ : Circle) ≠ 1 := by
  intro h
  have hc : AddCircle.toCircle (m • (θ : Circle)) = AddCircle.toCircle (0 : Circle) := by
    apply Subtype.ext
    simpa only [fourier_apply, AddCircle.toCircle_zero, _root_.Circle.coe_one] using h
  have hz := AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0) hc
  rw [← AddCircle.coe_zsmul, AddCircle.coe_eq_zero_iff] at hz
  obtain ⟨k, hk⟩ := hz
  have hi : Irrational ((m : ℝ) * θ) := irrational_intCast_mul_iff.mpr ⟨hm, hθ⟩
  apply hi.ne_int k
  simpa only [zsmul_eq_mul, mul_one] using hk.symm

lemma meanL_fourier_of_ne_zero {m : ℤ} (hm : m ≠ 0) :
    meanL (fourier m) = 0 := by
  rw [meanL_apply]
  have hi : (∫ x : Circle, fourier m x ∂AddCircle.haarAddCircle) = 0 :=
    integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hm (by norm_num))
  rw [hi]
  rfl

lemma fourier_mem_convergentSubmodule {θ : ℝ} (hθ : Irrational θ) (m : ℤ) :
    fourier m ∈ convergentSubmodule (θ : Circle) := by
  change Tendsto (fun n => averageL (θ : Circle) n (fourier m)) atTop
    (𝓝 (meanL (fourier m)))
  by_cases hm : m = 0
  · subst m
    have hm : meanL (fourier (T := (1 : ℝ)) 0) = 1 := by
      rw [meanL_apply]
      simp only [fourier_zero, integral_const, probReal_univ, one_smul]
      exact ContinuousMap.const_one
    rw [hm]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    apply ContinuousMap.ext
    intro x
    simp [averageL_apply, hn]
  · rw [meanL_fourier_of_ne_zero hm]
    exact tendsto_averageL_fourier_zero (fourier_ne_one_of_irrational hθ hm)

theorem tendsto_averageL {θ : ℝ} (hθ : Irrational θ) (f : CSpace) :
    Tendsto (fun n => averageL (θ : Circle) n f) atTop (𝓝 (meanL f)) := by
  have hs : Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) ≤
      convergentSubmodule (θ : Circle) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨m, rfl⟩
    exact fourier_mem_convergentSubmodule hθ m
  have hc := Submodule.topologicalClosure_minimal
    (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))))
    hs (isClosed_convergentSubmodule (θ : Circle))
  rw [span_fourier_closure_eq_top] at hc
  exact hc (Submodule.mem_top)

theorem tendstoUniformly_complex {θ : ℝ} (hθ : Irrational θ) (f : CSpace) :
    TendstoUniformly
      (fun (n : ℕ) x => (n : ℂ)⁻¹ * ∑ k ∈ range n, f (x + k • (θ : Circle)))
      (fun _ => ∫ x, f x ∂AddCircle.haarAddCircle) atTop := by
  have h := ContinuousMap.tendsto_iff_tendstoUniformly.mp (tendsto_averageL hθ f)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.mp h) ε hε] with n hn
  intro x
  simpa only [averageL_apply, meanL_apply, ContinuousMap.const_apply] using hn x

theorem tendstoUniformly_real {θ : ℝ} (hθ : Irrational θ)
    (f : C(Circle, ℝ)) :
    TendstoUniformly
      (fun n x => birkhoffAverage ℝ (fun y : Circle => y + (θ : Circle)) f n x)
      (fun _ => ∫ x, f x ∂AddCircle.haarAddCircle) atTop := by
  let fC : CSpace := ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hc := Complex.uniformContinuous_re.comp_tendstoUniformly
    (tendstoUniformly_complex hθ fC)
  simp only [Function.comp_def] at hc
  have heq : (fun (n : ℕ) (x : Circle) =>
      ((n : ℂ)⁻¹ * ∑ k ∈ range n, fC (x + k • (θ : Circle))).re) =
      (fun n x => birkhoffAverage ℝ (fun y : Circle => y + (θ : Circle)) f n x) := by
    funext n x
    simp only [fC, ContinuousMap.coe_mk, birkhoffAverage, birkhoffSum,
      add_right_iterate, smul_eq_mul]
    norm_cast
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [heq] at hc
  simpa only [fC, ContinuousMap.coe_mk, integral_complex_ofReal, Complex.ofReal_re] using hc

end InvariantProjection.UniformRotationAverage

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleWeightDecay
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.Rotation.hilbert_nontrivial _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Finset MeasureTheory
open scoped Topology BigOperators ENNReal

namespace InvariantProjection.CircleWeightDecay

attribute [local instance] OAI.InvariantProjection.CircleWeightDecay.circleWeightDecayPeriodPos
theorem all_rates_decay {θ : ℝ} (hθ : Irrational θ) (f : C(Circle, ℝ))
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hpos : ∀ᵐ x ∂AddCircle.haarAddCircle, 0 < f x)
    (hlog : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂AddCircle.haarAddCircle) = ∞) :
    ∀ a : ℝ, 0 < a → ∀ᶠ n in atTop, ∀ x : Circle,
      (∏ k ∈ range n, f (x + k • (θ : Circle))) ≤ Real.exp (-a * n) := by
  have h := RotationDecay.all_rates_orbitProduct_decay
    (σ := fun y : Circle => y + (θ : Circle)) hf0 ?_
  · simpa only [RotationDecay.orbitProduct, add_right_iterate] using h
  intro a ha
  obtain ⟨M, hM⟩ := Invariant233.exists_truncated_log_integral_lt f f.continuous.measurable
    hf0 hf1 hpos hlog (2 * a)
  let l : C(Circle, ℝ) := ⟨RotationDecay.truncatedLog f M,
    Invariant233.continuous_truncated_log f f.continuous M⟩
  refine ⟨M, ∫ x, l x ∂AddCircle.haarAddCircle, ?_, ?_⟩
  · change (∫ x, Real.log (max (f x) (Real.exp (-(M : ℝ))))
      ∂AddCircle.haarAddCircle) < -2 * a
    simpa only [neg_mul] using hM
  · exact UniformRotationAverage.tendstoUniformly_real hθ l

lemma circleMeasure_eq_haar : Invariant233.circleMeasure =
    (AddCircle.haarAddCircle : Measure Circle) := by
  change (volume : Measure Circle) = _
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  norm_num

theorem all_rates_decay_of_isContinuousCircleWeight {θ : ℝ} (hθ : Irrational θ)
    {f : Invariant233.Circle → ℝ} (hf : Invariant233.IsContinuousCircleWeight f) :
    ∀ a : ℝ, 0 < a → ∀ᶠ n in atTop, ∀ x : Circle,
      (∏ k ∈ range n, f (x + k • (θ : Circle))) ≤ Real.exp (-a * n) := by
  have hpos : ∀ᵐ x ∂AddCircle.haarAddCircle, 0 < f x := by
    rw [← circleMeasure_eq_haar]
    exact hf.ae_pos
  have hlog : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂AddCircle.haarAddCircle) = ∞ := by
    rw [← circleMeasure_eq_haar]
    exact (Invariant233.hasNegInfiniteLogIntegral_iff_of_ae_pos f hf.ae_pos).mp hf.2.2.2
  exact all_rates_decay hθ ⟨f, hf.1⟩ (fun x => (hf.2.1 x).1)
    (fun x => (hf.2.1 x).2) hpos hlog

end InvariantProjection.CircleWeightDecay

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleFiberDecay
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Finset MeasureTheory
open scoped Topology BigOperators ENNReal

namespace InvariantProjection.CircleFiberDecay

lemma coordinate_product_eq (θ : ℝ) (f : Circle → ℝ)
    (w : Circle → Invariant233.WeightedShift.Weight)
    (hw : ∀ x k, w x k = (f (x + k • (θ : Circle)) : ℂ))
    (x : Circle) (k : ℤ) (n : ℕ) :
    (∏ j ∈ range n, w x (k + j)) =
      ((∏ j ∈ range n, f ((x + k • (θ : Circle)) + j • (θ : Circle)) : ℝ) : ℂ) := by
  simp only [hw, add_zsmul, natCast_zsmul, ← add_assoc]
  norm_cast

theorem norm_fiber_power_le (θ : ℝ) (f : Circle → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (w : Circle → Invariant233.WeightedShift.Weight)
    (hw : ∀ x k, w x k = (f (x + k • (θ : Circle)) : ℂ))
    (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hprod : ∀ x, (∏ j ∈ range n, f (x + j • (θ : Circle))) ≤ B) (x : Circle) :
    ‖(Invariant233.WeightedShift.operator (w x)) ^ n‖ ≤ B := by
  apply Invariant233.WeightedShift.norm_operator_pow_le (w x) n hB
  intro k
  rw [coordinate_product_eq θ f w hw x k n, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg]
  · exact hprod (x + k • (θ : Circle))
  · exact prod_nonneg fun j _ => hf0 _

end InvariantProjection.CircleFiberDecay

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationNonzero
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.WeightedShift.diagonalAlgHom_apply _root_.OAI.Invariant233.WeightedShift.diagonal_add _root_.OAI.Invariant233.WeightedShift.diagonal_apply _root_.OAI.Invariant233.WeightedShift.diagonal_mul _root_.OAI.Invariant233.WeightedShift.diagonal_one _root_.OAI.Invariant233.WeightedShift.diagonal_smul _root_.OAI.Invariant233.WeightedShift.diagonal_star _root_.OAI.Invariant233.WeightedShift.diagonal_zero _root_.OAI.Invariant233.WeightedShift.operator_apply _root_.OAI.Invariant233.WeightedShift.reindex_apply _root_.OAI.Invariant233.WeightedShift.shift_apply _root_.OAI.Invariant233.WeightedShift.shift_zero _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.Rotation
open MeasureTheory

theorem representation_on_vector_ae (θ : ℝ) (a : C(Circle, ℂ)) (f : Hilbert) :
    representation θ a f =ᵐ[circleMeasure]
      fun x => WeightedShift.diagonal (orbitWeight θ a x) (f x) := by
  exact WeightedShift.fieldDiagonalVec_ae (orbitWeight θ a) ‖a‖ (norm_nonneg a)
    (fun x => lp.norm_le_of_forall_le (norm_nonneg a) (fun k => a.norm_coe_le_norm _))
    (fun k => (a.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable) f

theorem representation_vacuum_eq_zero_iff (θ : ℝ) (a : C(Circle, ℂ)) :
    representation θ a vacuum = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hout : representation θ a vacuum =ᵐ[circleMeasure] (fun _ => (0 : Fiber)) := by
      rw [h]
      exact Lp.coeFn_zero _ _ _
    have hc : vacuum =ᵐ[circleMeasure] (fun _ => lp.single 2 (0 : ℤ) (1 : ℂ)) :=
      Lp.coeFn_const 2 circleMeasure _
    have hae : (fun x : Circle => a x) =ᵐ[circleMeasure] (fun _ => (0 : ℂ)) := by
      filter_upwards [representation_on_vector_ae θ a vacuum, hc, hout] with x hx hc hz
      have heq := congrArg (fun v : Fiber => v (0 : ℤ)) (hx.symm.trans hz)
      change a (action θ 0 x) * vacuum x 0 = 0 at heq
      simpa [hc, action, lp.coeFn_single] using heq
    let : circleMeasure.IsOpenPosMeasure := by
      unfold circleMeasure
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    apply ContinuousMap.coe_injective
    exact Measure.eq_of_ae_eq hae a.continuous continuous_const
  · intro h
    subst a
    apply Lp.ext
    filter_upwards [representation_on_vector_ae θ 0 vacuum, Lp.coeFn_zero Fiber 2 circleMeasure]
      with x hx hz
    rw [hx, hz]
    ext k
    change (0 : C(Circle, ℂ)) (action θ k x) * vacuum x k = 0
    simp

theorem representation_eq_zero_iff (θ : ℝ) (a : C(Circle, ℂ)) :
    representation θ a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply (representation_vacuum_eq_zero_iff θ a).1
    simp [h]
  · intro h
    subst a
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [representation_on_vector_ae θ 0 f, Lp.coeFn_zero Fiber 2 circleMeasure]
      with x hx hz
    change (representation θ 0 f) x = (0 : Hilbert) x
    rw [hx, hz]
    ext k
    change (0 : C(Circle, ℂ)) (action θ k x) * f x k = 0
    simp

theorem fiberShift_operator_injective : Function.Injective U := by
  intro f g h
  apply Lp.ext
  filter_upwards [
    (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap.coeFn_compLpL f,
    (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap.coeFn_compLpL g]
    with x hf hg
  apply (WeightedShift.shift 1).injective
  calc
    WeightedShift.shift 1 (f x) = U f x := hf.symm
    _ = U g x := congrArg (fun v : Hilbert => v x) h
    _ = WeightedShift.shift 1 (g x) := hg

theorem weighted_eq_zero_iff (θ : ℝ) (a : C(Circle, ℂ)) :
    weighted θ a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply (representation_eq_zero_iff θ a).1
    apply ContinuousLinearMap.ext
    intro f
    apply fiberShift_operator_injective
    have heq := congrArg (fun A : Hilbert →L[ℂ] Hilbert => A f) h
    simpa [weighted] using heq
  · intro h
    rw [weighted, (representation_eq_zero_iff θ a).2 h, mul_zero]

theorem weightedReal_eq_zero_iff (θ : ℝ) (f : C(Circle, ℝ)) :
    weightedReal θ f = 0 ↔ f = 0 := by
  rw [weightedReal, weighted_eq_zero_iff]
  constructor
  · intro h
    apply ContinuousMap.ext
    intro x
    have hx := congrArg (fun a : C(Circle, ℂ) => a x) h
    simpa [complexWeight] using hx
  · intro h
    subst f
    apply ContinuousMap.ext
    intro x
    simp [complexWeight]

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_RotationQuasinilpotent
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Invariant233.Rotation

theorem weighted_on_vector_ae (θ : ℝ) (a : C(Circle, ℂ)) (ξ : Hilbert) :
    weighted θ a ξ =ᵐ[circleMeasure]
      fun x => WeightedShift.operator (orbitWeight θ a x) (ξ x) := by
  filter_upwards [
    (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap.coeFn_compLpL
      (representation θ a ξ),
    representation_on_vector_ae θ a ξ] with x hu ha
  change U (representation θ a ξ) x = _
  rw [U, hu, ha]
  rfl

theorem weightedReal_all_rates_norm_decay {θ : ℝ} (hθ : Irrational θ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    ∀ a : ℝ, 0 < a → ∀ᶠ n : ℕ in atTop,
      ‖weightedReal θ f ^ n‖ ≤ Real.exp (-a * n) := by
  apply InvariantProjection.FieldPowerBounds.all_rates_norm_decay
    (weightedReal θ f)
    (fun x => WeightedShift.operator (orbitWeight θ (complexWeight f) x))
    (weighted_on_vector_ae θ (complexWeight f))
  intro a ha
  filter_upwards [InvariantProjection.CircleWeightDecay.all_rates_decay_of_isContinuousCircleWeight
    hθ hf a ha] with n hn
  apply Filter.Eventually.of_forall
  intro x
  exact InvariantProjection.CircleFiberDecay.norm_fiber_power_le θ f
    (fun x => (hf.2.1 x).1) (orbitWeight θ (complexWeight f))
    (fun _ _ => rfl) n (Real.exp_nonneg _) hn x

theorem weightedReal_normQuasinilpotent {θ : ℝ} (hθ : Irrational θ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    NormQuasinilpotent (weightedReal θ f) :=
  norm_quasinilpotent_of_exponential_decay _ (weightedReal_all_rates_norm_decay hθ f hf)

theorem weightedReal_ne_zero_of_isContinuousCircleWeight (θ : ℝ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    weightedReal θ f ≠ 0 := by
  intro h
  have hz := (weightedReal_eq_zero_iff θ f).1 h
  obtain ⟨x, hx⟩ := hf.ae_pos.exists
  simp [hz] at hx

theorem weightedReal_spectrum {θ : ℝ} (hθ : Irrational θ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    spectrum ℂ (weightedReal θ f) = {0} :=
  spectrum_eq_zero_of_norm_root_tendsto_zero _ (weightedReal_normQuasinilpotent hθ f hf)

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_RotationDeterminant
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProjectionMeetTrace.vectorFunctional_apply _root_.OAI.Invariant233.vectorTraceCLM_apply _root_.OAI.Invariant233.vectorTraceContinuousLinearMap_apply _root_.OAI.Invariant233.vonNeumannVectorTraceCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal CStarAlgebra
namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vectorFugledeKadisonDeterminant_unitary_mul (ξ : H)
    (u : unitary (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    vectorFugledeKadisonDeterminant ξ ((u : H →L[ℂ] H) * T) =
      vectorFugledeKadisonDeterminant ξ T := by
  have h : star ((u : H →L[ℂ] H) * T) * ((u : H →L[ℂ] H) * T) = star T * T := by
    rw [star_mul, mul_assoc, ← mul_assoc (star (u : H →L[ℂ] H)),
      Unitary.star_mul_self_of_mem u.property]
    simp
  simp only [vectorFugledeKadisonDeterminant, h]

theorem vectorFugledeKadisonDeterminant_continuous_representation
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    (μ : Measure X) (π : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hξ : ∀ g : C(X, ℂ), vectorTrace ξ (π g) = ∫ x, g x ∂μ)
    (f : C(X, ℂ)) :
    vectorFugledeKadisonDeterminant ξ (π f) =
      ⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
        (Real.exp ((∫ x, Real.log (‖f x‖ ^ 2 + ε.val) ∂μ) / 2)) := by
  let : NormedAlgebra ℝ C(X, ℂ) := NormedAlgebra.restrictScalars ℝ ℂ C(X, ℂ)
  unfold vectorFugledeKadisonDeterminant
  apply iInf_congr
  intro ε
  rw [← regularizedLog_map π f ε.val ε.property, hξ]
  have hpoint : ∀ x, (CFC.log (star f * f + ε.val • (1 : C(X, ℂ)))) x =
      (Real.log (‖f x‖ ^ 2 + ε.val) : ℂ) := by
    intro x
    have h := regularizedLog_map (ContinuousMap.evalStarAlgHom ℂ ℂ x) f ε.val ε.property
    simpa only [ContinuousMap.evalStarAlgHom_apply] using
      h.trans (regularizedLog_complex (f x) ε.val)
  simp_rw [hpoint]
  rw [integral_complex_ofReal]
  rfl

namespace Rotation

theorem representation_real_vectorDeterminant_zero (θ : ℝ) (f : C(Circle, ℝ))
    (hf : IsContinuousCircleWeight f) :
    vectorFugledeKadisonDeterminant vacuum (representation θ (complexWeight f)) = 0 := by
  have hformula := vectorFugledeKadisonDeterminant_continuous_representation
    circleMeasure (representationStarAlgHom θ) vacuum
    (fun g => vacuumFunctional_representation θ g) (complexWeight f)
  change vectorFugledeKadisonDeterminant vacuum (representation θ (complexWeight f)) = _
    at hformula
  rw [hformula]
  have hnorm : ∀ x, ‖complexWeight f x‖ = f x := by
    intro x
    simp only [complexWeight, ContinuousMap.coe_mk, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hf.2.1 x).1]
  simp_rw [hnorm]
  exact hf.regularized_determinant_eq_zero

theorem weightedReal_vectorDeterminant_zero (θ : ℝ) (f : C(Circle, ℝ))
    (hf : IsContinuousCircleWeight f) :
    vectorFugledeKadisonDeterminant vacuum (weightedReal θ f) = 0 := by
  let u : unitary (Hilbert →L[ℂ] Hilbert) := ⟨U, U_mem_unitary⟩
  change vectorFugledeKadisonDeterminant vacuum
    ((u : Hilbert →L[ℂ] Hilbert) * representation θ (complexWeight f)) = 0
  rw [vectorFugledeKadisonDeterminant_unitary_mul]
  exact representation_real_vectorDeterminant_zero θ f hf

end Rotation
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ContinuousCounterexampleAssembly
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous weights with the invariant-projection obstruction and their spectral properties. -/

noncomputable section
namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

theorem continuousWeight_obstruction_of_measurableOperator
    (d : BackgroundBumpData θ)
    (hstar : HasOnlyTrivialInvariantProjections (Rotation.algebra θ)
      (p.measurableOperator θ hp)) :
    HasOnlyTrivialInvariantProjections (Rotation.algebra θ)
      (Rotation.weightedReal θ
        ⟨p.continuousWeight θ d, (hp.isContinuousCircleWeight_continuousWeight d).1⟩) := by
  apply hp.continuousWeight_hasOnlyTrivialInvariantProjections d
  exact hstar

theorem exists_continuous_invariant_weight
    (hθ : Irrational θ)
    (hstar : HasOnlyTrivialInvariantProjections (Rotation.algebra θ)
      (p.measurableOperator θ hp)) :
    ∃ f : C(Circle, ℝ), IsContinuousCircleWeight f ∧
      Rotation.weightedReal θ f ∈ Rotation.algebra θ ∧
      HasOnlyTrivialInvariantProjections (Rotation.algebra θ) (Rotation.weightedReal θ f) := by
  obtain ⟨d⟩ := BackgroundCost.exists_backgroundBumpData θ hθ
  let f : C(Circle, ℝ) :=
    ⟨p.continuousWeight θ d, (hp.isContinuousCircleWeight_continuousWeight d).1⟩
  have hf : IsContinuousCircleWeight f := hp.isContinuousCircleWeight_continuousWeight d
  exact ⟨f, hf, Rotation.weightedReal_mem_algebra θ f,
    hp.continuousWeight_obstruction_of_measurableOperator d hstar⟩

end Invariant233.CircleParameterLaws

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
-- module Solutions.Q234_IR.IrrationalRotation_PrescribedAngleConditional
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
attribute [-simp] _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spectral-radius hypothesis and its consequences for prescribed irrational angles. -/

noncomputable section
open Filter
open scoped ENNReal Topology

namespace Invariant233

theorem PublishedRotationSpectralInput.normQuasinilpotent
    {θ : ℝ} (hpub : PublishedRotationSpectralInput θ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    NormQuasinilpotent (Rotation.weightedReal θ f) := by
  have h := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius
    (Rotation.weightedReal θ f)
  rw [hpub.radius_zero f hf] at h
  have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp h
  simpa only [NormQuasinilpotent, Function.comp_def, ENNReal.toReal_zero,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using ht

namespace Results

theorem prescribed_irrational_counterexample_of_published_spectral_input
    (θ : ℝ) (hθ : Irrational θ) (hpub : PublishedRotationSpectralInput θ) :
    ∃ f : C(Circle, ℝ), Rotation.IsContinuousCounterexample θ f := by
  obtain ⟨p, hp⟩ := exists_circle_parameters hθ
  obtain ⟨f, hf, hmem, hinv⟩ :=
    hp.exists_continuous_invariant_weight hθ
      (hp.measurableOperator_hasOnlyTrivialInvariantProjections hθ)
  exact ⟨f, hf, hmem, hinv, Rotation.weightedReal_ne_zero_of_isContinuousCircleWeight θ f hf,
    hpub.normQuasinilpotent f hf, Rotation.weightedReal_vectorDeterminant_zero θ f hf⟩

end Results
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_PrescribedAngle
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
attribute [-simp] _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous counterexamples for every prescribed irrational angle. -/

namespace Invariant233

theorem publishedRotationSpectralInput_of_irrational {θ : ℝ} (hθ : Irrational θ) :
    PublishedRotationSpectralInput θ := by
  refine ⟨fun f hf => ?_⟩
  rw [spectralRadius_eq_of_unital, Rotation.weightedReal_spectrum hθ f hf]
  simp

namespace Results

theorem prescribed_irrational_counterexample_oai (θ : ℝ)
    (_hθ0 : 0 < θ) (_hθ1 : θ < 1) (hθ : Irrational θ) :
    ∃ f : C(Circle, ℝ), Rotation.IsContinuousCounterexample θ f :=
  prescribed_irrational_counterexample_of_published_spectral_input θ hθ
    (publishedRotationSpectralInput_of_irrational hθ)

end Results
end Invariant233

end OAI
end

theorem solution : type_of% @OAI.Invariant233.Results.prescribed_irrational_counterexample_oai := @OAI.Invariant233.Results.prescribed_irrational_counterexample_oai
