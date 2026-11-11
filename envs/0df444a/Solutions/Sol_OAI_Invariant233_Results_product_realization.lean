-- Prove2me | solution 1 for OAI.Invariant233.Results.product_realization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:33:16.622522+00:00
-- url     : https://prove2.me/submissions/dc1ad0b3-7336-41ce-9543-22cabb597197

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
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
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Countable
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Logic.Function.Iterate
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
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
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
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
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
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
import Mathlib.Probability.Distributions.Uniform
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
import Mathlib.Tactic.Linarith
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
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Compact
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
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Sequences
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003
import Theorems.Thm_OAI_Invariant233_ProductModel_SamplingWeights_ae_all_sourceCylinder_energy_tendsto_zero
import Theorems.Thm_OAI_Invariant233_ProductModel_SamplingWeights_ae_all_source_univ_energy_tendsto_zero
import Theorems.Thm_OAI_Invariant233_ProductModel_SamplingWeights_source_hasUniformL2Marginals_of_energy_convergence
import Theorems.Thm_OAI_Invariant233_ProductModel_product_realization_of_ae_sampling

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BlockReciprocalSum
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace InvariantProjection.IndependentAngles

theorem tsum_fin_block_reciprocal {m : ℕ} (hm : 0 < m) (K : ℝ) :
    (∑' _i : Fin m, 1 / ((m : ℝ) * K)) = 1 / K := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  by_cases hK : K = 0
  · simp [hK]
  · field_simp

theorem summable_block_reciprocal (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K : ℕ → ℝ) (hK : ∀ j, 0 < K j)
    (hsum : Summable (fun j => 1 / K j)) :
    Summable (fun i : Σ j, Fin (m j) => 1 / ((m i.1 : ℝ) * K i.1)) := by
  apply (summable_sigma_of_nonneg (fun i => div_nonneg (by norm_num)
    (mul_nonneg (Nat.cast_nonneg _) (hK i.1).le))).2
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa only [tsum_fin_block_reciprocal (hm _) (K _)] using hsum

theorem tsum_block_reciprocal (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K : ℕ → ℝ) (hK : ∀ j, 0 < K j)
    (hsum : Summable (fun j => 1 / K j)) :
    (∑' i : Σ j, Fin (m j), 1 / ((m i.1 : ℝ) * K i.1)) = ∑' j, 1 / K j := by
  rw [(summable_block_reciprocal m hm K hK hsum).tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  simp only [tsum_fin_block_reciprocal (hm _) (K _)]

theorem enumerated_block_reciprocal {ι : Type*} (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K : ℕ → ℝ) (hK : ∀ j, 0 < K j)
    (hsum : Summable (fun j => 1 / K j)) (e : ι ≃ Σ j, Fin (m j)) :
    Summable (fun i => 1 / ((m (e i).1 : ℝ) * K (e i).1)) ∧
    (∑' i, 1 / ((m (e i).1 : ℝ) * K (e i).1)) = ∑' j, 1 / K j := by
  constructor
  · exact e.summable_iff.mpr (summable_block_reciprocal m hm K hK hsum)
  · calc
      (∑' i, 1 / ((m (e i).1 : ℝ) * K (e i).1)) =
          ∑' i : Σ j, Fin (m j), 1 / ((m i.1 : ℝ) * K i.1) := e.tsum_eq (fun i : Σ j, Fin (m j) => 1 / ((m i.1 : ℝ) * K i.1))
      _ = ∑' j, 1 / K j := tsum_block_reciprocal m hm K hK hsum

end InvariantProjection.IndependentAngles

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConsecutiveBlocks
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace InvariantProjection.IndependentAngles

theorem consecutiveBlocks_bijective (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) :
    Function.Bijective
      (fun i : Σ j, Fin (m j) => (∑ r ∈ Finset.range i.1, m r) + i.2.val) := by
  let d : ℕ → ℕ := fun j => ∑ r ∈ Finset.range j, m r
  have hd0 : d 0 = 0 := by simp [d]
  have hstep : ∀ j, d (j + 1) = d j + m j := fun j => Finset.sum_range_succ m j
  have hmono : Monotone d := fun j k hjk =>
    Finset.sum_le_sum_of_subset (Finset.range_mono hjk)
  have hlarge : ∀ j, j ≤ d j := by
    intro j
    induction j with
    | zero => omega
    | succ j hj =>
        have hp := hm j
        rw [hstep]
        omega
  have hgap : ∀ {j k}, j < k → d j + m j ≤ d k := by
    intro j k hjk
    rw [← hstep]
    exact hmono (by omega)
  constructor
  · rintro ⟨j, u⟩ ⟨k, v⟩ heq
    change d j + u.val = d k + v.val at heq
    have hjk : j = k := by
      rcases lt_trichotomy j k with h | h | h
      · have hg := hgap h
        have hu := u.isLt
        omega
      · exact h
      · have hg := hgap h
        have hv := v.isLt
        omega
    subst k
    have huv : u = v := Fin.ext (by omega)
    subst v
    rfl
  · intro n
    have hex : ∃ j, n < d (j + 1) := ⟨n, by have := hlarge (n + 1); omega⟩
    let j := Nat.find hex
    have hupper : n < d (j + 1) := Nat.find_spec hex
    have hlower : d j ≤ n := by
      by_cases hj : j = 0
      · simp [hj, hd0]
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
        have hn : ¬n < d (j - 1 + 1) := Nat.find_min hex (by change j - 1 < j; omega)
        have hpred : j - 1 + 1 = j := by omega
        rw [hpred] at hn
        omega
    have hi : n - d j < m j := by
      rw [hstep] at hupper
      omega
    refine ⟨⟨j, ⟨n - d j, hi⟩⟩, ?_⟩
    change d j + (n - d j) = n
    omega

theorem exists_consecutiveBlocks_equiv (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) :
    ∃ e : ℕ ≃ Σ j, Fin (m j), ∀ i : Σ j, Fin (m j),
      e.symm i = (∑ r ∈ Finset.range i.1, m r) + i.2.val := by
  let e : (Σ j, Fin (m j)) ≃ ℕ :=
    Equiv.ofBijective _ (consecutiveBlocks_bijective m hm)
  exact ⟨e.symm, fun _ => rfl⟩

end InvariantProjection.IndependentAngles

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_DominatedL2Density
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingCylinderWeak.quotient_cutCoordinates _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace Invariant233.TailTrimming

theorem exists_dominated_l2_density {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} [IsFiniteMeasure μ]
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hν : ν ≤ μ.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∃ g : Lp ℝ 2 μ,
      (∀ᵐ x ∂μ, 0 ≤ g x ∧ g x ≤ f x) ∧
      ν = μ.withDensity (fun x => ENNReal.ofReal (g x)) ∧ ‖g‖ ≤ ‖f‖ := by
  have : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) :=
    isFiniteMeasure_withDensity_ofReal ((Lp.memLp f).integrable (by norm_num)).2
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le _ hν
  have hac : ν ≪ μ := hν.absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  have hbound : ν.rnDeriv μ ≤ᵐ[μ] (fun x => ENNReal.ofReal (f x)) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv ν μ)
    intro s hs _hfinite
    exact (Measure.setLIntegral_rnDeriv_le s).trans
      ((hν s).trans_eq (withDensity_apply _ hs))
  let d : X → ℝ := fun x => (ν.rnDeriv μ x).toReal
  have hd0 (x : X) : 0 ≤ d x := ENNReal.toReal_nonneg
  have hdmeas : AEStronglyMeasurable d μ :=
    (Measure.measurable_rnDeriv ν μ).ennreal_toReal.aestronglyMeasurable
  have hdle : ∀ᵐ x ∂μ, d x ≤ f x := by
    filter_upwards [hbound, hf] with x hx hx0
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hx
    simpa only [ENNReal.toReal_ofReal hx0] using h
  have hd : MemLp d 2 μ := by
    apply (Lp.memLp f).mono' hdmeas
    filter_upwards [hdle] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hd0 x)] using hx
  let g : Lp ℝ 2 μ := hd.toLp d
  have hgeq : (fun x => g x) =ᵐ[μ] d := hd.coeFn_toLp
  refine ⟨g, ?_, ?_, ?_⟩
  · filter_upwards [hgeq, hdle] with x hx hxle
    rw [hx]
    exact ⟨ENNReal.toReal_nonneg, hxle⟩
  · calc
      ν = μ.withDensity (ν.rnDeriv μ) := (Measure.withDensity_rnDeriv_eq ν μ hac).symm
      _ = μ.withDensity (fun x => ENNReal.ofReal (g x)) := by
        apply withDensity_congr_ae
        filter_upwards [hgeq, hbound] with x hx hxb
        rw [hx]
        exact (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxb)).symm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hgeq, hdle, hf] with x hx hxle hx0
    rw [hx]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hd0 x),
      abs_of_nonneg hx0] using hxle

end Invariant233.TailTrimming

namespace Invariant233.ProductModel

theorem HasUniformL2Marginals.isFiniteMeasure {η : ℕ → Measure EndpointPair}
    (hη : HasUniformL2Marginals η) (l : ℕ) : IsFiniteMeasure (η l) := by
  obtain ⟨H, hH, hη⟩ := hη
  obtain ⟨f, g, hf0, hg0, hf, hg, hfH, hgH⟩ := hη l
  have : IsFiniteMeasure (baseMeasure.withDensity (fun x => ENNReal.ofReal (f x))) :=
    isFiniteMeasure_withDensity_ofReal ((Lp.memLp f).integrable (by norm_num)).2
  have : IsFiniteMeasure ((η l).map Prod.fst) := by
    rw [hf]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact Measure.isFiniteMeasure_of_map measurable_fst.aemeasurable

theorem HasUniformL2Marginals.mono {η ζ : ℕ → Measure EndpointPair}
    (hη : HasUniformL2Marginals η) (hζ : ∀ l, ζ l ≤ η l) :
    HasUniformL2Marginals ζ := by
  obtain ⟨H, hH, hη⟩ := hη
  refine ⟨H, hH, ?_⟩
  intro l
  obtain ⟨f, g, hf0, hg0, hf, hg, hfH, hgH⟩ := hη l
  have hfst : (ζ l).map Prod.fst ≤
      baseMeasure.withDensity (fun x => ENNReal.ofReal (f x)) := by
    rw [← hf]
    exact Measure.map_mono (hζ l) measurable_fst
  have hsnd : (ζ l).map Prod.snd ≤
      baseMeasure.withDensity (fun x => ENNReal.ofReal (g x)) := by
    rw [← hg]
    exact Measure.map_mono (hζ l) measurable_snd
  obtain ⟨f', hf'0, hf', hf'norm⟩ :=
    Invariant233.TailTrimming.exists_dominated_l2_density f hf0 hfst
  obtain ⟨g', hg'0, hg', hg'norm⟩ :=
    Invariant233.TailTrimming.exists_dominated_l2_density g hg0 hsnd
  exact ⟨f', g', hf'0.mono (fun _ h => h.1), hg'0.mono (fun _ h => h.1),
    hf', hg', hf'norm.trans hfH, hg'norm.trans hgH⟩

theorem HasUniformL2Marginals.restrict {η : ℕ → Measure EndpointPair}
    (hη : HasUniformL2Marginals η) (S : ℕ → Set EndpointPair) :
    HasUniformL2Marginals (fun l => (η l).restrict (S l)) :=
  hη.mono (fun _ => Measure.restrict_le_self)

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedShiftHalfline
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.WeightedShift

@[simp] theorem tailWeight_apply (m k : ℤ) :
    tailWeight m k = if m ≤ k then 1 else 0 := rfl

@[simp] theorem tailProjection_apply (m : ℤ) (ξ : Hilbert) (k : ℤ) :
    tailProjection m ξ k = if m ≤ k then ξ k else 0 := by
  change (if m ≤ k then (1 : ℂ) else 0) * ξ k = _
  split_ifs <;> simp

@[simp] theorem tailProjection_mul_self (m : ℤ) :
    tailProjection m * tailProjection m = tailProjection m := by
  ext ξ k
  simp only [mul_apply_eq_comp, tailProjection_apply]
  split_ifs <;> rfl

@[simp] theorem tailProjection_star (m : ℤ) :
    star (tailProjection m) = tailProjection m := by
  change star (diagonal (tailWeight m)) = diagonal (tailWeight m)
  rw [← diagonal_star]
  congr 1
  ext k
  simp only [lp.coeFn_star, Pi.star_apply, tailWeight_apply]
  split_ifs <;> simp

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_OrdinaryTailSubspaces
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.WeightedShift

@[simp] theorem tailProjection_single (m k : ℤ) (z : ℂ) :
    tailProjection m (lp.single 2 k z) =
      if m ≤ k then lp.single 2 k z else 0 := by
  ext j
  by_cases hj : j = k
  · subst j
    by_cases hk : m ≤ k <;> simp [tailProjection_apply, hk]
  · by_cases hk : m ≤ k <;> simp [tailProjection_apply, lp.single_apply, hj, hk]

end Invariant233.WeightedShift

end

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

theorem tsum_tail_le_of_half_decay {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hstep : ∀ n, a (n + 1) ≤ a n / 2) (j : ℕ) :
    (∑' n : ℕ, a (j + n)) ≤ 2 * a j := by
  have hs : Summable (fun n : ℕ => a (j + n)) :=
    summable_of_half_decay (fun n => ha (j + n))
      (fun n => by simpa only [Nat.add_assoc] using hstep (j + n))
  calc
    (∑' n : ℕ, a (j + n)) ≤ ∑' n : ℕ, a j * (1 / 2 : ℝ) ^ n :=
      hs.tsum_le_tsum (half_decay_iterate hstep j)
        (summable_geometric_two.mul_left (a j))
    _ = 2 * a j := by rw [tsum_mul_left, tsum_geometric_two]; ring

theorem reciprocal_tail_bound {K : ℕ → ℝ} (hK : ∀ n, 0 < K n)
    (hdouble : ∀ n, 2 * K n ≤ K (n + 1)) (j : ℕ) :
    (∑' n : ℕ, 1 / K (j + 1 + n)) ≤ 2 / K (j + 1) := by
  simpa only [div_eq_mul_inv, one_mul] using
    tsum_tail_le_of_half_decay (fun n => le_of_lt (one_div_pos.mpr (hK n)))
      (reciprocal_half_decay hK hdouble) (j + 1)

end Invariant233.ParameterTails

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSampling
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

lemma delta_nonneg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 0 ≤ delta s := by
  exact le_min hs.1 (sub_nonneg.mpr hs.2)

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarEndpointKernelBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

end Invariant233.ScalarSampling

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

theorem quarter_le_card_interval {Q : ℝ} (hQ : 4 ≤ Q) :
    Q / 4 ≤ ((Finset.Icc (⌈Q / 2⌉ : ℤ) ⌊Q⌋).card : ℝ) := by
  have hi : (⌊Q⌋ : ℤ) + 1 - ⌈Q / 2⌉ ≤
      ((Finset.Icc (⌈Q / 2⌉ : ℤ) ⌊Q⌋).card : ℤ) := by
    rw [Int.card_Icc]
    exact Int.self_le_toNat _
  have hr : (⌊Q⌋ : ℝ) + 1 - (⌈Q / 2⌉ : ℝ) ≤
      ((Finset.Icc (⌈Q / 2⌉ : ℤ) ⌊Q⌋).card : ℝ) := by exact_mod_cast hi
  have hf := Int.lt_floor_add_one Q
  have hc := Int.ceil_lt_add_one (Q / 2)
  linarith

theorem eventually_exists_sampling_powers :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, N ≤ m ^ 2 →
      ∃ t : Finset ℤ,
        (∀ n ∈ t, (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n ∧
          (n : ℝ) ≤ (m : ℝ) ^ ((7 / 10 : ℝ) * m)) ∧
        (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (t.card : ℝ) ∧
        (∀ n ∈ t, 0 < n) ∧
        ∀ n ∈ t, ∀ n' ∈ t, n ≠ n' → ∀ v v' : ℤ,
          |v| ≤ (m ^ 300 : ℕ) → |v'| ≤ (m ^ 300 : ℕ) →
          (v ≠ 0 ∨ v' ≠ 0) → (N * m ^ 1000 : ℕ) < |v * n + v' * n'| := by
  have hm : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hcount := eventually_power_gap hm 112 (69 / 100) (7 / 10) 1602 (by norm_num)
  have hgrowth := eventually_power_gap hm 4 0 (7 / 10) 1002 (by norm_num)
  filter_upwards [hcount, hgrowth, eventually_ge_atTop 20] with m hcount hgrowth hm20
  intro N hN
  have hmone : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let Q : ℝ := (m : ℝ) ^ ((7 / 10 : ℝ) * m)
  let s : Finset ℤ := Finset.Icc (⌈Q / 2⌉ : ℤ) ⌊Q⌋
  have hQpos : 0 < Q := Real.rpow_pos_of_pos hmpos _
  have hQlarge : 4 ≤ Q := by
    have hp : 1 ≤ (m : ℝ) ^ (1002 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hmone) (by norm_num)
    simp only [zero_mul, Real.rpow_zero, mul_one] at hgrowth
    dsimp [Q]
    linarith
  have hR : N * m ^ 1000 ≤ m ^ 1002 := by
    calc
      N * m ^ 1000 ≤ m ^ 2 * m ^ 1000 := Nat.mul_le_mul_right _ hN
      _ = m ^ 1002 := by rw [← pow_add]
  have hRreal : (N * m ^ 1000 : ℕ) ≤ (m : ℝ) ^ (1002 : ℝ) := by
    rw [show (1002 : ℝ) = ((1002 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact_mod_cast hR
  have hRlt : ((N * m ^ 1000 : ℕ) : ℝ) < Q / 2 := by
    have hp := Real.rpow_pos_of_pos hmpos (1002 : ℝ)
    simp only [zero_mul, Real.rpow_zero, mul_one] at hgrowth
    dsimp [Q]
    linarith
  have hinterval : ∀ n ∈ s, Q / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ Q := by
    intro n hn
    have hmem := Finset.mem_Icc.mp hn
    constructor
    · exact (Int.le_ceil (Q / 2)).trans (by exact_mod_cast hmem.1)
    · exact (show (n : ℝ) ≤ (⌊Q⌋ : ℝ) by exact_mod_cast hmem.2).trans (Int.floor_le Q)
  obtain ⟨t, hts, hcard, hsep⟩ :=
    exists_frequency_separated_subset s (m ^ 300) (N * m ^ 1000) (by
      intro n hn
      have h := hRlt.trans_le (hinterval n hn).1
      exact_mod_cast h)
  have hcardreal : (s.card : ℝ) ≤ (t.card : ℝ) *
      (((2 * m ^ 300 + 1) ^ 2 * (2 * (N * m ^ 1000) + 1) + 1 : ℕ) : ℝ) :=
    by exact_mod_cast hcard
  have hbudget : (((2 * m ^ 300 + 1) ^ 2 * (2 * (N * m ^ 1000) + 1) + 1 : ℕ) : ℝ) ≤
      28 * (m : ℝ) ^ (1602 : ℝ) := by
    rw [show (1602 : ℝ) = ((1602 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact_mod_cast deletion_budget_le hmone hN
  have hcountlower : 28 * (m : ℝ) ^ (1602 : ℝ) *
      (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (s.card : ℝ) := by
    have hc := quarter_le_card_interval hQlarge
    change Q / 4 ≤ (s.card : ℝ) at hc
    dsimp [Q] at hc
    linarith
  have hselected : (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (t.card : ℝ) := by
    have hbound := hcardreal.trans (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg t.card))
    have hp : 0 < 28 * (m : ℝ) ^ (1602 : ℝ) := by positivity
    apply le_of_mul_le_mul_left _ hp
    calc
      28 * (m : ℝ) ^ (1602 : ℝ) * (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤
          (s.card : ℝ) := hcountlower
      _ ≤ 28 * (m : ℝ) ^ (1602 : ℝ) * (t.card : ℝ) := by
        simpa only [mul_comm] using hbound
  refine ⟨t, (fun n hn => hinterval n (hts hn)), hselected, ?_, hsep⟩
  intro n hn
  have h := (half_pos hQpos).trans_le (hinterval n (hts hn)).1
  exact_mod_cast h

theorem eventually_exists_nat_sampling_powers :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, N ≤ m ^ 2 →
      ∃ t : Finset ℕ,
        (∀ n ∈ t, (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n ∧
          (n : ℝ) ≤ (m : ℝ) ^ ((7 / 10 : ℝ) * m)) ∧
        (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (t.card : ℝ) ∧
        (∀ n ∈ t, 0 < n) ∧
        ∀ n ∈ t, ∀ n' ∈ t, n ≠ n' → ∀ v v' : ℤ,
          |v| ≤ (m ^ 300 : ℕ) → |v'| ≤ (m ^ 300 : ℕ) →
          (v ≠ 0 ∨ v' ≠ 0) →
          (N * m ^ 1000 : ℕ) < |v * (n : ℤ) + v' * (n' : ℤ)| := by
  classical
  filter_upwards [eventually_exists_sampling_powers] with m hm
  intro N hN
  obtain ⟨t, hrange, hcard, hpos, hsep⟩ := hm N hN
  have hcast : ∀ n ∈ t, (n.toNat : ℤ) = n := by
    intro n hn
    exact Int.toNat_of_nonneg (hpos n hn).le
  have hcastReal : ∀ n ∈ t, (n.toNat : ℝ) = (n : ℝ) := by
    intro n hn
    exact_mod_cast hcast n hn
  have hcardImage : (t.image Int.toNat).card = t.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have h := congrArg (fun n : ℕ => (n : ℤ)) hab
    simpa only [hcast a ha, hcast b hb] using h
  refine ⟨t.image Int.toNat, ?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
    simpa only [hcastReal z hz] using hrange z hz
  · simpa only [hcardImage] using hcard
  · intro n hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
    have hzpos := hpos z hz
    omega
  · intro n hn n' hn' hne v v' hv hv' hvv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hn'
    have hzz : z ≠ z' := by intro h; exact hne (congrArg Int.toNat h)
    simpa only [hcast z hz, hcast z' hz'] using hsep z hz z' hz' hzz v v' hv hv' hvv

end Invariant233.SeparatedPowers

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_SquaredIntegralLp
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.SquaredIntegralLp

theorem eLpNorm'_two_eq_lintegral_sq_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) :
    eLpNorm' f 2 μ = (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm'_eq_lintegral_enorm]
  congr 1
  apply lintegral_congr
  intro x
  rw [ENNReal.rpow_two, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
  rw [sq_abs]

theorem eLpNorm_two_eq_lintegral_sq_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hfm : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]
  simpa only [ENNReal.toReal_ofNat] using eLpNorm'_two_eq_lintegral_sq_rpow μ f

theorem eLpNorm_two_eq_ofReal_integral_sq_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hfm : AEStronglyMeasurable f μ)
    (hf : Integrable (fun x => f x ^ 2) μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_two_eq_lintegral_sq_rpow μ f hfm,
    ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall fun x => sq_nonneg (f x))]

theorem tendsto_eLpNorm_two_of_integral_sq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : ℕ → X → ℝ) (g : Y → ℝ)
    (hfm : ∀ index, AEStronglyMeasurable (f index) μ)
    (hgm : AEStronglyMeasurable g ν)
    (hf : ∀ n, Integrable (fun x => f n x ^ 2) μ)
    (hg : Integrable (fun y => g y ^ 2) ν)
    (h : Tendsto (fun n => ∫ x, f n x ^ 2 ∂μ) atTop
      (𝓝 (∫ y, g y ^ 2 ∂ν))) :
    Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 (eLpNorm g 2 ν)) := by
  have hreal := (ENNReal.continuous_ofReal.tendsto _).comp h
  have hp := hreal.ennrpow_const (1 / 2 : ℝ)
  simpa only [eLpNorm_two_eq_ofReal_integral_sq_rpow μ _ (hfm _) (hf _),
    eLpNorm_two_eq_ofReal_integral_sq_rpow ν _ hgm hg, Function.comp_def] using hp

end Invariant233.SquaredIntegralLp

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TriangularLawMass
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace Invariant233.ProductModel

theorem measurePreserving_finite_coordinate_pairs (I : Finset ℕ) :
    MeasurePreserving
      (fun xz : EndpointPair => fun i : I => (xz.1 i, xz.2 i))
      (baseMeasure.prod baseMeasure)
      (Measure.pi (fun _ : I => circleMeasure.prod circleMeasure)) := by
  have hr : MeasurePreserving I.restrict baseMeasure
      (Measure.pi (fun _ : I => circleMeasure)) := by
    refine ⟨Finset.measurable_restrict I, ?_⟩
    exact infinitePi_map_restrict (fun _ : ℕ => circleMeasure)
  let e := MeasurableEquiv.arrowProdEquivProdArrow Circle Circle I
  have he := (measurePreserving_arrowProdEquivProdArrow Circle Circle I
    (fun _ => circleMeasure) (fun _ => circleMeasure)).symm
  exact he.comp (hr.prod hr)

end Invariant233.ProductModel

end

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TriangularMarginals
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace Invariant233.ProductModel

private theorem rep_preserving : MeasurePreserving circleRepresentative circleMeasure
    (volume.restrict (Ico (0 : ℝ) 1)) :=
  CocycleSupport.measurePreserving_circleRepresentative

theorem circleRepresentative_upper_tail (r : ℝ) (hr : 0 ≤ r) :
    circleMeasure {x | r < circleRepresentative x} = ENNReal.ofReal (1 - r) := by
  change circleMeasure (circleRepresentative ⁻¹' Ioi r) = _
  rw [rep_preserving.measure_preimage measurableSet_Ioi.nullMeasurableSet,
    Measure.restrict_apply measurableSet_Ioi]
  have hset : Ioi r ∩ Ico (0 : ℝ) 1 = Ioo r 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Ico, mem_Ioo]
    constructor
    · tauto
    · intro hx
      exact ⟨hx.1, le_trans hr hx.1.le, hx.2⟩
  rw [hset, Real.volume_Ioo]

theorem circleRepresentative_lower_tail (r : ℝ) (hr : r ≤ 1) :
    circleMeasure {x | circleRepresentative x < r} = ENNReal.ofReal r := by
  change circleMeasure (circleRepresentative ⁻¹' Iio r) = _
  rw [rep_preserving.measure_preimage measurableSet_Iio.nullMeasurableSet,
    Measure.restrict_apply measurableSet_Iio]
  have hset : Iio r ∩ Ico (0 : ℝ) 1 = Ico 0 r := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ico]
    constructor
    · tauto
    · intro hx
      exact ⟨hx.2, hx.1, lt_of_lt_of_le hx.2 hr⟩
  rw [hset, Real.volume_Ico, sub_zero]

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TrimmingWeakLimits
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Topology BoundedContinuousFunction
open scoped ENNReal NNReal

namespace Invariant233.TrimmingWeakLimits

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

omit [OpensMeasurableSpace X] in

theorem testAgainstNN_add_measure (μ ν : FiniteMeasure X) (f : X →ᵇ ℝ≥0) :
    (μ + ν).testAgainstNN f = μ.testAgainstNN f + ν.testAgainstNN f := by
  simp only [← ENNReal.coe_inj, ENNReal.coe_add, FiniteMeasure.testAgainstNN_coe_eq,
    FiniteMeasure.toMeasure_add, lintegral_add_measure]

theorem tendsto_of_add_eq_of_mass_tendsto_zero {I : Type*} {l : Filter I}
    {μn βn δn : I → FiniteMeasure X} {μ : FiniteMeasure X}
    (hμ : Tendsto μn l (𝓝 μ)) (hsplit : ∀ i, βn i + δn i = μn i)
    (hlost : Tendsto (fun i => (δn i).mass) l (𝓝 0)) :
    Tendsto βn l (𝓝 μ) := by
  apply FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto.mpr
  intro f
  have hmain := FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto.mp hμ f
  have hsmall := FiniteMeasure.tendsto_zero_testAgainstNN_of_tendsto_zero_mass hlost f
  have heq : (fun i => (βn i).testAgainstNN f) =
      (fun i => (μn i).testAgainstNN f - (δn i).testAgainstNN f) := by
    funext i
    rw [← hsplit i, testAgainstNN_add_measure, add_tsub_cancel_right]
  rw [heq]
  simpa only [tsub_zero] using hmain.sub hsmall

theorem tendsto_restrict_of_compl_mass_tendsto_zero {I : Type*} {l : Filter I}
    {μn : I → FiniteMeasure X} {μ : FiniteMeasure X}
    (hμ : Tendsto μn l (𝓝 μ)) (A : I → Set X)
    (hA : ∀ i, MeasurableSet (A i))
    (hlost : Tendsto (fun i => μn i (A i)ᶜ) l (𝓝 0)) :
    Tendsto (fun i => (μn i).restrict (A i)) l (𝓝 μ) := by
  apply tendsto_of_add_eq_of_mass_tendsto_zero hμ
    (δn := fun i => (μn i).restrict (A i)ᶜ)
  · intro i
    simpa only [union_compl_self, FiniteMeasure.restrict_univ] using
      (FiniteMeasure.restrict_union (μ := μn i) disjoint_compl_right (hA i).compl).symm
  · simpa only [FiniteMeasure.restrict_mass] using hlost

end Invariant233.TrimmingWeakLimits

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_VaryingMapWeakLimit
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace Invariant233.VaryingMapWeakLimit

variable {X Y : Type*} [MeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]

theorem tendsto_map_of_ae_tendsto (μ : FiniteMeasure X)
    (f : ℕ → X → Y) (g : X → Y)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hlim : ∀ᵐ x ∂(μ : Measure X), Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => μ.map (f n)) atTop (𝓝 (μ.map g)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro φ
  have hi := tendsto_integral_of_dominated_convergence (μ := (μ : Measure X))
    (fun _ => ‖φ‖)
    (fun n => (φ.continuous.measurable.comp (hf n)).aestronglyMeasurable)
    (integrable_const ‖φ‖)
    (fun n => Filter.Eventually.of_forall (fun x => φ.norm_coe_le_norm (f n x)))
    (hlim.mono (fun x hx => φ.continuous.continuousAt.tendsto.comp hx))
  simpa only [Function.comp_def, FiniteMeasure.toMeasure_map,
    integral_map (hf _).aemeasurable φ.continuous.aestronglyMeasurable,
    integral_map hg.aemeasurable φ.continuous.aestronglyMeasurable] using hi

theorem tendsto_map_restrict_of_ae_tendsto (μ : FiniteMeasure X)
    (f : ℕ → X → Y) (g : X → Y)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hlim : ∀ᵐ x ∂(μ : Measure X), Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n))
    (hlost : Tendsto (fun n => μ (A n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => (μ.restrict (A n)).map (f n)) atTop (𝓝 (μ.map g)) := by
  apply TrimmingWeakLimits.tendsto_of_add_eq_of_mass_tendsto_zero
    (tendsto_map_of_ae_tendsto μ f g hf hg hlim)
    (δn := fun n => (μ.restrict (A n)ᶜ).map (f n))
  · intro n
    rw [← FiniteMeasure.map_add (hf n)]
    congr 1
    simpa only [union_compl_self, FiniteMeasure.restrict_univ] using
      (FiniteMeasure.restrict_union (μ := μ) disjoint_compl_right (hA n).compl).symm
  · simpa only [FiniteMeasure.mass, FiniteMeasure.map_apply _ (hf _) MeasurableSet.univ,
      preimage_univ, FiniteMeasure.restrict_apply μ _ MeasurableSet.univ,
      univ_inter] using hlost

end Invariant233.VaryingMapWeakLimit

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

end Invariant233.ProductCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSampling
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory Set
open scoped ENNReal Topology BigOperators

namespace Invariant233.ProductModel.Sampling

theorem representative_mem_Ico (x : Circle) : circleRepresentative x ∈ Ico (0 : ℝ) 1 := by
  simpa [circleRepresentative] using (AddCircle.equivIco (1 : ℝ) 0 x).property

theorem triangularEvent_measurable (I : Finset ℕ) : MeasurableSet (triangularEvent I) := by
  unfold triangularEvent
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _hi
  exact measurableSet_lt
    (representative_measurable.comp ((measurable_pi_apply i).comp measurable_fst))
    (representative_measurable.comp ((measurable_pi_apply i).comp measurable_snd))

theorem triangularLaw_finite (I : Finset ℕ) : IsFiniteMeasure (triangularLaw I) := by
  unfold triangularLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem circleMeasure_singleton (x : Circle) : circleMeasure {x} = 0 := by
  simpa [circleMeasure, Metric.closedBall_zero] using
    (AddCircle.volume_closedBall (1 : ℝ) (x := x) 0)

theorem representative_map_haar :
    circleMeasure.map circleRepresentative = volume.restrict (Ico (0 : ℝ) 1) := by
  exact CocycleSupport.measurePreserving_circleRepresentative.map_eq

theorem representative_tail_measure {a : ℝ} (ha0 : 0 ≤ a) (_ha1 : a ≤ 1) :
    circleMeasure {x | a < circleRepresentative x} = ENNReal.ofReal (1 - a) := by
  exact Invariant233.ProductModel.circleRepresentative_upper_tail a ha0

theorem representative_initial_measure {a : ℝ} (_ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    circleMeasure {x | circleRepresentative x < a} = ENNReal.ofReal a := by
  exact Invariant233.ProductModel.circleRepresentative_lower_tail a ha1

end Invariant233.ProductModel.Sampling

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
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductTailTrimming
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Invariant233.ProductModel.TailTrimming

theorem fract_add_eq_fract_add_fract (u t : ℝ) :
    Int.fract (u + t) = Int.fract (u + Int.fract t) := by
  conv_lhs => rw [← Int.floor_add_fract t]
  rw [show u + ((⌊t⌋ : ℝ) + Int.fract t) =
    (u + Int.fract t) + (⌊t⌋ : ℝ) by ring]
  exact Int.fract_add_intCast _ _

theorem fract_add_lt_iff {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) (t : ℝ) :
    Int.fract (u + t) < u ↔ 1 - Int.fract t ≤ u := by
  rw [fract_add_eq_fract_add_fract]
  have hr0 := Int.fract_nonneg t
  have hr1 := Int.fract_lt_one t
  by_cases h : u + Int.fract t < 1
  · have hf : ⌊u + Int.fract t⌋ = (0 : ℤ) :=
      Int.floor_eq_zero_iff.mpr ⟨add_nonneg hu.1 hr0, h⟩
    rw [Int.fract, hf, Int.cast_zero, sub_zero]
    constructor <;> intro hh <;> linarith
  · have hf : ⌊u + Int.fract t⌋ = (1 : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num <;> linarith [hu.2]
    rw [Int.fract, hf, Int.cast_one]
    constructor <;> intro hh <;> linarith

theorem uniform_wrap_measure (t : ℝ) :
    (volume.restrict (Ico (0 : ℝ) 1)) {u : ℝ | Int.fract (u + t) < u} =
      ENNReal.ofReal (Int.fract t) := by
  have hm : MeasurableSet {u : ℝ | Int.fract (u + t) < u} :=
    measurableSet_lt ((measurable_id.add_const t).fract) measurable_id
  rw [Measure.restrict_apply hm]
  have heq : {u : ℝ | Int.fract (u + t) < u} ∩ Ico 0 1 =
      Ico (1 - Int.fract t) 1 := by
    ext u
    constructor
    · rintro ⟨h, hu⟩
      exact ⟨(fract_add_lt_iff hu t).mp h, hu.2⟩
    · rintro ⟨hl, hr⟩
      have hu : u ∈ Ico (0 : ℝ) 1 :=
        ⟨by linarith [Int.fract_lt_one t], hr⟩
      exact ⟨(fract_add_lt_iff hu t).mpr hl, hu⟩
  rw [heq, Real.volume_Ico]
  congr 1
  ring

theorem coordinateOrderFailure_measure (θ : ℕ → ℝ) (n i : ℕ) :
    baseMeasure (coordinateOrderFailure θ n i) =
      ENNReal.ofReal (Int.fract ((n : ℝ) * θ i)) := by
  have hmp := CocycleSupport.measurePreserving_productRepresentative (ι := ℕ) i
  have hm : MeasurableSet {u : ℝ | Int.fract (u + (n : ℝ) * θ i) < u} :=
    measurableSet_lt ((measurable_id.add_const _).fract) measurable_id
  have heq : coordinateOrderFailure θ n i =
      (fun x : Base => circleRepresentative (x i)) ⁻¹'
        {u : ℝ | Int.fract (u + (n : ℝ) * θ i) < u} := by
    ext x
    simp only [coordinateOrderFailure, rotationIterate, Set.mem_ofPred_eq,
      Int.cast_natCast, Set.mem_preimage]
    exact Iff.of_eq (congrArg (fun r : ℝ => r < circleRepresentative (x i))
      (ProductCocycle.representative_add (x i) ((n : ℝ) * θ i)))
  rw [heq]
  change (Measure.infinitePi (fun _ : ℕ => (volume : Measure UnitAddCircle))) _ = _
  exact (hmp.measure_preimage hm.nullMeasurableSet).trans (uniform_wrap_measure _)

theorem tailOrderFailure_measure_le (I : Finset ℕ) (θ : ℕ → ℝ) (n : ℕ) :
    baseMeasure (tailOrderFailure I θ n) ≤
      ∑' i : {i : ℕ // i ∉ I}, ENNReal.ofReal (Int.fract ((n : ℝ) * θ i)) := by
  exact (measure_iUnion_le _).trans_eq
    (tsum_congr (fun i => coordinateOrderFailure_measure θ n i))

theorem tailOrderFailure_measure_le_angles (I : Finset ℕ) (θ : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (n : ℕ) :
    baseMeasure (tailOrderFailure I θ n) ≤
      ∑' i : {i : ℕ // i ∉ I}, ENNReal.ofReal ((n : ℝ) * θ i) := by
  refine (tailOrderFailure_measure_le I θ n).trans (ENNReal.tsum_le_tsum ?_)
  intro i
  apply ENNReal.ofReal_le_ofReal
  have hf : (0 : ℤ) ≤ ⌊(n : ℝ) * θ i⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg n) (hθ i))
  have hf' : (0 : ℝ) ≤ (⌊(n : ℝ) * θ i⌋ : ℝ) := by exact_mod_cast hf
  rw [Int.fract]
  linarith

theorem indepFun_coordinate_restrictions (S T : Set ℕ) (hST : Disjoint S T) :
    IndepFun (fun x : Base => fun i : S => x i)
      (fun x : Base => fun i : T => x i) baseMeasure := by
  have hi : iIndepFun (fun i (x : Base) => x i) baseMeasure :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have h := indep_iSup_of_disjoint
    (fun i : ℕ => (measurable_pi_apply i : Measurable (fun x : Base => x i)).comap_le)
    hi hST
  change Indep (MeasurableSpace.comap (fun x : Base => fun i : S => x i) inferInstance)
    (MeasurableSpace.comap (fun x : Base => fun i : T => x i) inferInstance) baseMeasure
  simp_rw [MeasurableSpace.comap_process_pi]
  simpa only [iSup_subtype] using h

theorem withDensity_tail_event (I : Finset ℕ)
    (w : (I → Circle) → ℝ≥0∞) (hw : Measurable w)
    (B : Set ({i : ℕ // i ∉ I} → Circle)) (hB : MeasurableSet B) :
    (baseMeasure.withDensity (fun x : Base => w (fun i : I => x i)))
        ((fun x : Base => fun i : {i : ℕ // i ∉ I} => x i) ⁻¹' B) =
      (baseMeasure.withDensity (fun x : Base => w (fun i : I => x i))) univ *
        baseMeasure ((fun x : Base => fun i : {i : ℕ // i ∉ I} => x i) ⁻¹' B) := by
  let P : Base → (I → Circle) := fun x i => x i
  let Q : Base → ({i : ℕ // i ∉ I} → Circle) := fun x i => x i
  have hP : Measurable P := by fun_prop
  have hQ : Measurable Q := by fun_prop
  have hpre : MeasurableSet (Q ⁻¹' B) := hQ hB
  have hind : IndepFun P Q baseMeasure :=
    indepFun_coordinate_restrictions (I : Set ℕ) (I : Set ℕ)ᶜ disjoint_compl_right
  have hind' := hind.comp hw (measurable_const.indicator hB :
    Measurable (B.indicator (fun _ => (1 : ℝ≥0∞))))
  have hh := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (hw.comp hP) ((measurable_const.indicator hB).comp hQ) hind'
  have heq : (fun x : Base => w (P x) * B.indicator (fun _ => (1 : ℝ≥0∞)) (Q x)) =
      (Q ⁻¹' B).indicator (fun x => w (P x)) := by
    funext x
    by_cases hx : Q x ∈ B <;> simp [hx]
  have heq1 : (fun x : Base => B.indicator (fun _ => (1 : ℝ≥0∞)) (Q x)) =
      (Q ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : Q x ∈ B <;> simp [hx]
  change (∫⁻ x, w (P x) * B.indicator (fun _ => (1 : ℝ≥0∞)) (Q x) ∂baseMeasure) =
    (∫⁻ x, w (P x) ∂baseMeasure) *
      (∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) (Q x) ∂baseMeasure) at hh
  rw [heq, heq1, lintegral_indicator hpre, lintegral_indicator_const hpre, one_mul] at hh
  change (baseMeasure.withDensity (fun x => w (P x))) (Q ⁻¹' B) =
    (baseMeasure.withDensity (fun x => w (P x))) univ * baseMeasure (Q ⁻¹' B)
  simpa only [withDensity_apply _ hpre,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hh

theorem weighted_tailOrderFailure_eq (I : Finset ℕ) (θ : ℕ → ℝ) (n : ℕ)
    (w : (I → Circle) → ℝ≥0∞) (hw : Measurable w) :
    (baseMeasure.withDensity (fun x : Base => w (fun i : I => x i)))
        (tailOrderFailure I θ n) =
      (baseMeasure.withDensity (fun x : Base => w (fun i : I => x i))) univ *
        baseMeasure (tailOrderFailure I θ n) := by
  let B : Set ({i : ℕ // i ∉ I} → Circle) :=
    ⋃ i : {i : ℕ // i ∉ I},
      {y | circleRepresentative (y i + ((n : ℝ) * θ i : ℝ)) <
        circleRepresentative (y i)}
  have hr : Measurable circleRepresentative := ProductCocycle.measurable_representative
  have hB : MeasurableSet B := by
    apply MeasurableSet.iUnion
    intro i
    exact measurableSet_lt (hr.comp ((measurable_pi_apply i).add_const _))
      (hr.comp (measurable_pi_apply i))
  have heq : tailOrderFailure I θ n =
      (fun x : Base => fun i : {i : ℕ // i ∉ I} => x i) ⁻¹' B := by
    ext x
    simp only [tailOrderFailure, coordinateOrderFailure, B, rotationIterate,
      mem_iUnion, mem_ofPred_eq, mem_preimage, Int.cast_natCast]
  rw [heq]
  exact withDensity_tail_event I w hw B hB

theorem weighted_tailOrderFailure_le (I : Finset ℕ) (θ : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (n : ℕ)
    (w : (I → Circle) → ℝ≥0∞) (hw : Measurable w) :
    (baseMeasure.withDensity (fun x : Base => w (fun i : I => x i)))
        (tailOrderFailure I θ n) ≤
      (baseMeasure.withDensity (fun x : Base => w (fun i : I => x i))) univ *
        (ENNReal.ofReal (n : ℝ) * ∑' i : {i : ℕ // i ∉ I}, ENNReal.ofReal (θ i)) := by
  rw [weighted_tailOrderFailure_eq I θ n w hw]
  apply mul_le_mul_right
  convert tailOrderFailure_measure_le_angles I θ hθ n using 1
  all_goals try with_reducible_and_instances rfl
  simp_rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.tsum_mul_left]

theorem not_mem_tailOrderFailure_iff (I : Finset ℕ) (θ : ℕ → ℝ) (n : ℕ) (x : Base) :
    x ∉ tailOrderFailure I θ n ↔
      ∀ i, i ∉ I → circleRepresentative (x i) ≤
        circleRepresentative (rotationIterate θ (n : ℤ) x i) := by
  simp only [tailOrderFailure, coordinateOrderFailure, mem_iUnion,
    mem_ofPred_eq, not_exists, not_lt, Subtype.forall]

theorem measurable_orbitPairMap (θ : ℕ → ℝ) (n : ℕ) :
    Measurable (orbitPairMap θ n) := by
  apply measurable_id.prodMk
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply i).add_const _

theorem measurableSet_orderedPairEvent : MeasurableSet orderedPairEvent := by
  have hr : Measurable circleRepresentative := ProductCocycle.measurable_representative
  simp only [orderedPairEvent, Ordered, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (hr.comp ((measurable_pi_apply i).comp measurable_fst))
    (hr.comp ((measurable_pi_apply i).comp measurable_snd))

theorem orbitPairMeasure_mass (θ : ℕ → ℝ) (n : ℕ) (w : Base → ℝ≥0∞) :
    orbitPairMeasure θ n w univ = (baseMeasure.withDensity w) univ := by
  rw [orbitPairMeasure, Measure.map_apply (measurable_orbitPairMap θ n) MeasurableSet.univ]
  simp

theorem orbitPairMeasure_unordered_le (I : Finset ℕ) (θ : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (n : ℕ)
    (w : (I → Circle) → ℝ≥0∞) (hw : Measurable w)
    (hprefix : ∀ᵐ x ∂baseMeasure.withDensity (fun x : Base => w (fun i : I => x i)),
      ∀ i ∈ I, circleRepresentative (x i) ≤
        circleRepresentative (rotationIterate θ (n : ℤ) x i)) :
    orbitPairMeasure θ n (fun x : Base => w (fun i : I => x i)) orderedPairEventᶜ ≤
      orbitPairMeasure θ n (fun x : Base => w (fun i : I => x i)) univ *
        (ENNReal.ofReal (n : ℝ) * ∑' i : {i : ℕ // i ∉ I}, ENNReal.ofReal (θ i)) := by
  rw [orbitPairMeasure_mass]
  refine le_trans ?_ (weighted_tailOrderFailure_le I θ hθ n w hw)
  rw [orbitPairMeasure, Measure.map_apply (measurable_orbitPairMap θ n)
    measurableSet_orderedPairEvent.compl]
  apply measure_mono_ae
  filter_upwards [hprefix] with x hx
  intro hbad
  by_contra htail
  have ht := (not_mem_tailOrderFailure_iff I θ n x).mp htail
  apply hbad
  change Ordered x (rotationIterate θ (n : ℤ) x)
  intro i
  by_cases hi : i ∈ I
  · exact hx i hi
  · exact ht i hi

theorem orbitAverageMeasure_unordered_le (I N : Finset ℕ) (θ : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (M : ℕ) (hN : ∀ n ∈ N, n ≤ M)
    (w : ℕ → (I → Circle) → ℝ≥0∞) (hw : ∀ n ∈ N, Measurable (w n))
    (hprefix : ∀ n ∈ N,
      ∀ᵐ x ∂baseMeasure.withDensity (fun x : Base => w n (fun i : I => x i)),
        ∀ i ∈ I, circleRepresentative (x i) ≤
          circleRepresentative (rotationIterate θ (n : ℤ) x i)) :
    orbitAverageMeasure θ N (fun n x => w n (fun i : I => x i)) orderedPairEventᶜ ≤
      orbitAverageMeasure θ N (fun n x => w n (fun i : I => x i)) univ *
        (ENNReal.ofReal (M : ℝ) * ∑' i : {i : ℕ // i ∉ I}, ENNReal.ofReal (θ i)) := by
  let B : ℝ≥0∞ := ENNReal.ofReal (M : ℝ) *
    ∑' i : {i : ℕ // i ∉ I}, ENNReal.ofReal (θ i)
  have hbound (n : ℕ) (hn : n ∈ N) :
      orbitPairMeasure θ n (fun x : Base => w n (fun i : I => x i)) orderedPairEventᶜ ≤
        orbitPairMeasure θ n (fun x : Base => w n (fun i : I => x i)) univ * B := by
    refine (orbitPairMeasure_unordered_le I θ hθ n (w n) (hw n hn) (hprefix n hn)).trans ?_
    apply mul_le_mul_right
    apply mul_le_mul_left
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hN n hn)
  change orbitAverageMeasure θ N (fun n x => w n (fun i : I => x i)) orderedPairEventᶜ ≤
    orbitAverageMeasure θ N (fun n x => w n (fun i : I => x i)) univ * B
  simp only [orbitAverageMeasure, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
  rw [mul_assoc, Finset.sum_mul]
  apply mul_le_mul_right
  exact Finset.sum_le_sum hbound

theorem trimmed_orbitAverage_supported (θ : ℕ → ℝ) (N : Finset ℕ)
    (hN : ∀ n ∈ N, 0 < n) (w : ℕ → Base → ℝ≥0∞) :
    SupportedOnPositiveOrderedOrbitPairs θ
      ((orbitAverageMeasure θ N w).restrict orderedPairEvent) := by
  refine ⟨N, hN, ?_⟩
  have hm : MeasurableSet {xy : Base × Base |
      ∃ n ∈ N, xy.2 = rotationIterate θ (n : ℤ) xy.1} := by
    simp only [ofPred_exists]
    apply MeasurableSet.iUnion
    intro n
    by_cases hn : n ∈ N
    · simp only [hn, true_and]
      apply measurableSet_eq_fun measurable_snd
      apply Measurable.of_eval
      intro i
      exact ((measurable_pi_apply i).comp measurable_fst).add_const _
    · simp only [hn, false_and, ofPred_false, MeasurableSet.empty]
  have hgraph : ∀ᵐ xy ∂orbitAverageMeasure θ N w,
      ∃ n ∈ N, xy.2 = rotationIterate θ (n : ℤ) xy.1 := by
    apply Measure.ae_smul_measure
    apply ae_finsetSum_measure_iff.mpr
    intro n hn
    apply (ae_map_iff (measurable_orbitPairMap θ n).aemeasurable hm).mpr
    exact Filter.Eventually.of_forall (fun _ => ⟨n, hn, rfl⟩)
  filter_upwards [ae_restrict_mem measurableSet_orderedPairEvent,
    ae_restrict_of_ae hgraph] with xy horder hgraph
  exact ⟨horder, hgraph⟩

end Invariant233.ProductModel.TailTrimming

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingTrimming
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingCylinderWeak.quotient_cutCoordinates _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.ProductModel

attribute [local instance] OAI.Invariant233.ProductModel.productSamplingTrimmingOpensMeasurableSpace
theorem weaklyConverges_iff_tendsto (η : ℕ → FiniteMeasure EndpointPair)
    (ν : FiniteMeasure EndpointPair) :
    WeaklyConverges (fun l => (η l : Measure EndpointPair)) (ν : Measure EndpointPair) ↔
      Tendsto η atTop (𝓝 ν) := by
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  constructor
  · intro h φ
    exact h φ.toContinuousMap
  · intro h φ
    exact h (BoundedContinuousFunction.mkOfCompact φ)

theorem WeaklyConverges.tendsto_mass {η : ℕ → Measure EndpointPair}
    {ν : Measure EndpointPair} (hweak : WeaklyConverges η ν)
    (hη : ∀ l, IsFiniteMeasure (η l)) (hν : IsFiniteMeasure ν) :
    Tendsto (fun l => η l univ) atTop (𝓝 (ν univ)) := by
  let μn : ℕ → FiniteMeasure EndpointPair := fun l => ⟨η l, hη l⟩
  let μ : FiniteMeasure EndpointPair := ⟨ν, hν⟩
  have hμ := (weaklyConverges_iff_tendsto μn μ).mp hweak
  have hm : Tendsto (fun index => ((μn index).mass : ℝ≥0∞)) atTop
      (𝓝 (μ.mass : ℝ≥0∞)) := ENNReal.tendsto_coe.mpr hμ.mass
  rw [FiniteMeasure.ennreal_mass (μ := μ)] at hm
  exact hm.congr (fun index => FiniteMeasure.ennreal_mass (μ := μn index))

theorem WeaklyConverges.restrict_of_discarded_tendsto_zero
    {η : ℕ → Measure EndpointPair} {ν : Measure EndpointPair}
    (hweak : WeaklyConverges η ν)
    (hη : ∀ l, IsFiniteMeasure (η l)) (hν : IsFiniteMeasure ν)
    (A : ℕ → Set EndpointPair) (hA : ∀ l, MeasurableSet (A l))
    (hlost : Tendsto (fun l => η l (A l)ᶜ) atTop (𝓝 0)) :
    WeaklyConverges (fun l => (η l).restrict (A l)) ν := by
  let μn : ℕ → FiniteMeasure EndpointPair := fun l => ⟨η l, hη l⟩
  let μ : FiniteMeasure EndpointPair := ⟨ν, hν⟩
  have hμ : Tendsto μn atTop (𝓝 μ) :=
    (weaklyConverges_iff_tendsto μn μ).mp hweak
  have hlost' : Tendsto (fun l => μn l (A l)ᶜ) atTop (𝓝 0) := by
    change Tendsto (fun l => (η l (A l)ᶜ).toNNReal) atTop (𝓝 0)
    have h := (ENNReal.tendsto_toNNReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hlost
    exact h
  have htrim := Invariant233.TrimmingWeakLimits.tendsto_restrict_of_compl_mass_tendsto_zero
    hμ A hA hlost'
  exact (weaklyConverges_iff_tendsto (fun l => (μn l).restrict (A l)) μ).mpr htrim

namespace TailTrimming

attribute [local instance] OAI.Invariant233.ProductModel.productSamplingTrimmingOpensMeasurableSpace
theorem orderedOrbitSampling_of_untrimmed (θ : ℕ → ℝ) (I : Finset ℕ)
    (N : ℕ → Finset ℕ) (w : ℕ → ℕ → Base → ℝ≥0∞)
    (hN : ∀ l, ∀ n ∈ N l, 0 < n)
    (hL2 : HasUniformL2Marginals (fun l => orbitAverageMeasure θ (N l) (w l)))
    (hweak : WeaklyConverges (fun l => orbitAverageMeasure θ (N l) (w l))
      (triangularLaw I))
    (hlost : Tendsto (fun l => orbitAverageMeasure θ (N l) (w l) orderedPairEventᶜ)
      atTop (𝓝 0)) :
    OrderedOrbitSampling θ I := by
  refine ⟨fun l => (orbitAverageMeasure θ (N l) (w l)).restrict orderedPairEvent,
    ?_, ?_, hL2.restrict (fun _ => orderedPairEvent), ?_⟩
  · intro l
    let := hL2.isFiniteMeasure l
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  · intro l
    exact trimmed_orbitAverage_supported θ (N l) (hN l) (w l)
  · have hν : IsFiniteMeasure (triangularLaw I) := by
      unfold triangularLaw
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
    exact hweak.restrict_of_discarded_tendsto_zero hL2.isFiniteMeasure hν
      (fun _ => orderedPairEvent) (fun _ => measurableSet_orderedPairEvent) hlost

theorem orderedOrbitSampling_of_prefix_samples (θ : ℕ → ℝ) (I : Finset ℕ)
    (hθ : ∀ i, 0 ≤ θ i) (D N : ℕ → Finset ℕ) (M : ℕ → ℕ)
    (w : ∀ l, ℕ → (D l → Circle) → ℝ≥0∞)
    (hw : ∀ l, ∀ n ∈ N l, Measurable (w l n))
    (hN : ∀ l, ∀ n ∈ N l, 0 < n)
    (hM : ∀ l, ∀ n ∈ N l, n ≤ M l)
    (hprefix : ∀ l, ∀ n ∈ N l,
      ∀ᵐ x ∂baseMeasure.withDensity (fun x : Base => w l n (fun i : D l => x i)),
        ∀ i ∈ D l, circleRepresentative (x i) ≤
          circleRepresentative (rotationIterate θ (n : ℤ) x i))
    (hL2 : HasUniformL2Marginals
      (fun l => orbitAverageMeasure θ (N l) (fun n x => w l n (fun i : D l => x i))))
    (hweak : WeaklyConverges
      (fun l => orbitAverageMeasure θ (N l) (fun n x => w l n (fun i : D l => x i)))
      (triangularLaw I))
    (htail : Tendsto (fun l => ENNReal.ofReal (M l : ℝ) *
      ∑' i : {i : ℕ // i ∉ D l}, ENNReal.ofReal (θ i)) atTop (𝓝 0)) :
    OrderedOrbitSampling θ I := by
  let η : ℕ → Measure EndpointPair :=
    fun l => orbitAverageMeasure θ (N l) (fun n x => w l n (fun i : D l => x i))
  have hν : IsFiniteMeasure (triangularLaw I) := by
    unfold triangularLaw
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hm : Tendsto (fun l => η l univ) atTop (𝓝 (triangularLaw I univ)) :=
    hweak.tendsto_mass hL2.isFiniteMeasure hν
  have hνtop : triangularLaw I univ ≠ ∞ := by
    let := hν
    exact measure_ne_top _ _
  have hbound := ENNReal.Tendsto.mul hm (Or.inr (by simp : (0 : ℝ≥0∞) ≠ ∞))
    htail (Or.inr hνtop)
  have hzero : Tendsto (fun l => η l univ * (ENNReal.ofReal (M l : ℝ) *
      ∑' i : {i : ℕ // i ∉ D l}, ENNReal.ofReal (θ i))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hbound
  apply orderedOrbitSampling_of_untrimmed θ I N
    (fun l n x => w l n (fun i : D l => x i)) hN hL2 hweak
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
  · intro l
    exact bot_le
  · intro l
    exact orbitAverageMeasure_unordered_le (D l) (N l) θ hθ (M l) (hM l)
      (w l) (hw l) (hprefix l)

end TailTrimming
end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_IndependentAngles
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace InvariantProjection.IndependentAngles

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_add_ne_of_indep [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y μ)
    [NullSingletonClass (μ.map Y)] (c : ℝ) :
    ∀ᵐ ω ∂μ, X ω + Y ω ≠ c := by
  have hset : MeasurableSet {z : ℝ × ℝ | z.1 + z.2 ≠ c} := by
    exact (measurable_fst.add measurable_snd) (measurableSet_singleton c).compl
  have hp : ∀ᵐ z ∂(μ.map X).prod (μ.map Y), z.1 + z.2 ≠ c := by
    apply (ae_prod_iff_ae_ae hset).2
    exact Filter.Eventually.of_forall fun x =>
      ((μ.map Y).ae_ne (c - x)).mono fun y hy h => hy (by linarith)
  rw [← hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable] at hp
  exact ae_of_ae_map (hX.prodMk hY).aemeasurable hp

theorem nullSingletonClass_map_mul {X : Ω → ℝ} (hX : Measurable X)
    [NullSingletonClass (μ.map X)] {c : ℝ} (hc : c ≠ 0) :
    NullSingletonClass (μ.map (fun ω => c * X ω)) := by
  constructor
  intro y
  rw [Measure.map_apply (show Measurable (fun ω => c * X ω) from
    measurable_const.mul hX) (measurableSet_singleton y)]
  have hsub : (fun ω => c * X ω) ⁻¹' {y} ⊆ X ⁻¹' {y / c} := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
    apply (eq_div_iff hc).2
    simpa [mul_comm] using hω
  apply measure_mono_null hsub
  rw [← Measure.map_apply hX (measurableSet_singleton (y / c))]
  exact measure_singleton _

theorem ae_finset_sum_ne [IsProbabilityMeasure μ] [DecidableEq ι]
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hno : ∀ i, NullSingletonClass (μ.map (X i)))
    (s : Finset ι) (c : ι → ℝ) {i : ι} (hi : i ∈ s) (hci : c i ≠ 0)
    (r : ℝ) : ∀ᵐ ω ∂μ, (∑ j ∈ s, c j * X j ω) ≠ r := by
  let Y : ι → Ω → ℝ := fun j ω => c j * X j ω
  have hY : ∀ j, Measurable (Y j) := fun j => measurable_const.mul (hX j)
  have hindY : iIndepFun Y μ := hind.comp (fun j x => c j * x)
    (fun _ => measurable_const.mul measurable_id)
  have hsumInd : IndepFun (∑ j ∈ s.erase i, Y j) (Y i) μ :=
    hindY.indepFun_finsetSum_of_notMem hY (Finset.notMem_erase i s)
  let : NullSingletonClass (μ.map (X i)) := hno i
  let : NullSingletonClass (μ.map (Y i)) :=
    nullSingletonClass_map_mul (hX i) hci
  have hsum : Measurable (∑ j ∈ s.erase i, Y j) := by
    change Measurable (fun ω => (∑ j ∈ s.erase i, Y j) ω)
    simp only [Finset.sum_apply]
    exact Finset.measurable_sum (s.erase i) (fun j _ => hY j)
  filter_upwards [ae_add_ne_of_indep hsum (hY i) hsumInd r] with ω hω
  convert hω using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Finset.sum_apply, Y]
  exact (Finset.sum_erase_add _ _ hi).symm

theorem ae_finsupp_sum_ne [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hno : ∀ i, NullSingletonClass (μ.map (X i)))
    (c : ι →₀ ℚ) (hc : c ≠ 0) (r : ℝ) :
    ∀ᵐ ω ∂μ, c.sum (fun j q => (q : ℝ) * X j ω) ≠ r := by
  classical
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hc
  have hci : (c i : ℝ) ≠ 0 := by
    exact_mod_cast Finsupp.mem_support_iff.mp hi
  exact ae_finset_sum_ne hX hind hno c.support (fun j => (c j : ℝ)) hi hci r

theorem ae_no_rational_affine_relation [Countable ι] [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hno : ∀ i, NullSingletonClass (μ.map (X i))) :
    ∀ᵐ ω ∂μ, ∀ (c : ι →₀ ℚ) (q : ℚ),
      (q : ℝ) + c.sum (fun j r => (r : ℝ) * X j ω) = 0 → c = 0 ∧ q = 0 := by
  apply ae_all_iff.mpr
  intro c
  apply ae_all_iff.mpr
  intro q
  by_cases hc : c = 0
  · subst c
    exact Filter.Eventually.of_forall fun ω h => ⟨rfl, by simpa using h⟩
  · filter_upwards [ae_finsupp_sum_ne hX hind hno c hc (-(q : ℝ))] with ω hω
    intro heq
    exact False.elim (hω (by linarith))

theorem ae_linearIndependent_with_one [Countable ι] [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hno : ∀ i, NullSingletonClass (μ.map (X i))) :
    ∀ᵐ ω ∂μ, LinearIndependent ℚ (fun o : Option ι => o.elim 1 (fun i => X i ω)) := by
  filter_upwards [ae_no_rational_affine_relation hX hind hno] with ω hω
  rw [linearIndependent_iff]
  intro l hl
  rw [Finsupp.linearCombination_apply, Finsupp.sum_option_index_smul] at hl
  have hrel : (l none : ℝ) + l.some.sum (fun j r => (r : ℝ) * X j ω) = 0 := by
    simpa only [Option.elim_none, Option.elim_some, Rat.smul_def, mul_one] using hl
  obtain ⟨hsome, hnone⟩ := hω l.some (l none) hrel
  ext o
  cases o with
  | none => exact hnone
  | some i =>
      change l.some i = 0
      rw [hsome]
      rfl

theorem infinitePi_ae_linearIndependent_with_one [Countable ι]
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, NullSingletonClass (ν i)] :
    ∀ᵐ θ ∂Measure.infinitePi ν,
      LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ) := by
  have hm : ∀ i : ι, Measurable (fun θ : ι → ℝ => θ i) :=
    fun i => measurable_pi_apply i
  have hi : iIndepFun (fun i (θ : ι → ℝ) => θ i) (Measure.infinitePi ν) :=
    iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  have hn : ∀ i : ι, NullSingletonClass
      ((Measure.infinitePi ν).map (fun θ : ι → ℝ => θ i)) := by
    intro i
    rw [Measure.infinitePi_map_eval]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact ae_linearIndependent_with_one hm hi hn

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

theorem intervalProduct_ae_bounds_linearIndependent [Countable ι]
    (a b : ι → ℝ) (hab : ∀ i, a i < b i) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume (Set.Icc (a i) (b i))),
      (∀ i, θ i ∈ Set.Icc (a i) (b i)) ∧
      LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ) := by
  let ν : ι → Measure ℝ := fun i => ProbabilityTheory.cond volume (Set.Icc (a i) (b i))
  let (i : ι) : IsProbabilityMeasure (ν i) := intervalLaw_isProbabilityMeasure (hab i)
  let (i : ι) : NullSingletonClass (ν i) := intervalLaw_nullSingletonClass (a i) (b i)
  have hb : ∀ᵐ θ ∂Measure.infinitePi ν, ∀ i, θ i ∈ Set.Icc (a i) (b i) := by
    apply ae_all_iff.mpr
    intro i
    have hi : ∀ᵐ x ∂(Measure.infinitePi ν).map (fun θ => θ i),
        x ∈ Set.Icc (a i) (b i) := by
      rw [Measure.infinitePi_map_eval]
      exact ae_cond_mem measurableSet_Icc
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hi
  exact hb.and (infinitePi_ae_linearIndependent_with_one ν)

theorem prescribedIntervals_ae_summable_independent [Countable ι]
    (N : ι → ℝ) (hN : ∀ i, 0 < N i) (hsum : Summable (fun i => 1 / N i)) :
    ∀ᵐ θ ∂Measure.infinitePi
        (fun i => ProbabilityTheory.cond volume (Set.Icc (1 / N i) (2 / N i))),
      (∀ i, θ i ∈ Set.Icc (1 / N i) (2 / N i)) ∧ Summable θ ∧
      (∑' i, θ i) ≤ 2 * (∑' i, 1 / N i) ∧
      LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ) := by
  have hinterval : ∀ i, (1 : ℝ) / N i < 2 / N i := fun i =>
    div_lt_div_of_pos_right (by norm_num) (hN i)
  filter_upwards [intervalProduct_ae_bounds_linearIndependent
    (fun i => 1 / N i) (fun i => 2 / N i) hinterval] with θ hθ
  have hnonneg : ∀ i, 0 ≤ θ i := fun i =>
    (le_of_lt (one_div_pos.mpr (hN i))).trans (hθ.1 i).1
  have hupper : ∀ i, θ i ≤ 2 * (1 / N i) := by
    intro i
    simpa only [mul_one_div] using (hθ.1 i).2
  have hsumθ : Summable θ :=
    Summable.of_nonneg_of_le hnonneg hupper (hsum.mul_left 2)
  refine ⟨hθ.1, hsumθ, ?_, hθ.2⟩
  calc
    (∑' i, θ i) ≤ ∑' i, 2 * (1 / N i) :=
      hsumθ.tsum_le_tsum hupper (hsum.mul_left 2)
    _ = 2 * (∑' i, 1 / N i) := tsum_mul_left

end InvariantProjection.IndependentAngles

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

theorem real_K_pos (n : ℕ) : 0 < (p.K n : ℝ) := by exact_mod_cast hp.K_pos n

theorem real_K_double (n : ℕ) : 2 * (p.K n : ℝ) ≤ (p.K (n + 1) : ℝ) := by
  exact_mod_cast (hp.K_double n).le

theorem summable_reciprocal : Summable (fun n => 1 / (p.K n : ℝ)) :=
  ParameterTails.summable_reciprocal hp.real_K_pos hp.real_K_double

theorem reciprocal_tail_bound (n : ℕ) :
    (∑' r : ℕ, 1 / (p.K (n + 1 + r) : ℝ)) ≤ 2 / (p.K (n + 1) : ℝ) :=
  ParameterTails.reciprocal_tail_bound hp.real_K_pos hp.real_K_double n

theorem prefix_count_succ_le (n : ℕ) :
    (p.prefixCount (n + 1) : ℝ) ≤ (101 / 100 : ℝ) * p.m n := by
  have h := hp.prefix_count_le n
  simp only [ProductScaleData.prefixCount, Finset.sum_range_succ, Nat.cast_add] at *
  linarith

theorem m_lt_next_K (n : ℕ) : p.m n < p.K (n + 1) := by
  have hm : (20 : ℝ) ≤ p.m n := by exact_mod_cast le_trans (by decide) (hp.m_ge_100 n)
  have h := SamplingHorizon.twice_lt_ceiling_cutoff hm
  rw [← hp.next_K n] at h
  have hmpos : (0 : ℝ) < p.m n := by exact_mod_cast hp.m_pos n
  have : (p.m n : ℝ) < p.K (n + 1) := by linarith
  exact_mod_cast this

theorem m_strictMono : StrictMono p.m := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (hp.m_lt_next_K n).trans_le (hp.m_ge_K (n + 1))

theorem reciprocal_sum_le : (∑' n, 1 / (p.K n : ℝ)) ≤ 1 / 50 := by
  have h := ParameterTails.tsum_tail_le_of_half_decay
    (fun n => (one_div_pos.mpr (hp.real_K_pos n)).le)
    (ParameterTails.reciprocal_half_decay hp.real_K_pos hp.real_K_double) 0
  norm_num [hp.initial_K] at h ⊢
  exact h

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_BlockPhaseConstruction
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace Invariant233.ProductPhases

theorem mem_consecutiveBlock_iff (m : ℕ → ℕ) (j i : ℕ) :
    i ∈ consecutiveBlock m j ↔
      (∑ r ∈ Finset.range j, m r) ≤ i ∧
        i < (∑ r ∈ Finset.range j, m r) + m j := by
  simp [consecutiveBlock]

theorem mem_consecutiveBlock_enumeration (m : ℕ → ℕ)
    (e : ℕ ≃ Σ j, Fin (m j))
    (he : ∀ a : Σ j, Fin (m j),
      e.symm a = (∑ r ∈ Finset.range a.1, m r) + a.2.val)
    (i : ℕ) : i ∈ consecutiveBlock m (e i).1 := by
  have hi : i = (∑ r ∈ Finset.range (e i).1, m r) + (e i).2.val := by
    simpa only [e.symm_apply_apply] using he (e i)
  apply (mem_consecutiveBlock_iff m (e i).1 i).mpr
  have hb := (e i).2.isLt
  omega

end Invariant233.ProductPhases

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductScaleTail
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

open ProductPhases InvariantProjection.IndependentAngles
variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

omit hp

theorem mem_consecutiveBlock_tail (j r i : ℕ)
    (hi : i ∈ consecutiveBlock (fun k => p.m (j + k)) r) :
    p.prefixCount j + i ∈ consecutiveBlock p.m (j + r) := by
  have h := (mem_consecutiveBlock_iff _ _ _).mp hi
  apply (mem_consecutiveBlock_iff _ _ _).mpr
  rw [Finset.sum_range_add]
  dsimp [ProductScaleData.prefixCount]
  omega

include hp

theorem angle_tail_le (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : ∀ j, ∀ i ∈ consecutiveBlock p.m j,
      θ i ≤ 2 / ((p.m j : ℝ) * p.K j)) (j : ℕ) :
    (∑' i, θ (p.prefixCount j + i)) ≤ 2 * (∑' r, 1 / (p.K (j + r) : ℝ)) := by
  let mt : ℕ → ℕ := fun r => p.m (j + r)
  let Kt : ℕ → ℝ := fun r => p.K (j + r)
  have hm : ∀ r, 0 < mt r := fun r => hp.m_pos (j + r)
  have hK : ∀ r, 0 < Kt r := fun r => hp.real_K_pos (j + r)
  have hsum : Summable (fun r => 1 / Kt r) := by
    simpa only [Kt, Nat.add_comm] using (summable_nat_add_iff j).mpr hp.summable_reciprocal
  obtain ⟨e, he⟩ := exists_consecutiveBlocks_equiv mt hm
  have hrec := enumerated_block_reciprocal mt hm Kt hK hsum e
  have hbound (i : ℕ) : θ (p.prefixCount j + i) ≤
      2 * (1 / ((mt (e i).1 : ℝ) * Kt (e i).1)) := by
    have hi := mem_consecutiveBlock_enumeration mt e he i
    have hi' := mem_consecutiveBlock_tail j (e i).1 i hi
    simpa only [mt, Kt, mul_one_div] using hθ _ _ hi'
  have hs : Summable (fun i => θ (p.prefixCount j + i)) :=
    Summable.of_nonneg_of_le (fun i => hθ0 _) hbound (hrec.1.mul_left 2)
  calc
    _ ≤ ∑' i, 2 * (1 / ((mt (e i).1 : ℝ) * Kt (e i).1)) :=
      hs.tsum_le_tsum hbound (hrec.1.mul_left 2)
    _ = 2 * (∑' r, 1 / (p.K (j + r) : ℝ)) := by
      rw [tsum_mul_left, hrec.2]

theorem angle_tail_le_four_div_next (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : ∀ j, ∀ i ∈ consecutiveBlock p.m j,
      θ i ≤ 2 / ((p.m j : ℝ) * p.K j)) (n : ℕ) :
    (∑' i, θ (p.prefixCount (n + 1) + i)) ≤ 4 / (p.K (n + 1) : ℝ) := by
  calc
    _ ≤ 2 * (∑' r, 1 / (p.K (n + 1 + r) : ℝ)) := hp.angle_tail_le θ hθ0 hθ (n + 1)
    _ ≤ 2 * (2 / (p.K (n + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hp.reciprocal_tail_bound n) (by norm_num)
    _ = _ := by ring

theorem horizon_ratio_le_decay (n : ℕ) :
    (p.m n : ℝ) ^ ((7 / 10 : ℝ) * p.m n) / p.K (n + 1) ≤
      (p.m n : ℝ) ^ (-(p.m n : ℝ) / 20) := by
  have hm : 0 < (p.m n : ℝ) := by exact_mod_cast hp.m_pos n
  have hnext : (p.m n : ℝ) ^ ((3 / 4 : ℝ) * p.m n) ≤ p.K (n + 1) := by
    rw [hp.next_K n]
    exact Nat.le_ceil _
  calc
    _ ≤ (p.m n : ℝ) ^ ((7 / 10 : ℝ) * p.m n) /
        (p.m n : ℝ) ^ ((3 / 4 : ℝ) * p.m n) :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hm _) hnext
    _ = _ := by rw [← Real.rpow_sub hm]; congr 1; ring

theorem power_mul_angle_tail_le (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : ∀ j, ∀ i ∈ consecutiveBlock p.m j,
      θ i ≤ 2 / ((p.m j : ℝ) * p.K j)) (n t : ℕ)
    (ht : (t : ℝ) ≤ (p.m n : ℝ) ^ ((7 / 10 : ℝ) * p.m n)) :
    (t : ℝ) * (∑' i, θ (p.prefixCount (n + 1) + i)) ≤
      4 * (p.m n : ℝ) ^ (-(p.m n : ℝ) / 20) := by
  calc
    _ ≤ (p.m n : ℝ) ^ ((7 / 10 : ℝ) * p.m n) * (4 / (p.K (n + 1) : ℝ)) :=
      mul_le_mul ht (hp.angle_tail_le_four_div_next θ hθ0 hθ n)
        (tsum_nonneg fun _ => hθ0 _) (by positivity)
    _ = 4 * ((p.m n : ℝ) ^ ((7 / 10 : ℝ) * p.m n) / p.K (n + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hp.horizon_ratio_le_decay n) (by norm_num)

theorem tendsto_tail_trim_bound :
    Tendsto (fun n => 4 * (p.m n : ℝ) ^ (-(p.m n : ℝ) / 20)) atTop (𝓝 0) := by
  have hm : Tendsto (fun n => (p.m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hp.m_strictMono.tendsto_atTop
  have hi : Tendsto (fun n => 4 * (p.m n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hm).const_mul 4
  apply squeeze_zero' _ _ hi
  · exact Filter.Eventually.of_forall fun _ => by positivity
  · apply Filter.Eventually.of_forall
    intro n
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply SamplingHorizon.decay_le_inv
    exact_mod_cast le_trans (by decide : 20 ≤ 100) (hp.m_ge_100 n)

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingScaleTrimming
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Invariant233.ProductModel.TailTrimming

theorem tsum_outside_range_ofReal (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθsum : Summable θ) (d : ℕ) :
    (∑' i : {i : ℕ // i ∉ Finset.range d}, ENNReal.ofReal (θ i)) =
      ENNReal.ofReal (∑' k, θ (d + k)) := by
  let e : ℕ ≃ {i : ℕ // i ∉ Finset.range d} := Equiv.ofBijective
    (fun k => ⟨d + k, by simp⟩) (by
      constructor
      · intro i j hij
        have h := congrArg Subtype.val hij
        exact Nat.add_left_cancel h
      · intro i
        refine ⟨i.val - d, ?_⟩
        apply Subtype.ext
        have hi := i.property
        simp only [Finset.mem_range, not_lt] at hi
        dsimp
        omega)
  rw [← e.tsum_eq (fun i => ENNReal.ofReal (θ i))]
  change (∑' k, ENNReal.ofReal (θ (d + k))) = _
  exact (ENNReal.ofReal_tsum_of_nonneg (fun _ => hθ0 _)
    (hθsum.comp_injective (fun _ _ h => Nat.add_left_cancel h))).symm

theorem source_horizon_angle_tail_le {p : ProductScaleData} (hp : ProductScaleLaws p)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (hθ : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ≤ 2 / ((p.m j : ℝ) * p.K j)) (l t : ℕ)
    (ht : (t : ℝ) ≤ (p.m l : ℝ) ^ ((7 / 10 : ℝ) * p.m l)) :
    ENNReal.ofReal (t : ℝ) *
      (∑' i : {i : ℕ // i ∉ Finset.range (p.prefixCount (l + 1))},
        ENNReal.ofReal (θ i)) ≤
      ENNReal.ofReal (4 * (p.m l : ℝ) ^ (-(p.m l : ℝ) / 20)) := by
  rw [tsum_outside_range_ofReal θ hθ0 hθsum,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg t)]
  exact ENNReal.ofReal_le_ofReal (hp.power_mul_angle_tail_le θ hθ0 hθ l t ht)

theorem source_horizon_angle_tail_tendsto_zero {p : ProductScaleData}
    (hp : ProductScaleLaws p) (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθsum : Summable θ)
    (hθ : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ≤ 2 / ((p.m j : ℝ) * p.K j)) (M : ℕ → ℕ)
    (hM : ∀ l, (M l : ℝ) ≤ (p.m l : ℝ) ^ ((7 / 10 : ℝ) * p.m l)) :
    Tendsto (fun l => ENNReal.ofReal (M l : ℝ) *
      ∑' i : {i : ℕ // i ∉ Finset.range (p.prefixCount (l + 1))},
        ENNReal.ofReal (θ i)) atTop (𝓝 0) := by
  have hb := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hp.tendsto_tail_trim_bound
  have hb' : Tendsto (fun l => ENNReal.ofReal
      (4 * (p.m l : ℝ) ^ (-(p.m l : ℝ) / 20))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using! hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb'
  · intro l
    exact bot_le
  · intro l
    exact source_horizon_angle_tail_le hp θ hθ0 hθsum hθ l (M l) (hM l)

end Invariant233.ProductModel.TailTrimming

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductSourceAngleLaw
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal

namespace Invariant233.ProductScaleLaws
open ProductPhases InvariantProjection.IndependentAngles

variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem source_coordinate_reciprocal (S : ℕ → ℝ)
    (hblock : ∀ j, ∀ i ∈ consecutiveBlock p.m j, S i = (p.m j : ℝ) * p.K j) :
    Summable (fun i => 1 / S i) ∧
      (∑' i, 1 / S i) = ∑' j, 1 / (p.K j : ℝ) := by
  obtain ⟨e, he⟩ := exists_consecutiveBlocks_equiv p.m hp.m_pos
  have hS (i : ℕ) : S i = (p.m (e i).1 : ℝ) * p.K (e i).1 :=
    hblock _ _ (mem_consecutiveBlock_enumeration p.m e he i)
  simpa only [hS] using enumerated_block_reciprocal p.m hp.m_pos
    (fun j => (p.K j : ℝ)) hp.real_K_pos hp.summable_reciprocal e

theorem ae_source_angles (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hblock : ∀ j, ∀ i ∈ consecutiveBlock p.m j, S i = (p.m j : ℝ) * p.K j) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Icc (1 / S i) (2 / S i))),
      (∀ j, ∀ i ∈ consecutiveBlock p.m j,
        θ i ∈ Icc (1 / p.N j) (2 / p.N j)) ∧
      (∀ i, 0 < θ i ∧ θ i < 1) ∧ Summable θ ∧
      (∑' i, θ i) ≤ 1 / 25 ∧ ProductModel.JointlyRationallyIndependent θ := by
  have hrec := hp.source_coordinate_reciprocal S hblock
  filter_upwards [prescribedIntervals_ae_summable_independent S hS hrec.1] with θ hθ
  have hb (j i : ℕ) (hi : i ∈ consecutiveBlock p.m j) :
      θ i ∈ Icc (1 / p.N j) (2 / p.N j) := by
    simpa only [hblock j i hi, ProductScaleData.N] using hθ.1 i
  have hpos (i : ℕ) : 0 < θ i :=
    (one_div_pos.mpr (hS i)).trans_le (hθ.1 i).1
  have hsum : (∑' i, θ i) ≤ 1 / 25 := by
    have ht := hθ.2.2.1
    rw [hrec.2] at ht
    have hk := hp.reciprocal_sum_le
    linarith
  refine ⟨hb, ?_, hθ.2.1, hsum, hθ.2.2.2⟩
  intro i
  refine ⟨hpos i, ?_⟩
  have hi : θ i ≤ ∑' k, θ k :=
    hθ.2.1.le_tsum i (fun k _ => (hpos k).le)
  linarith

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductIdealSamplingLimit
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingCylinderWeak.quotient_cutCoordinates _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace Invariant233.ProductModel.IdealSampling

theorem cutoffEvent_measurable (I D : Finset ℕ) (α : ℝ) :
    MeasurableSet (cutoffEvent I D α) := by
  unfold cutoffEvent
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  have hx : Measurable (fun xz : EndpointPair => circleRepresentative (xz.1 i)) := by
    fun_prop
  exact measurableSet_le measurable_const (hx.min (measurable_const.sub hx))

theorem endpointMap_tendsto (I : Finset ℕ) (D : ℕ → Finset ℕ)
    {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0)) (xz : EndpointPair) :
    Tendsto (fun l => endpointMap I (D l) (h l) xz) atTop
      (𝓝 (xz.1, selectedEndpoint I xz.1 xz.2)) := by
  apply tendsto_const_nhds.prodMk_nhds
  apply tendsto_pi_nhds.mpr
  intro i
  by_cases hi : i ∈ I
  · simp [endpoint, selectedEndpoint, hi]
  · have hr : Tendsto (fun l => h l * ScalarSampling.delta
        (circleRepresentative (xz.1 i)) * circleRepresentative (xz.2 i))
        atTop (𝓝 0) := by
      simpa using (hh.mul_const (ScalarSampling.delta
        (circleRepresentative (xz.1 i)))).mul_const (circleRepresentative (xz.2 i))
    have hc : Continuous (fun r : ℝ => (r : Circle)) := by fun_prop
    have ha : Tendsto (fun l => xz.1 i + ((h l * ScalarSampling.delta
        (circleRepresentative (xz.1 i)) * circleRepresentative (xz.2 i) : ℝ) : Circle))
        atTop (𝓝 (xz.1 i)) := by
      simpa using tendsto_const_nhds.add (hc.continuousAt.tendsto.comp hr)
    simpa [endpoint, selectedEndpoint, hi] using
      (ha.if' (p := fun l => i ∈ D l) tendsto_const_nhds)

theorem circle_cutoff_loss_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    circleMeasure {x : Circle | ScalarSampling.delta (circleRepresentative x) < α} ≤
      ENNReal.ofReal (2 * α) := by
  have heq : {x : Circle | ScalarSampling.delta (circleRepresentative x) < α} =
      {x | circleRepresentative x < α} ∪
        {x | 1 - α < circleRepresentative x} := by
    ext x
    simp only [mem_ofPred_eq, mem_union, ScalarSampling.delta, min_lt_iff]
    constructor <;> intro hx
    · rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by linarith)
    · rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by linarith)
  rw [heq]
  calc
    _ ≤ circleMeasure {x | circleRepresentative x < α} +
        circleMeasure {x | 1 - α < circleRepresentative x} := measure_union_le _ _
    _ = ENNReal.ofReal α + ENNReal.ofReal α := by
      rw [Sampling.representative_initial_measure hα0 hα1,
        Sampling.representative_tail_measure (by linarith : 0 ≤ 1 - α)
          (by linarith : 1 - α ≤ 1)]
      congr 1
      congr 1
      ring

    _ = ENNReal.ofReal (2 * α) := by rw [← ENNReal.ofReal_add hα0 hα0]; congr 1; ring

theorem cutoff_loss_le (I D : Finset ℕ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    sourceMeasure I (cutoffEvent I D α)ᶜ ≤
      ENNReal.ofReal (2 * ((D \ I).card : ℝ) * α) := by
  let B : Set Circle := {x | ScalarSampling.delta (circleRepresentative x) < α}
  have hB : MeasurableSet B := measurableSet_lt
    (Sampling.representative_measurable.min
      (measurable_const.sub Sampling.representative_measurable)) measurable_const
  let bad : ℕ → Set EndpointPair := fun i => {xz | xz.1 i ∈ B}
  have hbad (i : ℕ) : (baseMeasure.prod baseMeasure) (bad i) ≤ ENNReal.ofReal (2 * α) := by
    have he : MeasurePreserving (fun x : Base => x i) baseMeasure circleMeasure :=
      measurePreserving_eval_infinitePi (fun _ : ℕ => circleMeasure) i
    have hf : MeasurePreserving (fun xz : EndpointPair => xz.1 i)
        (baseMeasure.prod baseMeasure) circleMeasure := he.comp measurePreserving_fst
    have hm := hf.measure_preimage hB.nullMeasurableSet
    change (baseMeasure.prod baseMeasure) ((fun xz : EndpointPair => xz.1 i) ⁻¹' B) ≤ _
    rw [hm]
    exact circle_cutoff_loss_le hα0 hα1
  have heq : (cutoffEvent I D α)ᶜ = ⋃ i ∈ D \ I, bad i := by
    ext xz
    simp [cutoffEvent, bad, B, and_assoc]
  calc
    sourceMeasure I (cutoffEvent I D α)ᶜ ≤
        (baseMeasure.prod baseMeasure) (cutoffEvent I D α)ᶜ := Measure.restrict_le_self _
    _ = (baseMeasure.prod baseMeasure) (⋃ i ∈ D \ I, bad i) := by rw [heq]
    _ ≤ ∑ i ∈ D \ I, (baseMeasure.prod baseMeasure) (bad i) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ D \ I, ENNReal.ofReal (2 * α) := Finset.sum_le_sum (fun i _ => hbad i)
    _ = ENNReal.ofReal (2 * ((D \ I).card : ℝ) * α) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring

theorem cutoff_loss_tendsto_zero (I : Finset ℕ) (D : ℕ → Finset ℕ)
    {α : ℕ → ℝ} (hα0 : ∀ l, 0 ≤ α l) (hα1 : ∀ l, α l ≤ 1)
    (hcut : Tendsto (fun l => ((D l \ I).card : ℝ) * α l) atTop (𝓝 0)) :
    Tendsto (fun l => sourceMeasure I (cutoffEvent I (D l) (α l))ᶜ) atTop (𝓝 0) := by
  have hb : Tendsto (fun l => ENNReal.ofReal
      (2 * ((D l \ I).card : ℝ) * α l)) atTop (𝓝 0) := by
    have hr := hcut.const_mul 2
    have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero, mul_assoc] using he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
  · intro l
    exact bot_le
  · intro l
    exact cutoff_loss_le I (D l) (hα0 l) (hα1 l)

theorem law_weaklyConverges (I : Finset ℕ) (D : ℕ → Finset ℕ)
    {h α : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0))
    (hα0 : ∀ l, 0 ≤ α l) (hα1 : ∀ l, α l ≤ 1)
    (hcut : Tendsto (fun l => ((D l \ I).card : ℝ) * α l) atTop (𝓝 0)) :
    WeaklyConverges (fun l => law I (D l) (h l) (α l)) (triangularLaw I) := by
  let μ : FiniteMeasure EndpointPair := ⟨sourceMeasure I, inferInstance⟩
  have hlost := cutoff_loss_tendsto_zero I D hα0 hα1 hcut
  have hlost' : Tendsto (fun l => μ (cutoffEvent I (D l) (α l))ᶜ) atTop (𝓝 0) := by
    change Tendsto (fun l => (sourceMeasure I (cutoffEvent I (D l) (α l))ᶜ).toNNReal)
      atTop (𝓝 0)
    exact (ENNReal.tendsto_toNNReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hlost
  have hv := VaryingMapWeakLimit.tendsto_map_restrict_of_ae_tendsto μ
    (fun l => endpointMap I (D l) (h l))
    (fun xz : EndpointPair => (xz.1, selectedEndpoint I xz.1 xz.2))
    (fun l => endpointMap_measurable I (D l) (h l))
    (Sampling.endpointMap_measurable I)
    (Filter.Eventually.of_forall (endpointMap_tendsto I D hh))
    (fun l => cutoffEvent I (D l) (α l))
    (fun l => cutoffEvent_measurable I (D l) (α l)) hlost'
  exact (weaklyConverges_iff_tendsto _ _).mpr hv

theorem law_weaklyConverges_of_linear_dimension
    (I : Finset ℕ) (D : ℕ → Finset ℕ) (m : ℕ → ℕ)
    (hm : ∀ l, 1 ≤ m l) (hmTop : Tendsto m atTop atTop)
    {C : ℝ}
    (hD : ∀ l, ((D l).card : ℝ) ≤ C * (m l : ℝ)) :
    WeaklyConverges (fun l => law I (D l)
      ((m l : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (m l : ℝ) ^ 2)) (triangularLaw I) := by
  have hmR : Tendsto (fun l => (m l : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmTop
  have hm1 (l : ℕ) : (1 : ℝ) ≤ m l := by exact_mod_cast hm l
  have hmp (l : ℕ) : (0 : ℝ) < m l := lt_of_lt_of_le zero_lt_one (hm1 l)
  apply law_weaklyConverges I D
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 5)).comp hmR)
  · intro l
    positivity
  · intro l
    apply (div_le_one (sq_pos_of_pos (hmp l))).mpr
    nlinarith [hm1 l]
  · have hi : Tendsto (fun l => C * (m l : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp hmR).const_mul C
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hi
    · intro l
      positivity
    · intro l
      have hc : ((D l \ I).card : ℝ) ≤ C * (m l : ℝ) :=
        (Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)).trans (hD l)
      calc
        ((D l \ I).card : ℝ) * (1 / (m l : ℝ) ^ 2) ≤
            (C * (m l : ℝ)) * (1 / (m l : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
        _ = C * (m l : ℝ)⁻¹ := by field_simp

end Invariant233.ProductModel.IdealSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductIdealSamplingScales
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233.ProductModel.IdealSampling

theorem scale_m_tendsto_atTop {p : ProductScaleData} (hp : ProductScaleLaws p) :
    Tendsto p.m atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  have hn2 : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  have hnm := hp.m_ge_pow n
  omega

theorem law_weaklyConverges_of_productScaleLaws (I : Finset ℕ)
    {p : ProductScaleData} (hp : ProductScaleLaws p) :
    WeaklyConverges (fun l => law I (Finset.range (p.prefixCount (l + 1)))
      ((p.m l : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m l : ℝ) ^ 2)) (triangularLaw I) := by
  apply law_weaklyConverges_of_linear_dimension I _ p.m
    (fun l => (hp.m_pos l)) (scale_m_tendsto_atTop hp) (C := 101 / 100)
  intro l
  simpa only [Finset.card_range] using hp.prefix_count_succ_le l

end Invariant233.ProductModel.IdealSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingCylinderWeak
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.cylinderCoordinateSet_empty _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology ENNReal

namespace Invariant233.SamplingCylinderWeak

theorem tendsto_finiteMeasure_of_piSystem
    {X ι : Type*} [Nonempty X] [MeasurableSpace X] [TopologicalSpace X]
    [SecondCountableTopology X] [OpensMeasurableSpace X]
    {S : Set (Set X)} (hS : IsPiSystem S)
    {μ : ι → FiniteMeasure X} {ν : FiniteMeasure X}
    {l : Filter ι} [l.IsCountablyGenerated]
    (hmeas : ∀ s ∈ S, MeasurableSet s)
    (hbasis : ∀ u : Set X, IsOpen u → ∀ x ∈ u,
      ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u)
    (hmass : Tendsto (fun i => (μ i).mass) l (𝓝 ν.mass))
    (hconv : ∀ s ∈ S, Tendsto (fun i => μ i s) l (𝓝 (ν s))) :
    Tendsto μ l (𝓝 ν) := by
  by_cases hν : ν = 0
  · subst ν
    exact FiniteMeasure.tendsto_zero_of_tendsto_zero_mass (by simpa using hmass)
  have hνmass : ν.mass ≠ 0 := (FiniteMeasure.mass_nonzero_iff ν).mpr hν
  have hnonzero : ∀ᶠ i in l, μ i ≠ 0 := by
    filter_upwards [(tendsto_order.1 hmass).1 0 (pos_iff_ne_zero.mpr hνmass)] with i hi
    exact (FiniteMeasure.mass_nonzero_iff (μ i)).mp (ne_of_gt hi)
  have hnorm : Tendsto (fun i => (μ i).normalize) l (𝓝 ν.normalize) := by
    apply hS.tendsto_probabilityMeasure_of_tendsto_of_mem hmeas hbasis
    intro s hs
    have h := (hmass.inv₀ hνmass).mul (hconv s hs)
    rw [← ν.normalize_eq_of_nonzero hν s] at h
    apply h.congr'
    filter_upwards [hnonzero] with i hi
    exact ((μ i).normalize_eq_of_nonzero hi s).symm
  exact FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass hnorm hmass

theorem cylinder_isOpen {ι : Type*} (t : CylinderTest ι) :
    IsOpen (cylinder t) := by
  have heq : cylinder t = ⋂ v ∈ t,
      (fun x : ι → ℝ => x v.1) ⁻¹' Ioo (v.2.1 : ℝ) (v.2.2 : ℝ) := by
    ext x
    simp [cylinder]
  rw [heq]
  exact isOpen_biInter_finset fun v _ => isOpen_Ioo.preimage (continuous_apply v.1)

theorem cylinder_piSystem {ι : Type*} :
    IsPiSystem (Set.range (cylinder (ι := ι))) := by
  classical
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ _
  exact ⟨s ∪ t, cylinder_union s t⟩

theorem exists_cylinder_nhds_subset {ι : Type*} (u : Set (ι → ℝ))
    (hu : IsOpen u) (x : ι → ℝ) (hx : x ∈ u) :
    ∃ t : CylinderTest ι, cylinder t ∈ 𝓝 x ∧ cylinder t ⊆ u := by
  classical
  obtain ⟨v, ⟨U, F, hU, rfl⟩, hxv, hvu⟩ :=
    (isTopologicalBasis_pi (fun _ : ι => Real.isTopologicalBasis_Ioo_rat)).exists_subset_of_mem_open hx hu
  have hchoices : ∀ i : F, ∃ a b : ℚ, a < b ∧ U i = Ioo (a : ℝ) (b : ℝ) := by
    intro i
    have hi := hU i i.property
    simpa only [mem_iUnion, mem_singleton_iff, exists_prop, eq_comm] using hi
  choose a b hab hinterval using hchoices
  let t : CylinderTest ι := F.attach.image (fun i => (i.val, a i, b i))
  have heq : cylinder t = (F : Set ι).pi U := by
    ext y
    simp only [cylinder, mem_ofPred_eq, t, Finset.mem_image, Finset.mem_attach,
      true_and, Set.mem_pi, Finset.mem_coe]
    constructor
    · intro h i hi
      have hv := h (i, a ⟨i, hi⟩, b ⟨i, hi⟩) ⟨⟨i, hi⟩, rfl⟩
      simpa only [hinterval ⟨i, hi⟩, mem_Ioo] using hv
    · intro h v hv
      obtain ⟨i, rfl⟩ := hv
      simpa only [hinterval i, mem_Ioo] using h i i.property
  refine ⟨t, ?_, heq ▸ hvu⟩
  exact (cylinder_isOpen t).mem_nhds (heq.symm ▸ hxv)

theorem tendsto_finiteMeasure_of_cylinders
    {κ ι : Type*} [Countable κ] {l : Filter ι} [l.IsCountablyGenerated]
    {μ : ι → FiniteMeasure (κ → ℝ)} {ν : FiniteMeasure (κ → ℝ)}
    (h : ∀ t : CylinderTest κ,
      Tendsto (fun i => μ i (cylinder t)) l (𝓝 (ν (cylinder t)))) :
    Tendsto μ l (𝓝 ν) := by
  apply tendsto_finiteMeasure_of_piSystem cylinder_piSystem
  · rintro _ ⟨t, rfl⟩
    exact (cylinder_isOpen t).measurableSet
  · intro u hu x hx
    obtain ⟨t, htx, htu⟩ := exists_cylinder_nhds_subset u hu x hx
    exact ⟨cylinder t, ⟨t, rfl⟩, htx, htu⟩
  · simpa only [cylinder_empty, FiniteMeasure.mass] using h ∅
  · rintro _ ⟨t, rfl⟩
    exact h t

open ProductModel

attribute [local instance] OAI.Invariant233.SamplingCylinderWeak.instOpensMeasurableSpaceEndpointPair
theorem cutCoordinates_measurable : Measurable cutCoordinates := by
  have hr : Measurable circleRepresentative :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  apply Measurable.of_eval
  rintro ⟨b, i⟩
  cases b
  · exact hr.comp ((measurable_pi_apply i).comp measurable_fst)
  · exact hr.comp ((measurable_pi_apply i).comp measurable_snd)

theorem quotientCoordinates_continuous : Continuous quotientCoordinates := by
  unfold quotientCoordinates
  fun_prop

theorem endpointCylinder_measurable (t : CylinderTest (Bool × ℕ)) :
    MeasurableSet (endpointCylinder t) :=
  (cylinder_isOpen t).measurableSet.preimage cutCoordinates_measurable

@[simp] theorem map_quotient_cut (μ : FiniteMeasure EndpointPair) :
    (μ.map cutCoordinates).map quotientCoordinates = μ := by
  apply Subtype.ext
  change Measure.map quotientCoordinates (Measure.map cutCoordinates (μ : Measure EndpointPair)) = _
  rw [Measure.map_map quotientCoordinates_continuous.measurable cutCoordinates_measurable]
  have heq : quotientCoordinates ∘ cutCoordinates = id := funext quotient_cutCoordinates
  rw [heq, Measure.map_id]
  rfl

theorem tendsto_endpoint_of_cylinders
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μ : ι → FiniteMeasure EndpointPair} {ν : FiniteMeasure EndpointPair}
    (h : ∀ t : CylinderTest (Bool × ℕ),
      Tendsto (fun i => μ i (endpointCylinder t)) l (𝓝 (ν (endpointCylinder t)))) :
    Tendsto μ l (𝓝 ν) := by
  have hlift : Tendsto (fun i => (μ i).map cutCoordinates) l
      (𝓝 (ν.map cutCoordinates)) := by
    apply tendsto_finiteMeasure_of_cylinders
    intro t
    simpa only [FiniteMeasure.map_apply _ cutCoordinates_measurable
      (cylinder_isOpen t).measurableSet, endpointCylinder] using h t
  have hquot := FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlift
    quotientCoordinates_continuous
  simpa only [map_quotient_cut] using hquot

theorem weaklyConverges_of_cylinders
    {μ : ℕ → Measure EndpointPair} {ν : Measure EndpointPair}
    (hμ : ∀ n, IsFiniteMeasure (μ n)) (hν : IsFiniteMeasure ν)
    (h : ∀ t : CylinderTest (Bool × ℕ),
      Tendsto (fun n => μ n (endpointCylinder t)) atTop (𝓝 (ν (endpointCylinder t)))) :
    WeaklyConverges μ ν := by
  let μ' : ℕ → FiniteMeasure EndpointPair := fun n => ⟨μ n, hμ n⟩
  let ν' : FiniteMeasure EndpointPair := ⟨ν, hν⟩
  have hweak : Tendsto μ' atTop (𝓝 ν') := by
    apply tendsto_endpoint_of_cylinders
    intro t
    exact (ENNReal.tendsto_toNNReal (by let := hν; exact measure_ne_top _ _)).comp (h t)
  intro φ
  exact (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak)
    (BoundedContinuousFunction.mkOfCompact φ)

end Invariant233.SamplingCylinderWeak

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductIdealCylinderLimit
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.cylinderCoordinateSet_empty _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators

namespace Invariant233.ProductModel.IdealSampling

local instance instOpensMeasurableSpaceEndpointPair : OpensMeasurableSpace EndpointPair := inferInstance
open SamplingCylinderWeak

private theorem mem_frontier_preimage_of_continuousAt
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X} {s : Set Y} (hf : ContinuousAt f x)
    (hx : x ∈ frontier (f ⁻¹' s)) : f x ∈ frontier s := by
  rw [frontier_eq_closure_inter_closure] at hx ⊢
  constructor
  · exact closure_mono (image_preimage_subset f s) (mem_closure_image hf hx.1)
  · exact closure_mono (image_preimage_subset f sᶜ) (mem_closure_image hf hx.2)

private theorem null_frontier_preimage_of_ae_continuousAt
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] {μ : Measure X} {f : X → Y} {s : Set Y}
    (hf : ∀ᵐ x ∂μ, ContinuousAt f x) (hs : μ (f ⁻¹' frontier s) = 0) :
    μ (frontier (f ⁻¹' s)) = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hf, measure_eq_zero_iff_ae_notMem.mp hs] with x hfx hsx
  exact fun hx => hsx (mem_frontier_preimage_of_continuousAt hfx hx)

theorem triangularLaw_coordinate_singleton (I : Finset ℕ) (b : Bool) (i : ℕ)
    (a : Circle) :
    triangularLaw I {xy | (if b then xy.2 i else xy.1 i) = a} = 0 := by
  have hfst : (baseMeasure.prod baseMeasure) {xz : EndpointPair | xz.1 i = a} = 0 := by
    have hp := (measurePreserving_eval_infinitePi (fun _ : ℕ => circleMeasure) i).comp
      (measurePreserving_fst (μ := baseMeasure) (ν := baseMeasure))
    have he := hp.measure_preimage (measurableSet_singleton a).nullMeasurableSet
    simpa [Sampling.circleMeasure_singleton, Function.comp_def, Set.preimage, Set.mem_singleton_iff] using he
  have hsnd : (baseMeasure.prod baseMeasure) {xz : EndpointPair | xz.2 i = a} = 0 := by
    have hp := (measurePreserving_eval_infinitePi (fun _ : ℕ => circleMeasure) i).comp
      (measurePreserving_snd (μ := baseMeasure) (ν := baseMeasure))
    have he := hp.measure_preimage (measurableSet_singleton a).nullMeasurableSet
    simpa [Sampling.circleMeasure_singleton, Function.comp_def, Set.preimage, Set.mem_singleton_iff] using he
  rw [triangularLaw, Measure.map_apply (Sampling.endpointMap_measurable I)]
  · apply le_antisymm ((Measure.restrict_le_self _).trans_eq ?_) (bot_le)
    cases b
    · simpa using hfst
    · by_cases hi : i ∈ I
      · simpa [selectedEndpoint, hi] using hsnd
      · simpa [selectedEndpoint, hi] using hfst
  · cases b <;> simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
    · exact measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_fst) measurable_const
    · exact measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_snd) measurable_const

theorem triangularLaw_cutCoordinate_singleton (I : Finset ℕ) (k : Bool × ℕ)
    (a : ℝ) : triangularLaw I {xy | cutCoordinates xy k = a} = 0 := by
  apply measure_mono_null _ (triangularLaw_coordinate_singleton I k.1 k.2 (a : Circle))
  intro xy hxy
  change circleRepresentative (if k.1 then xy.2 k.2 else xy.1 k.2) = a at hxy
  change (if k.1 then xy.2 k.2 else xy.1 k.2) = (a : Circle)
  rw [← hxy]
  exact AddCircle.coe_equivIco.symm

theorem triangularLaw_ae_continuousAt_cutCoordinate (I : Finset ℕ) (k : Bool × ℕ) :
    ∀ᵐ xy ∂triangularLaw I, ContinuousAt (fun z => cutCoordinates z k) xy := by
  have hn : ∀ᵐ xy ∂triangularLaw I,
      (if k.1 then xy.2 k.2 else xy.1 k.2) ≠ (0 : Circle) :=
    by simpa only [not_not] using (ae_iff.mpr (by
      simpa only [not_not] using triangularLaw_coordinate_singleton I k.1 k.2 0))
  filter_upwards [hn] with xy hxy
  have hc : Continuous (fun z : EndpointPair => if k.1 then z.2 k.2 else z.1 k.2) := by
    cases k.1 <;> simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true] <;> fun_prop
  have hr : ContinuousAt circleRepresentative (if k.1 then xy.2 k.2 else xy.1 k.2) :=
    continuousAt_subtype_val.comp (AddCircle.continuousAt_equivIco (1 : ℝ) 0 hxy)
  exact hr.comp (f := fun z : EndpointPair => if k.1 then z.2 k.2 else z.1 k.2) hc.continuousAt

theorem triangularLaw_null_frontier_interval (I : Finset ℕ) (k : Bool × ℕ)
    (a b : ℝ) :
    triangularLaw I (frontier {xy | a < cutCoordinates xy k ∧ cutCoordinates xy k < b}) = 0 := by
  change triangularLaw I (frontier ((fun xy => cutCoordinates xy k) ⁻¹' Ioo a b)) = 0
  apply null_frontier_preimage_of_ae_continuousAt
    (triangularLaw_ae_continuousAt_cutCoordinate I k)
  by_cases hab : a < b
  · rw [frontier_Ioo hab]
    have he : (fun xy => cutCoordinates xy k) ⁻¹' ({a, b} : Set ℝ) =
        {xy | cutCoordinates xy k = a} ∪ {xy | cutCoordinates xy k = b} := by
      ext xy
      simp
    rw [he]
    exact measure_union_null (triangularLaw_cutCoordinate_singleton I k a)
      (triangularLaw_cutCoordinate_singleton I k b)
  · simp [Set.Ioo_eq_empty hab]

theorem triangularLaw_null_frontier_endpointCylinder (I : Finset ℕ)
    (t : CylinderTest (Bool × ℕ)) :
    triangularLaw I (frontier (endpointCylinder t)) = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [endpointCylinder]
  | @insert v t hv ih =>
    have he : endpointCylinder (insert v t) =
        {xy | (v.2.1 : ℝ) < cutCoordinates xy v.1 ∧
          cutCoordinates xy v.1 < (v.2.2 : ℝ)} ∩ endpointCylinder t := by
      ext xy
      simp [endpointCylinder, SamplingCylinderWeak.cylinder]
    rw [he]
    apply measure_mono_null (frontier_inter_subset _ _)
    exact measure_union_null
      (measure_inter_null_of_null_left _ (triangularLaw_null_frontier_interval I v.1 _ _))
      (measure_inter_null_of_null_right _ ih)

theorem finiteMeasure_tendsto_apply_of_null_frontier
    {X ι : Type*} [Nonempty X] [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {l : Filter ι} {μ : ι → FiniteMeasure X} {ν : FiniteMeasure X}
    (hμ : Tendsto μ l (𝓝 ν)) {E : Set X}
    (hE : (ν : Measure X) (frontier E) = 0) :
    Tendsto (fun i => μ i E) l (𝓝 (ν E)) := by
  by_cases hν : ν = 0
  · subst ν
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ≥0)) l (𝓝 0)))
      (by simpa using hμ.mass)
    · intro i; exact bot_le
    · intro i; exact (μ i).apply_le_mass E
  · have hnorm := FiniteMeasure.tendsto_normalize_of_tendsto hμ hν
    have hEnorm : ν.normalize (frontier E) = 0 := by
      rw [ν.normalize_eq_of_nonzero hν]
      have hzero : ν (frontier E) = 0 := by
        change ((ν : Measure X) (frontier E)).toNNReal = 0
        rw [hE]
        rfl
      rw [hzero, mul_zero]
    have h := hμ.mass.mul
      (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hnorm hEnorm)
    simpa only [← FiniteMeasure.self_eq_mass_mul_normalize] using h

theorem cylinder_real_tendsto_of_weaklyConverges
    (I : Finset ℕ) {μ : ℕ → Measure EndpointPair}
    (hfinite : ∀ n, IsFiniteMeasure (μ n))
    (hμ : WeaklyConverges μ (triangularLaw I))
    (t : CylinderTest (Bool × ℕ)) :
    Tendsto (fun n => (μ n).real (endpointCylinder t)) atTop
      (𝓝 ((triangularLaw I).real (endpointCylinder t))) := by
  let μ' : ℕ → FiniteMeasure EndpointPair := fun n => ⟨μ n, hfinite n⟩
  let ν : FiniteMeasure EndpointPair := ⟨triangularLaw I, Sampling.triangularLaw_finite I⟩
  have hw : Tendsto μ' atTop (𝓝 ν) :=
    (weaklyConverges_iff_tendsto μ' ν).mp hμ
  have ht := finiteMeasure_tendsto_apply_of_null_frontier hw
    (triangularLaw_null_frontier_endpointCylinder I t)
  have hr := NNReal.continuous_coe.continuousAt.tendsto.comp ht
  change Tendsto (fun n => (((μ n) (endpointCylinder t)).toNNReal : ℝ)) atTop
    (𝓝 (((triangularLaw I) (endpointCylinder t)).toNNReal : ℝ))
  exact hr

theorem law_cylinder_real_tendsto_of_productScaleLaws (I : Finset ℕ)
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (t : CylinderTest (Bool × ℕ)) :
    Tendsto (fun l => (law I (Finset.range (p.prefixCount (l + 1)))
      ((p.m l : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m l : ℝ) ^ 2)).real
        (endpointCylinder t)) atTop
      (𝓝 ((triangularLaw I).real (endpointCylinder t))) :=
  cylinder_real_tendsto_of_weaklyConverges I (fun _ => inferInstance)
    (law_weaklyConverges_of_productScaleLaws I hp) t

end Invariant233.ProductModel.IdealSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductIdealSamplingKernel
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingCylinderWeak.map_quotient_cut _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.ScalarSampling.TestedTriangular.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedTriangular.secondKernel_univ_univ _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal
namespace Invariant233.ProductModel.IdealSampling

theorem integral_uniform_displacement (x : Circle) {a : ℝ} (ha : a ≠ 0)
    (f : Circle → ℝ) (hf : Measurable f) :
    (∫ z, f (x + ((a * circleRepresentative z : ℝ) : Circle)) ∂circleMeasure) =
      a⁻¹ * ∫ t in (0 : ℝ)..a, f (x + (t : Circle)) := by
  have hm : Measurable (fun t : ℝ => f (x + ((a * t : ℝ) : Circle))) := by
    apply hf.comp
    fun_prop
  have he := integral_map (μ := circleMeasure)
    Sampling.representative_measurable.aemeasurable hm.aestronglyMeasurable
  rw [Sampling.representative_map_haar] at he
  calc
    _ = ∫ t, f (x + ((a * t : ℝ) : Circle)) ∂volume.restrict (Ico (0 : ℝ) 1) := he.symm
    _ = ∫ t in (0 : ℝ)..1, f (x + ((a * t : ℝ) : Circle)) := by
      rw [restrict_Ico_eq_restrict_Ioc, intervalIntegral.integral_of_le (by norm_num)]
    _ = _ := by
      simpa only [mul_zero, mul_one, smul_eq_mul] using
        (intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
          (fun t : ℝ => f (x + (t : Circle))) ha)

theorem integral_rawKernel_test {h α s : ℝ}
    (hcut : α ≤ ScalarSampling.delta s)
    (ha0 : 0 < h * ScalarSampling.delta s) (ha1 : h * ScalarSampling.delta s ≤ 1)
    (x : Circle) (f : Circle → ℝ) :
    (∫ t in (0 : ℝ)..1, ScalarSampling.rawKernel h α s t * f (x + (t : Circle))) =
      (h * ScalarSampling.delta s)⁻¹ *
        ∫ t in (0 : ℝ)..(h * ScalarSampling.delta s), f (x + (t : Circle)) := by
  let a := h * ScalarSampling.delta s
  have hh : (fun t : ℝ => ScalarSampling.rawKernel h α s t * f (x + (t : Circle))) =
      (Ioo 0 a).indicator (fun t => a⁻¹ * f (x + (t : Circle))) := by
    funext t
    simp only [ScalarSampling.rawKernel, ite_eq_left hcut]
    by_cases ht : t ∈ Ioo 0 a <;> simp [a, Set.indicator, ht] at *
  rw [hh, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
  have hsub : Ioo (0 : ℝ) a ⊆ Ioc 0 1 := by
    intro t ht
    exact ⟨ht.1, ht.2.le.trans ha1⟩
  rw [inter_eq_left.mpr hsub, restrict_Ioo_eq_restrict_Ioc, integral_const_mul,
    ← intervalIntegral.integral_of_le ha0.le]

theorem integral_displacement_eq_rawKernel {h α : ℝ} (x : Circle)
    (hcut : α ≤ ScalarSampling.delta (circleRepresentative x))
    (ha0 : 0 < h * ScalarSampling.delta (circleRepresentative x))
    (ha1 : h * ScalarSampling.delta (circleRepresentative x) ≤ 1)
    (f : Circle → ℝ) (hf : Measurable f) :
    (∫ z, f (x + ((h * ScalarSampling.delta (circleRepresentative x) *
      circleRepresentative z : ℝ) : Circle)) ∂circleMeasure) =
      ∫ t in (0 : ℝ)..1, ScalarSampling.rawKernel h α (circleRepresentative x) t *
        f (x + (t : Circle)) := by
  rw [integral_uniform_displacement x ha0.ne' f hf,
    integral_rawKernel_test hcut ha0 ha1]

theorem integral_cutoff_displacement_eq_rawKernel {h α : ℝ}
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hα : 0 < α)
    (x : Circle) (f : Circle → ℝ) (hf : Measurable f) :
    (if α ≤ ScalarSampling.delta (circleRepresentative x) then
      ∫ z, f (x + ((h * ScalarSampling.delta (circleRepresentative x) *
        circleRepresentative z : ℝ) : Circle)) ∂circleMeasure else 0) =
      ∫ t in (0 : ℝ)..1, ScalarSampling.rawKernel h α (circleRepresentative x) t *
        f (x + (t : Circle)) := by
  by_cases hcut : α ≤ ScalarSampling.delta (circleRepresentative x)
  · rw [ite_eq_left hcut]
    apply integral_displacement_eq_rawKernel x hcut
      (mul_pos hh0 (hα.trans_le hcut)) _ f hf
    have hx := Sampling.representative_mem_Ico x
    have hd : ScalarSampling.delta (circleRepresentative x) ≤ 1 :=
      (min_le_left _ _).trans hx.2.le
    exact (mul_le_mul_of_nonneg_right hh1 (hα.trans_le hcut).le).trans
      (by simpa using hd)
  · simp only [ite_eq_right hcut, ScalarSampling.rawKernel, zero_mul,
      intervalIntegral.integral_zero]

theorem integral_triangular_endpoint (x : Circle) (f : Circle → ℝ)
    (hf : Measurable f) :
    (∫ z, if circleRepresentative x < circleRepresentative z then f z else 0
      ∂circleMeasure) =
      ∫ y in (circleRepresentative x)..1, f (y : Circle) := by
  let s := circleRepresentative x
  have hx := Sampling.representative_mem_Ico x
  have hm : Measurable (fun y : ℝ => (Ioi s).indicator (fun y => f (y : Circle)) y) := by
    apply Measurable.indicator _ measurableSet_Ioi
    exact hf.comp (by fun_prop)
  have he := integral_map (μ := circleMeasure)
    Sampling.representative_measurable.aemeasurable hm.aestronglyMeasurable
  rw [Sampling.representative_map_haar] at he
  have hcoe (z : Circle) : ((circleRepresentative z : ℝ) : Circle) = z :=
    ProductCocycle.coe_representative z
  calc
    _ = ∫ z, (Ioi s).indicator (fun y => f (y : Circle)) (circleRepresentative z)
        ∂circleMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by simp [Set.indicator, hcoe, s])
    _ = ∫ y, (Ioi s).indicator (fun y => f (y : Circle)) y
        ∂volume.restrict (Ico (0 : ℝ) 1) := he.symm
    _ = ∫ y in s..1, f (y : Circle) := by
      rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
      have hset : Ioi s ∩ Ico (0 : ℝ) 1 = Ioo s 1 := by
        ext y
        constructor
        · intro hy
          exact ⟨hy.1, hy.2.2⟩
        · intro hy
          exact ⟨hy.1, ⟨hx.1.trans hy.1.le, hy.2⟩⟩
      rw [hset, restrict_Ioo_eq_restrict_Ioc, intervalIntegral.integral_of_le hx.2.le]

theorem integral_triangular_endpoint_eq_kernel (x : Circle) (f : Circle → ℝ)
    (hf : Measurable f) :
    (∫ z, if circleRepresentative x < circleRepresentative z then f z else 0
      ∂circleMeasure) =
      ∫ t in (0 : ℝ)..1, ScalarSampling.triangularKernel (circleRepresentative x) t *
        f (x + (t : Circle)) := by
  let s := circleRepresentative x
  have hx := Sampling.representative_mem_Ico x
  have hh : (fun t : ℝ => ScalarSampling.triangularKernel s t * f (x + (t : Circle))) =
      (Ioo 0 (1 - s)).indicator (fun t => f (x + (t : Circle))) := by
    funext t
    simpa only [ScalarSampling.triangularKernel, one_mul] using
      (Set.indicator_mul_left (Ioo 0 (1 - s)) (fun _ : ℝ => (1 : ℝ))
        (fun t => f (x + (t : Circle))) (i := t)).symm
  have hphase : (∫ t in (0 : ℝ)..1,
      ScalarSampling.triangularKernel s t * f (x + (t : Circle))) =
      ∫ t in (0 : ℝ)..(1 - s), f (x + (t : Circle)) := by
    rw [hh, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
    have hsub : Ioo (0 : ℝ) (1 - s) ⊆ Ioc 0 1 := by
      intro t ht
      exact ⟨ht.1, ht.2.le.trans (by dsimp [s] <;> linarith [hx.1])⟩
    rw [inter_eq_left.mpr hsub, restrict_Ioo_eq_restrict_Ioc,
      intervalIntegral.integral_of_le (sub_nonneg.mpr hx.2.le)]
  rw [integral_triangular_endpoint x f hf, hphase]
  have hcoe : ((s : ℝ) : Circle) = x := ProductCocycle.coe_representative x
  have he := intervalIntegral.integral_comp_add_left (a := 0) (b := 1 - s)
    (fun y : ℝ => f (y : Circle)) s
  simpa only [AddCircle.coe_add, hcoe, add_zero, add_sub_cancel] using he.symm

end Invariant233.ProductModel.IdealSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductIdealSamplingProduct
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingCylinderWeak.map_quotient_cut _root_.OAI.Invariant233.SamplingCylinderWeak.quotient_cutCoordinates _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.ScalarSampling.TestedTriangular.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedTriangular.secondKernel_univ_univ _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Invariant233.ProductModel.IdealSampling

theorem coordinateEvent_measurable (I : Finset ℕ) (α : ℝ) (i : ℕ) :
    MeasurableSet (coordinateEvent I α i) := by
  by_cases hi : i ∈ I
  · simp only [coordinateEvent, hi, ite_true, if_true]
    exact measurableSet_lt (Sampling.representative_measurable.comp measurable_fst)
      (Sampling.representative_measurable.comp measurable_snd)
  · simp only [coordinateEvent, hi, ite_false, if_false]
    have hx := Sampling.representative_measurable.comp
      (measurable_fst : Measurable (Prod.fst : Circle × Circle → Circle))
    exact measurableSet_le measurable_const (hx.min (measurable_const.sub hx))

theorem mem_retained_iff {I D : Finset ℕ} (hID : I ⊆ D) (α : ℝ)
    (xz : EndpointPair) :
    xz ∈ triangularEvent I ∩ cutoffEvent I D α ↔
      ∀ i : D, (xz.1 i, xz.2 i) ∈ coordinateEvent I α i := by
  constructor
  · rintro ⟨ht, hc⟩ i
    by_cases hi : (i : ℕ) ∈ I
    · simpa [coordinateEvent, hi] using ht i hi
    · simpa [coordinateEvent, hi] using hc i (Finset.mem_sdiff.mpr ⟨i.property, hi⟩)
  · intro hall
    constructor
    · intro i hi
      simpa [coordinateEvent, hi] using hall ⟨i, hID hi⟩
    · intro i hi
      simpa [coordinateEvent, (Finset.mem_sdiff.mp hi).2] using
        hall ⟨i, (Finset.mem_sdiff.mp hi).1⟩

theorem retained_product_eq {I D : Finset ℕ} (hID : I ⊆ D) (h α : ℝ)
    (F : D → Circle × Circle → ℝ) (xz : EndpointPair) :
    (triangularEvent I ∩ cutoffEvent I D α).indicator
      (fun xz => ∏ i : D, F i (xz.1 i, endpoint I D h xz.1 xz.2 i)) xz =
      ∏ i : D, (coordinateEvent I α i).indicator
        (F i ∘ coordinateEndpoint I h i) (xz.1 i, xz.2 i) := by
  classical
  by_cases hx : xz ∈ triangularEvent I ∩ cutoffEvent I D α
  · rw [Set.indicator_of_mem hx]
    apply Finset.prod_congr rfl
    intro i _
    rw [Set.indicator_of_mem ((mem_retained_iff hID α xz).mp hx i)]
    simp [coordinateEndpoint, endpoint, i.property]
  · rw [Set.indicator_of_notMem hx]
    have hn : ¬ ∀ i : D, (xz.1 i, xz.2 i) ∈ coordinateEvent I α i :=
      fun hh => hx ((mem_retained_iff hID α xz).mpr hh)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Set.indicator_of_notMem hi _

theorem integral_law_product {I D : Finset ℕ} (hID : I ⊆ D) (h α : ℝ)
    (F : D → Circle × Circle → ℝ) (hF : ∀ i, Measurable (F i)) :
    (∫ xy, ∏ i : D, F i (xy.1 i, xy.2 i) ∂law I D h α) =
      ∏ i : D, ∫ p, (coordinateEvent I α i).indicator
        (F i ∘ coordinateEndpoint I h i) p ∂(circleMeasure.prod circleMeasure) := by
  classical
  let G : D → Circle × Circle → ℝ := fun i =>
    (coordinateEvent I α i).indicator (F i ∘ coordinateEndpoint I h i)
  have hG (i : D) : Measurable (G i) :=
    ((hF i).comp (coordinateEndpoint_measurable I h i)).indicator
      (coordinateEvent_measurable I α i)
  have htest : Measurable (fun xy : EndpointPair => ∏ i : D, F i (xy.1 i, xy.2 i)) := by
    apply Finset.measurable_prod
    intro i _
    exact (hF i).comp (((measurable_pi_apply (i : ℕ)).comp measurable_fst).prodMk
      ((measurable_pi_apply (i : ℕ)).comp measurable_snd))
  have hp : Measurable (fun p : D → Circle × Circle => ∏ i : D, G i (p i)) := by
    apply Finset.measurable_prod
    intro i _
    exact (hG i).comp (measurable_pi_apply i)
  rw [law, integral_map (endpointMap_measurable I D h).aemeasurable
    htest.aestronglyMeasurable]
  change (∫ xz, ∏ i : D, F i (xz.1 i, endpoint I D h xz.1 xz.2 i)
    ∂(sourceMeasure I).restrict (cutoffEvent I D α)) = _
  rw [sourceMeasure, Measure.restrict_restrict (cutoffEvent_measurable I D α),
    inter_comm, ← integral_indicator
      ((Sampling.triangularEvent_measurable I).inter (cutoffEvent_measurable I D α))]
  simp_rw [retained_product_eq hID h α F]
  have he := integral_map (μ := baseMeasure.prod baseMeasure)
    (measurePreserving_finite_coordinate_pairs D).measurable.aemeasurable
    hp.aestronglyMeasurable
  rw [(measurePreserving_finite_coordinate_pairs D).map_eq] at he
  change (∫ xz, ∏ i : D, G i (xz.1 i, xz.2 i) ∂baseMeasure.prod baseMeasure) = _
  rw [← he]
  exact integral_fintype_prod_eq_prod G

theorem integral_coordinate_eq_kernel (I : Finset ℕ) {h α : ℝ}
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hα : 0 < α) (i : ℕ)
    (F : Circle × Circle → ℝ) (hF : Measurable F)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ p, ‖F p‖ ≤ C) :
    (∫ p, (coordinateEvent I α i).indicator (F ∘ coordinateEndpoint I h i) p
      ∂circleMeasure.prod circleMeasure) =
      ∫ x, (∫ t in (0 : ℝ)..1, coordinateKernel I h α i (circleRepresentative x) t *
        F (x, x + (t : Circle))) ∂circleMeasure := by
  have hm := (hF.comp (coordinateEndpoint_measurable I h i)).indicator
    (coordinateEvent_measurable I α i)
  have hint : Integrable ((coordinateEvent I α i).indicator
      (F ∘ coordinateEndpoint I h i)) (circleMeasure.prod circleMeasure) := by
    apply (integrable_const C).mono' hm.aestronglyMeasurable
    filter_upwards [] with p
    by_cases hp : p ∈ coordinateEvent I α i
    · simpa [Set.indicator_of_mem hp] using hbound (coordinateEndpoint I h i p)
    · simp [Set.indicator_of_notMem hp, hC]
  rw [integral_prod _ hint]
  apply integral_congr_ae
  filter_upwards [] with x
  have hfx : Measurable (fun z : Circle => F (x, z)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  by_cases hi : i ∈ I
  · simpa [coordinateEvent, coordinateEndpoint, coordinateKernel, hi,
      Set.indicator, Function.comp_def] using
      integral_triangular_endpoint_eq_kernel x (fun z => F (x, z)) hfx
  · have he := integral_cutoff_displacement_eq_rawKernel hh0 hh1 hα
      x (fun z => F (x, z)) hfx
    by_cases hc : α ≤ ScalarSampling.delta (circleRepresentative x)
    · simpa [coordinateEvent, coordinateEndpoint, coordinateKernel, hi, hc,
        Set.indicator, Function.comp_def] using he
    · simpa [coordinateEvent, coordinateEndpoint, coordinateKernel, hi, hc,
        Set.indicator, Function.comp_def] using he

theorem integral_law_product_eq_kernels {I D : Finset ℕ} (hID : I ⊆ D)
    {h α : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hα : 0 < α)
    (F : D → Circle × Circle → ℝ) (hF : ∀ i, Measurable (F i))
    (C : D → ℝ) (hC : ∀ i, 0 ≤ C i) (hbound : ∀ i p, ‖F i p‖ ≤ C i) :
    (∫ xy, ∏ i : D, F i (xy.1 i, xy.2 i) ∂law I D h α) =
      ∏ i : D, ∫ x, (∫ t in (0 : ℝ)..1,
        coordinateKernel I h α i (circleRepresentative x) t *
          F i (x, x + (t : Circle))) ∂circleMeasure := by
  rw [integral_law_product hID h α F hF]
  apply Finset.prod_congr rfl
  intro i _
  exact integral_coordinate_eq_kernel I hh0 hh1 hα i (F i) (hF i) (hC i) (hbound i)

end Invariant233.ProductModel.IdealSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductOrbitMarginals
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.TailTrimming

theorem orbitPairMeasure_first_marginal (θ : ℕ → ℝ) (n : ℕ)
    (w : Base → ℝ≥0∞) :
    (orbitPairMeasure θ n w).map Prod.fst = baseMeasure.withDensity w := by
  exact WeightedGraphMarginals.map_fst_graph _
    (ProductCocycle.measurePreserving_rotate θ (n : ℤ)).measurable

theorem orbitAverageMeasure_first_marginal (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ≥0∞) (hw : ∀ n ∈ N, Measurable (w n)) :
    (orbitAverageMeasure θ N w).map Prod.fst =
      baseMeasure.withDensity (fun x => (N.card : ℝ≥0∞)⁻¹ * ∑ n ∈ N, w n x) := by
  rw [orbitAverageMeasure, Measure.map_smul,
    WeightedGraphMarginals.map_finset_sum _ _ measurable_fst]
  simp_rw [orbitPairMeasure_first_marginal]
  rw [show (fun x => (N.card : ℝ≥0∞)⁻¹ * ∑ n ∈ N, w n x) =
    (N.card : ℝ≥0∞)⁻¹ • (fun x => ∑ n ∈ N, w n x) from rfl,
    withDensity_smul _ (Finset.measurable_sum N hw),
    WeightedGraphMarginals.withDensity_finset_sum baseMeasure N w hw]

theorem orbitPairMeasure_restrict (θ : ℕ → ℝ) (n : ℕ)
    (w : Base → ℝ≥0∞) (A : Set EndpointPair) (hA : MeasurableSet A) :
    (orbitPairMeasure θ n w).restrict A =
      orbitPairMeasure θ n ((orbitPairMap θ n ⁻¹' A).indicator w) := by
  unfold orbitPairMeasure
  rw [Measure.restrict_map (measurable_orbitPairMap θ n) hA,
    restrict_withDensity ((measurable_orbitPairMap θ n) hA),
    ← withDensity_indicator ((measurable_orbitPairMap θ n) hA)]

theorem orbitAverageMeasure_restrict (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ≥0∞) (A : Set EndpointPair) (hA : MeasurableSet A) :
    (orbitAverageMeasure θ N w).restrict A =
      orbitAverageMeasure θ N (fun n => (orbitPairMap θ n ⁻¹' A).indicator (w n)) := by
  unfold orbitAverageMeasure
  rw [Measure.restrict_smul]
  have hsum : (∑ n ∈ N, orbitPairMeasure θ n (w n)).restrict A =
      ∑ n ∈ N, (orbitPairMeasure θ n (w n)).restrict A := by
    simp only [← Measure.restrictₗ_apply, map_sum]
  rw [hsum]
  congr 1
  exact Finset.sum_congr rfl fun n _ => orbitPairMeasure_restrict θ n (w n) A hA

theorem ofReal_average_eq (N : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ n ∈ N, 0 ≤ w n) :
    ENNReal.ofReal ((N.card : ℝ)⁻¹ * ∑ n ∈ N, w n) =
      (N.card : ℝ≥0∞)⁻¹ * ∑ n ∈ N, ENNReal.ofReal (w n) := by
  rcases N.eq_empty_or_nonempty with rfl | hN
  · simp
  have hc : 0 < (N.card : ℝ) := by exact_mod_cast hN.card_pos
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), ENNReal.ofReal_inv_of_pos hc,
    ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg hw]

theorem orbitAverageMeasure_first_marginal_real (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ) (hw : ∀ n ∈ N, Measurable (w n))
    (hw0 : ∀ n ∈ N, ∀ x, 0 ≤ w n x) :
    (orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (w n x))).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal
        ((N.card : ℝ)⁻¹ * ∑ n ∈ N, w n x)) := by
  rw [orbitAverageMeasure_first_marginal θ N _ (fun n hn => (hw n hn).ennreal_ofReal)]
  congr 1
  funext x
  exact (ofReal_average_eq N (fun n => w n x) (fun n hn => hw0 n hn x)).symm

end Invariant233.ProductModel.TailTrimming

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductOrbitTests
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingCylinderWeak.map_quotient_cut _root_.OAI.Invariant233.SamplingCylinderWeak.quotient_cutCoordinates _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.TailTrimming

theorem measurable_orbitTestWeight (θ : ℕ → ℝ) (A : Set EndpointPair)
    (hA : MeasurableSet A) (w : ℕ → Base → ℝ) (n : ℕ)
    (hw : Measurable (w n)) : Measurable (orbitTestWeight θ A w n) :=
  hw.indicator ((measurable_orbitPairMap θ n) hA)

theorem orbitTestWeight_nonneg (θ : ℕ → ℝ) (A : Set EndpointPair)
    (w : ℕ → Base → ℝ) (n : ℕ) (hw0 : ∀ x, 0 ≤ w n x) (x : Base) :
    0 ≤ orbitTestWeight θ A w n x :=
  Set.indicator_nonneg (fun x _ => hw0 x) x

theorem orbitAverageMeasure_restrict_real (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ) (A : Set EndpointPair) (hA : MeasurableSet A) :
    (orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (w n x))).restrict A =
      orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (orbitTestWeight θ A w n x)) := by
  rw [orbitAverageMeasure_restrict θ N _ A hA]
  congr 1
  funext n x
  by_cases hx : orbitPairMap θ n x ∈ A <;>
    simp [orbitTestWeight, hx]

theorem orbitAverageMeasure_restrict_first_marginal_real (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ) (hw : ∀ n ∈ N, Measurable (w n))
    (hw0 : ∀ n ∈ N, ∀ x, 0 ≤ w n x)
    (A : Set EndpointPair) (hA : MeasurableSet A) :
    ((orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (w n x))).restrict A).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal
        ((N.card : ℝ)⁻¹ * ∑ n ∈ N, orbitTestWeight θ A w n x)) := by
  rw [orbitAverageMeasure_restrict_real θ N w A hA]
  exact orbitAverageMeasure_first_marginal_real θ N _
    (fun n hn => measurable_orbitTestWeight θ A hA w n (hw n hn))
    (fun n hn => orbitTestWeight_nonneg θ A w n (hw0 n hn))

end Invariant233.ProductModel.TailTrimming

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingWeights
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.SamplingCylinderWeak.map_quotient_cut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.SamplingWeights

open ScalarSampling

theorem measurable_triangularKernel :
    Measurable (fun p : ℝ × ℝ => triangularKernel p.1 p.2) := by
  unfold triangularKernel
  simp only [Set.indicator_apply, mem_Ioo]
  exact Measurable.ite
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_const.sub measurable_fst)))
    measurable_const measurable_const

theorem measurable_coordinateWeight (I : Finset ℕ) (h α : ℝ) (i : ℕ) :
    Measurable (fun p : ℝ × ℝ => coordinateWeight I h α i p.1 p.2) := by
  by_cases hi : i ∈ I
  · simpa only [coordinateWeight, ite_eq_left hi] using measurable_triangularKernel
  · simpa only [coordinateWeight, ite_eq_right hi] using measurable_rawKernel_pair h α

theorem coordinateWeight_bounds (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) (s t : ℝ) :
    0 ≤ coordinateWeight I h α i s t ∧
      coordinateWeight I h α i s t ≤ height h α := by
  by_cases hi : i ∈ I
  · simp only [coordinateWeight, ite_eq_left hi, triangularKernel, Set.indicator_apply]
    split_ifs
    · exact ⟨zero_le_one, le_max_left _ _⟩
    · exact ⟨le_rfl, (by unfold height; positivity)⟩
  · simp only [coordinateWeight, ite_eq_right hi]
    exact ⟨(rawKernel_height hh hα).1,
      (rawKernel_height hh hα).2.trans (le_max_right _ _)⟩

theorem coordinateWeight_ne_zero_imp (I : Finset ℕ) {h α s t : ℝ}
    (hh : h ≤ 1) (hs : s ∈ Icc (0 : ℝ) 1) (i : ℕ)
    (hw : coordinateWeight I h α i s t ≠ 0) :
    0 < t ∧ t < 1 - s := by
  by_cases hi : i ∈ I
  · simp only [coordinateWeight, ite_eq_left hi, triangularKernel] at hw
    by_contra hn
    exact hw (Set.indicator_of_notMem (show t ∉ Ioo 0 (1 - s) from hn) _)
  · simp only [coordinateWeight, ite_eq_right hi, rawKernel] at hw
    split_ifs at hw with hc
    · have ht : t ∈ Ioo 0 (h * delta s) := by
        by_contra hn
        exact hw (Set.indicator_of_notMem hn _)
      refine ⟨ht.1, ht.2.trans_le ?_⟩
      calc
        h * delta s ≤ 1 * delta s :=
          mul_le_mul_of_nonneg_right hh (delta_nonneg hs)
        _ ≤ 1 - s := by simpa only [one_mul, delta] using min_le_right s (1 - s)
    · exact (hw rfl).elim

theorem measurable_orbitWeight (D I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) : Measurable (orbitWeight D I h α θ n) := by
  apply Finset.measurable_prod
  intro i hi
  exact (measurable_coordinateWeight I h α i).comp
    ((ProductCocycle.measurable_representative.comp (measurable_pi_apply i)).prodMk
      measurable_const)

theorem measurable_prefixWeight (D I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) : Measurable (prefixWeight D I h α θ n) := by
  apply Finset.measurable_prod
  intro i hi
  exact (measurable_coordinateWeight I h α i).comp
    ((ProductCocycle.measurable_representative.comp (measurable_pi_apply i)).prodMk
      measurable_const)

theorem orbitWeight_bounds (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (θ : ℕ → ℝ) (n : ℕ) (x : Base) :
    0 ≤ orbitWeight D I h α θ n x ∧
      orbitWeight D I h α θ n x ≤ height h α ^ D.card := by
  constructor
  · exact Finset.prod_nonneg fun i hi => (coordinateWeight_bounds I hh hα i _ _).1
  · calc
      orbitWeight D I h α θ n x ≤ ∏ _i ∈ D, height h α :=
        Finset.prod_le_prod (fun i hi => (coordinateWeight_bounds I hh hα i _ _).1)
          (fun i hi => (coordinateWeight_bounds I hh hα i _ _).2)
      _ = _ := by simp

theorem orbitWeight_ne_zero_prefix_order (D I : Finset ℕ) {h α : ℝ}
    (hh : h ≤ 1) (θ : ℕ → ℝ) (n : ℕ) (x : Base)
    (hw : orbitWeight D I h α θ n x ≠ 0) :
    ∀ i ∈ D, circleRepresentative (x i) <
      circleRepresentative (rotationIterate θ (n : ℤ) x i) := by
  intro i hi
  have hs := ProductCocycle.representative_mem_Ico (x i)
  have hwi := (Finset.prod_ne_zero_iff.mp hw) i hi
  have ht := coordinateWeight_ne_zero_imp I hh ⟨hs.1, hs.2.le⟩ i hwi
  change ProductCocycle.representative (x i) <
    ProductCocycle.representative (x i + (((n : ℝ) * θ i : ℝ) : Circle))
  rw [ProductCocycle.representative_add,
    TailTrimming.fract_add_eq_fract_add_fract]
  rw [Int.fract_eq_self.mpr ⟨by linarith [ht.1, hs.1], by linarith [ht.2]⟩]
  linarith [ht.1]

theorem orbitWeight_ae_prefix_order (D I : Finset ℕ) {h α : ℝ}
    (hh : h ≤ 1) (θ : ℕ → ℝ) (n : ℕ) :
    ∀ᵐ x ∂baseMeasure.withDensity (fun x => ENNReal.ofReal (orbitWeight D I h α θ n x)),
      ∀ i ∈ D, circleRepresentative (x i) ≤
        circleRepresentative (rotationIterate θ (n : ℤ) x i) := by
  apply (ae_withDensity_iff (measurable_orbitWeight D I h α θ n).ennreal_ofReal).2
  filter_upwards [] with x hx
  have hw : orbitWeight D I h α θ n x ≠ 0 := by
    intro hz
    exact hx (by rw [hz, ENNReal.ofReal_zero])
  exact fun i hi => (orbitWeight_ne_zero_prefix_order D I hh θ n x hw i hi).le

theorem memLp_orbitWeight (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (θ : ℕ → ℝ) (n : ℕ) (p : ℝ≥0∞) :
    MemLp (orbitWeight D I h α θ n) p baseMeasure := by
  apply MemLp.of_bound (measurable_orbitWeight D I h α θ n).aestronglyMeasurable
    (height h α ^ D.card)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (orbitWeight_bounds D I hh hα θ n x).1]
  exact (orbitWeight_bounds D I hh hα θ n x).2

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingWeightTests
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.SamplingCylinderWeak.map_quotient_cut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

namespace Invariant233.ProductModel.SamplingWeights

theorem measurable_testedCoordinateWeight (endpoint : Bool) (I : Finset ℕ)
    (h α : ℝ) (i : ℕ) {E F : Set ℝ} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    Measurable (fun p : ℝ × ℝ => testedCoordinateWeight endpoint I h α i E F p.1 p.2) := by
  have he : Measurable (E.indicator (fun _ : ℝ => (1 : ℝ))) :=
    measurable_const.indicator hE
  have hf : Measurable (F.indicator (fun _ : ℝ => (1 : ℝ))) :=
    measurable_const.indicator hF
  cases endpoint
  · exact ((measurable_coordinateWeight I h α i).mul (he.comp measurable_fst)).mul
      (hf.comp (measurable_fst.add measurable_snd).fract)
  · exact (((measurable_coordinateWeight I h α i).comp
      ((measurable_fst.sub measurable_snd).fract.prodMk measurable_snd)).mul
      (he.comp (measurable_fst.sub measurable_snd).fract)).mul
      (hf.comp measurable_fst)

theorem testedCoordinateWeight_bounds (endpoint : Bool) (I : Finset ℕ)
    {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (i : ℕ) (E F : Set ℝ) (s t : ℝ) :
    0 ≤ testedCoordinateWeight endpoint I h α i E F s t ∧
      testedCoordinateWeight endpoint I h α i E F s t ≤ height h α := by
  unfold testedCoordinateWeight
  dsimp only
  by_cases he : (if endpoint = true then Int.fract (s - t) else s) ∈ E
  · by_cases hf : (if endpoint = true then s else Int.fract (s + t)) ∈ F
    · simp only [Set.indicator_of_mem he, Set.indicator_of_mem hf, mul_one]
      exact coordinateWeight_bounds I hh hα i _ _
    · simp only [Set.indicator_of_notMem hf, mul_zero]
      exact ⟨le_rfl, by unfold height; positivity⟩
  · simp only [Set.indicator_of_notMem he, mul_zero, zero_mul]
    exact ⟨le_rfl, by unfold height; positivity⟩

theorem measurableSet_rectangle (D : Finset ℕ) (E F : ℕ → Set ℝ)
    (hE : ∀ i ∈ D, MeasurableSet (E i)) (hF : ∀ i ∈ D, MeasurableSet (F i)) :
    MeasurableSet (rectangle D E F) := by
  unfold rectangle
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro hi
  exact ((ProductCocycle.measurable_representative.comp
    ((measurable_pi_apply i).comp measurable_fst)) (hE i hi)).inter
    ((ProductCocycle.measurable_representative.comp
      ((measurable_pi_apply i).comp measurable_snd)) (hF i hi))

theorem representative_rotation_fract (θ : ℕ → ℝ) (n : ℕ) (x : Base) (i : ℕ) :
    circleRepresentative (rotationIterate θ (n : ℤ) x i) =
      Int.fract (circleRepresentative (x i) + Int.fract ((n : ℝ) * θ i)) := by
  change ProductCocycle.representative (x i + (((n : ℝ) * θ i : ℝ) : Circle)) = _
  rw [ProductCocycle.representative_add, TailTrimming.fract_add_eq_fract_add_fract]
  rfl

theorem first_testedCoordinateWeight_eq (I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) (x : Base) (i : ℕ) (E F : Set ℝ) :
    testedCoordinateWeight false I h α i E F (circleRepresentative (x i))
      (Int.fract ((n : ℝ) * θ i)) =
    if circleRepresentative (x i) ∈ E ∧
        circleRepresentative (rotationIterate θ (n : ℤ) x i) ∈ F then
      coordinateWeight I h α i (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i))
    else 0 := by
  rw [representative_rotation_fract]
  unfold testedCoordinateWeight
  dsimp only
  by_cases he : circleRepresentative (x i) ∈ E <;>
    by_cases hf : Int.fract (circleRepresentative (x i) + (n : ℝ) * θ i) ∈ F <;>
    simp [he, hf, Set.indicator_apply]

theorem first_tested_product_eq (D I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) (E F : ℕ → Set ℝ) (x : Base) :
    (∏ i ∈ D, testedCoordinateWeight false I h α i (E i) (F i)
      (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i))) =
    (rectangle D E F).indicator (fun xy => orbitWeight D I h α θ n xy.1)
      (TailTrimming.orbitPairMap θ n x) := by
  simp_rw [first_testedCoordinateWeight_eq]
  rw [Finset.prod_ite_zero]
  simp only [rectangle, Set.indicator_apply, Set.mem_ofPred_eq,
    TailTrimming.orbitPairMap, orbitWeight]

theorem orbitTestWeight_eq_first_product (D I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) (E F : ℕ → Set ℝ) (x : Base) :
    TailTrimming.orbitTestWeight θ (rectangle D E F) (orbitWeight D I h α θ) n x =
      ∏ i ∈ D, testedCoordinateWeight false I h α i (E i) (F i)
        (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i)) := by
  simpa only [TailTrimming.orbitTestWeight, Set.indicator_apply, Set.mem_preimage,
    TailTrimming.orbitPairMap] using (first_tested_product_eq D I h α θ n E F x).symm

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingCylinderError
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.SamplingCylinderWeak
open ProductModel

theorem weaklyConverges_of_real_cylinders
    {η : ℕ → Measure EndpointPair} {ν : Measure EndpointPair}
    (hη : ∀ n, IsFiniteMeasure (η n)) (hν : IsFiniteMeasure ν)
    (h : ∀ t : CylinderTest (Bool × ℕ),
      Tendsto (fun n => (η n).real (endpointCylinder t)) atTop
        (𝓝 (ν.real (endpointCylinder t)))) :
    WeaklyConverges η ν := by
  apply weaklyConverges_of_cylinders hη hν
  intro t
  exact (ENNReal.tendsto_toReal_iff
    (fun n => by let := hη n; exact measure_ne_top _ _)
    (by let := hν; exact measure_ne_top _ _)).mp (h t)

theorem abs_integral_sub_le_eLpNorm_two
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤
      (eLpNorm (fun x => f x - g x) 2 μ).toReal := by
  have hd : MemLp (fun x => f x - g x) 2 μ := hf.sub hg
  rw [← integral_sub (hf.integrable (by norm_num)) (hg.integrable (by norm_num)),
    ← Real.norm_eq_abs]
  calc
    ‖∫ x, f x - g x ∂μ‖ ≤ ∫ x, ‖f x - g x‖ ∂μ := norm_integral_le_integral_norm _
    _ = (eLpNorm (fun x => f x - g x) 1 μ).toReal := by
      rw [integral_norm_eq_lintegral_enorm hd.aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm]
    _ ≤ (eLpNorm (fun x => f x - g x) 2 μ).toReal :=
      ENNReal.toReal_mono hd.eLpNorm_ne_top
        (eLpNorm_le_eLpNorm_of_exponent_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | exact MemLp.aestronglyMeasurable (by assumption) | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num))

theorem tendsto_integral_of_eLpNorm_sub_tendsto_zero
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f g : ℕ → X → ℝ} {a : ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : ∀ n, MemLp (g n) 2 μ)
    (herror : Tendsto (fun n => eLpNorm (fun x => f n x - g n x) 2 μ) atTop (𝓝 0))
    (hideal : Tendsto (fun n => ∫ x, g n x ∂μ) atTop (𝓝 a)) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 a) := by
  have hnorm : Tendsto (fun n => (eLpNorm (fun x => f n x - g n x) 2 μ).toReal)
      atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp herror
  have hdiff : Tendsto (fun n => (∫ x, f n x ∂μ) - ∫ x, g n x ∂μ)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hnorm
    intro n
    simpa only [Real.norm_eq_abs] using abs_integral_sub_le_eLpNorm_two (hf n) (hg n)
  simpa only [sub_add_cancel, zero_add] using hdiff.add hideal

theorem real_mass_eq_integral_of_tested_first_marginal
    {η : Measure EndpointPair} {R : Set EndpointPair}
    {f : Base → ℝ} (hf : MemLp f 2 baseMeasure) (hf0 : 0 ≤ᵐ[baseMeasure] f)
    (hmarginal : (η.restrict R).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (f x))) :
    η.real R = ∫ x, f x ∂baseMeasure := by
  have hmass := congrArg (fun ν : Measure Base => ν univ) hmarginal
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hmass
  rw [Measure.real, hmass]
  exact (integral_eq_lintegral_of_nonneg_ae hf0 hf.aestronglyMeasurable).symm

theorem weaklyConverges_of_tested_first_marginal_L2
    {η : ℕ → Measure EndpointPair} {ν : Measure EndpointPair}
    (hη : ∀ n, IsFiniteMeasure (η n)) (hν : IsFiniteMeasure ν)
    (f g : CylinderTest (Bool × ℕ) → ℕ → Base → ℝ)
    (hf : ∀ t n, MemLp (f t n) 2 baseMeasure)
    (hg : ∀ t n, MemLp (g t n) 2 baseMeasure)
    (hf0 : ∀ t n, 0 ≤ᵐ[baseMeasure] f t n)
    (hmarginal : ∀ t n, ((η n).restrict (endpointCylinder t)).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (f t n x)))
    (herror : ∀ t, Tendsto
      (fun n => eLpNorm (fun x => f t n x - g t n x) 2 baseMeasure) atTop (𝓝 0))
    (hideal : ∀ t, Tendsto (fun n => ∫ x, g t n x ∂baseMeasure) atTop
      (𝓝 (ν.real (endpointCylinder t)))) :
    WeaklyConverges η ν := by
  apply weaklyConverges_of_real_cylinders hη hν
  intro t
  have heq (n : ℕ) := real_mass_eq_integral_of_tested_first_marginal
    (hf t n) (hf0 t n) (hmarginal t n)
  simpa only [heq] using tendsto_integral_of_eLpNorm_sub_tendsto_zero
    (hf t) (hg t) (herror t) (hideal t)

end Invariant233.SamplingCylinderWeak

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingOrbitWeak
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology

namespace Invariant233.ProductModel.TailTrimming
open SamplingCylinderWeak

theorem cylinderTestAverage_nonneg (θ : ℕ → ℝ) (N : Finset ℕ) (w : ℕ → Base → ℝ)
    (hw0 : ∀ n ∈ N, ∀ x, 0 ≤ w n x) (t : CylinderTest (Bool × ℕ)) (x : Base) :
    0 ≤ cylinderTestAverage θ N w t x :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun n hn => orbitTestWeight_nonneg θ _ w n (hw0 n hn) x)

theorem orbitAverage_finite_of_memLp_average (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ) (hw : ∀ n ∈ N, Measurable (w n))
    (hw0 : ∀ n ∈ N, ∀ x, 0 ≤ w n x)
    (havg : MemLp (fun x => (N.card : ℝ)⁻¹ * ∑ n ∈ N, w n x) 2 baseMeasure) :
    IsFiniteMeasure (orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (w n x))) := by
  let a : Base → ℝ := fun x => (N.card : ℝ)⁻¹ * ∑ n ∈ N, w n x
  have ha0 : 0 ≤ᵐ[baseMeasure] a := Filter.Eventually.of_forall fun x =>
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun n hn => hw0 n hn x)
  have ha : Integrable a baseMeasure := havg.integrable (by norm_num)
  have hfinite : IsFiniteMeasure (baseMeasure.withDensity (fun x => ENNReal.ofReal (a x))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal ha ha0]
    exact ENNReal.ofReal_lt_top
  have hmap : IsFiniteMeasure
      ((orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (w n x))).map Prod.fst) := by
    rw [orbitAverageMeasure_first_marginal_real θ N w hw hw0]
    exact hfinite
  let := hmap
  exact Measure.isFiniteMeasure_of_map measurable_fst.aemeasurable

theorem orbitAverage_weaklyConverges_of_tested_L2
    (θ : ℕ → ℝ) (N : ℕ → Finset ℕ) (w : ℕ → ℕ → Base → ℝ)
    (hw : ∀ l, ∀ n ∈ N l, Measurable (w l n))
    (hw0 : ∀ l, ∀ n ∈ N l, ∀ x, 0 ≤ w l n x)
    (g : CylinderTest (Bool × ℕ) → ℕ → Base → ℝ)
    (hf : ∀ t l, MemLp (cylinderTestAverage θ (N l) (w l) t) 2 baseMeasure)
    (hg : ∀ t l, MemLp (g t l) 2 baseMeasure)
    {ν : Measure EndpointPair} (hν : IsFiniteMeasure ν)
    (herror : ∀ t, Tendsto (fun l => eLpNorm
      (fun x => cylinderTestAverage θ (N l) (w l) t x - g t l x) 2 baseMeasure)
      atTop (𝓝 0))
    (hideal : ∀ t, Tendsto (fun l => ∫ x, g t l x ∂baseMeasure) atTop
      (𝓝 (ν.real (endpointCylinder t)))) :
    WeaklyConverges
      (fun l => orbitAverageMeasure θ (N l) (fun n x => ENNReal.ofReal (w l n x))) ν := by
  have hfinite (l : ℕ) : IsFiniteMeasure
      (orbitAverageMeasure θ (N l) (fun n x => ENNReal.ofReal (w l n x))) := by
    apply orbitAverage_finite_of_memLp_average θ (N l) (w l) (hw l) (hw0 l)
    have heq : cylinderTestAverage θ (N l) (w l) ∅ =
        (fun x => ((N l).card : ℝ)⁻¹ * ∑ n ∈ N l, w l n x) :=
      funext (cylinderTestAverage_empty θ (N l) (w l))
    rw [← heq]
    exact hf ∅ l
  refine weaklyConverges_of_tested_first_marginal_L2 hfinite hν
    (fun t l => cylinderTestAverage θ (N l) (w l) t) g hf hg ?_ ?_ herror hideal
  · intro t l
    exact Filter.Eventually.of_forall (cylinderTestAverage_nonneg θ (N l) (w l) (hw0 l) t)
  · intro t l
    exact orbitAverageMeasure_restrict_first_marginal_real θ (N l) (w l) (hw l) (hw0 l)
      (endpointCylinder t) (endpointCylinder_measurable t)

end Invariant233.ProductModel.TailTrimming

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingCylinderWeights
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators
open Filter

namespace Invariant233.ProductModel.SamplingWeights
open SamplingCylinderWeak

theorem measurableSet_cylinderCoordinateSet (t : CylinderTest (Bool × ℕ))
    (b : Bool) (i : ℕ) : MeasurableSet (cylinderCoordinateSet t b i) := by
  unfold cylinderCoordinateSet
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro v
  apply MeasurableSet.iInter
  intro _hv
  apply MeasurableSet.iInter
  intro _hvi
  exact measurableSet_Ioo

theorem endpointCylinder_eq_rectangle (t : CylinderTest (Bool × ℕ))
    (D : Finset ℕ) (hD : cylinderSupport t ⊆ D) :
    endpointCylinder t = rectangle D
      (cylinderCoordinateSet t false) (cylinderCoordinateSet t true) := by
  ext xy
  change (∀ v ∈ t, (v.2.1 : ℝ) < cutCoordinates xy v.1 ∧
    cutCoordinates xy v.1 < (v.2.2 : ℝ)) ↔
    (∀ i ∈ D, circleRepresentative (xy.1 i) ∈ cylinderCoordinateSet t false i ∧
      circleRepresentative (xy.2 i) ∈ cylinderCoordinateSet t true i)
  constructor
  · intro hx i _hi
    constructor
    · intro v hv hvi
      simpa only [hvi, cutCoordinates, Bool.false_eq_true, ite_false, if_false] using hx v hv
    · intro v hv hvi
      simpa only [hvi, cutCoordinates, ite_true, if_true] using hx v hv
  · intro hx v hv
    have hi : v.1.2 ∈ D := hD (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    rcases v with ⟨⟨b, i⟩, a, c⟩
    cases b
    · exact (hx i hi).1 _ hv rfl
    · exact (hx i hi).2 _ hv rfl

theorem cylinder_orbitTestWeight_eq_first_product
    (D I : Finset ℕ) (h α : ℝ) (θ : ℕ → ℝ) (n : ℕ)
    (t : CylinderTest (Bool × ℕ)) (hD : cylinderSupport t ⊆ D) (x : Base) :
    TailTrimming.orbitTestWeight θ (endpointCylinder t) (orbitWeight D I h α θ) n x =
      ∏ i ∈ D, testedCoordinateWeight false I h α i
        (cylinderCoordinateSet t false i) (cylinderCoordinateSet t true i)
        (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i)) := by
  rw [endpointCylinder_eq_rectangle t D hD]
  exact orbitTestWeight_eq_first_product D I h α θ n _ _ x

theorem cylinderTestAverage_eq_product_average
    (D I N : Finset ℕ) (h α : ℝ) (θ : ℕ → ℝ)
    (t : CylinderTest (Bool × ℕ)) (hD : cylinderSupport t ⊆ D) (x : Base) :
    TailTrimming.cylinderTestAverage θ N (orbitWeight D I h α θ) t x =
      (N.card : ℝ)⁻¹ * ∑ n ∈ N, ∏ i ∈ D, testedCoordinateWeight false I h α i
        (cylinderCoordinateSet t false i) (cylinderCoordinateSet t true i)
        (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i)) := by
  unfold TailTrimming.cylinderTestAverage
  simp_rw [cylinder_orbitTestWeight_eq_first_product D I h α θ _ t hD]

theorem eventually_cylinderSupport_subset_sourcePrefix
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (t : CylinderTest (Bool × ℕ)) :
    ∀ᶠ l in atTop, cylinderSupport t ⊆ Finset.range (p.prefixCount (l + 1)) := by
  have hcount (l : ℕ) : l ≤ p.prefixCount l := by
    calc
      l = ∑ _i ∈ Finset.range l, 1 := by simp
      _ ≤ ∑ i ∈ Finset.range l, p.m i :=
        Finset.sum_le_sum (fun i _ => hp.m_pos i)
  change ∀ᶠ l in atTop, ∀ i ∈ cylinderSupport t,
    i ∈ Finset.range (p.prefixCount (l + 1))
  rw [Finset.eventually_all]
  intro i _hi
  filter_upwards [eventually_ge_atTop i] with l hl
  exact Finset.mem_range.mpr (lt_of_le_of_lt hl
    (lt_of_lt_of_le (Nat.lt_succ_self l) (hcount (l + 1))))

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingTestIntegrability
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingCylinderWeak.map_quotient_cut _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.SamplingWeights

theorem stronglyMeasurable_testedAverage (endpoint : Bool) (I : Finset ℕ) (h α : ℝ)
    (i : ℕ) {E F : Set ℝ} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    StronglyMeasurable (fun s => ∫ t in (0 : ℝ)..1,
      testedCoordinateWeight endpoint I h α i E F s t) := by
  have hm := (measurable_testedCoordinateWeight endpoint I h α i hE hF).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) 1))
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hm

theorem norm_testedAverage_le (endpoint : Bool) (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) (E F : Set ℝ) (s : ℝ) :
    ‖∫ t in (0 : ℝ)..1, testedCoordinateWeight endpoint I h α i E F s t‖ ≤
      height h α := by
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖testedCoordinateWeight endpoint I h α i E F s t‖ ≤ height h α := by
    intro t _
    rw [Real.norm_eq_abs, abs_of_nonneg (testedCoordinateWeight_bounds endpoint I hh hα i E F s t).1]
    exact (testedCoordinateWeight_bounds endpoint I hh hα i E F s t).2
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb

theorem memLp_testedIdeal (endpoint : Bool) (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (E F : ℕ → Set ℝ)
    (hE : ∀ i ∈ D, MeasurableSet (E i)) (hF : ∀ i ∈ D, MeasurableSet (F i))
    (p : ℝ≥0∞) : MemLp (testedIdeal endpoint D I h α E F) p baseMeasure := by
  have hm : Measurable (testedIdeal endpoint D I h α E F) := by
    unfold testedIdeal
    apply Finset.measurable_prod
    intro i hi
    exact (stronglyMeasurable_testedAverage endpoint I h α i (hE i hi) (hF i hi)).measurable.comp
      (ProductCocycle.measurable_representative.comp (measurable_pi_apply i))
  apply MemLp.of_bound hm.aestronglyMeasurable (height h α ^ D.card)
  filter_upwards [] with x
  unfold testedIdeal
  rw [Real.norm_eq_abs, Finset.abs_prod]
  calc
    _ ≤ ∏ _i ∈ D, height h α := Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      (fun i _ => by simpa only [Real.norm_eq_abs] using
        norm_testedAverage_le endpoint I hh hα i (E i) (F i) (circleRepresentative (x i)))
    _ = _ := by simp

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductIdealSamplingRectangles
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.ScalarSampling.TestedTriangular.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedTriangular.secondKernel_univ_univ _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Invariant233.ProductModel.SamplingWeights

theorem rectangle_indicator_eq_product (D : Finset ℕ) (E F : ℕ → Set ℝ)
    (xy : EndpointPair) :
    (rectangle D E F).indicator (fun _ => (1 : ℝ)) xy =
      ∏ i : D, (E i).indicator (fun _ => (1 : ℝ)) (circleRepresentative (xy.1 i)) *
        (F i).indicator (fun _ => (1 : ℝ)) (circleRepresentative (xy.2 i)) := by
  classical
  have he (i : D) :
      (E i).indicator (fun _ => (1 : ℝ)) (circleRepresentative (xy.1 i)) *
      (F i).indicator (fun _ => (1 : ℝ)) (circleRepresentative (xy.2 i)) =
      if circleRepresentative (xy.1 i) ∈ E i ∧ circleRepresentative (xy.2 i) ∈ F i
        then 1 else 0 := by
    by_cases hE : circleRepresentative (xy.1 i) ∈ E i <;>
      by_cases hF : circleRepresentative (xy.2 i) ∈ F i <;> simp [hE, hF]
  simp_rw [he]
  rw [Finset.prod_ite_zero]
  simp [rectangle, Set.indicator_apply]

theorem integral_base_coordinate_product (D : Finset ℕ) (g : D → Circle → ℝ)
    (hg : ∀ i, Measurable (g i)) :
    (∫ x : Base, ∏ i : D, g i (x i) ∂baseMeasure) =
      ∏ i : D, ∫ x, g i x ∂circleMeasure := by
  have hr : MeasurePreserving D.restrict baseMeasure
      (Measure.pi (fun _ : D => circleMeasure)) :=
    ⟨by fun_prop, Measure.infinitePi_map_restrict _⟩
  have hm : Measurable (fun x : D → Circle => ∏ i : D, g i (x i)) := by
    apply Finset.measurable_prod
    intro i _
    exact (hg i).comp (measurable_pi_apply i)
  have he := integral_map (μ := baseMeasure) hr.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hr.map_eq] at he
  calc
    _ = ∫ x : D → Circle, ∏ i : D, g i (x i) ∂Measure.pi (fun _ : D => circleMeasure) := by
      simpa only [Finset.restrict] using he.symm
    _ = _ := integral_fintype_prod_eq_prod g

theorem idealLaw_real_rectangle_eq_integral {I D : Finset ℕ} (hID : I ⊆ D)
    {h α : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hα : 0 < α)
    (E F : ℕ → Set ℝ) (hE : ∀ i ∈ D, MeasurableSet (E i))
    (hF : ∀ i ∈ D, MeasurableSet (F i)) :
    (IdealSampling.law I D h α).real (rectangle D E F) =
      ∫ x : Base, testedIdeal false D I h α E F x ∂baseMeasure := by
  unfold testedIdeal
  let G : D → Circle × Circle → ℝ := fun i p =>
    (E i).indicator (fun _ => (1 : ℝ)) (circleRepresentative p.1) *
      (F i).indicator (fun _ => (1 : ℝ)) (circleRepresentative p.2)
  have hG (i : D) : Measurable (G i) :=
    (((measurable_const.indicator (hE i i.property)).comp
      (Sampling.representative_measurable.comp measurable_fst)).mul
      ((measurable_const.indicator (hF i i.property)).comp
        (Sampling.representative_measurable.comp measurable_snd)))
  have hGb (i : D) (p : Circle × Circle) : ‖G i p‖ ≤ (1 : ℝ) := by
    dsimp [G]
    by_cases he : circleRepresentative p.1 ∈ E i <;>
      by_cases hf : circleRepresentative p.2 ∈ F i <;> simp [he, hf]
  have hk := IdealSampling.integral_law_product_eq_kernels hID hh0 hh1 hα G hG
    (fun _ => 1) (fun _ => zero_le_one) hGb
  rw [← integral_indicator_one (measurableSet_rectangle D E F hE hF)]
  change (∫ xy, (rectangle D E F).indicator (fun _ => (1 : ℝ)) xy
    ∂IdealSampling.law I D h α) = _
  simp_rw [rectangle_indicator_eq_product]
  change (∫ xy, ∏ i : D, G i (xy.1 i, xy.2 i) ∂IdealSampling.law I D h α) = _
  rw [hk]
  have hb := integral_base_coordinate_product D
    (fun i x => ∫ t in (0 : ℝ)..1, testedCoordinateWeight false I h α i (E i) (F i)
      (circleRepresentative x) t)
    (fun i => (stronglyMeasurable_testedAverage false I h α i (hE i i.property)
      (hF i i.property)).measurable.comp Sampling.representative_measurable)
  have hp (x : Base) : (∏ i : D, ∫ t in (0 : ℝ)..1,
      testedCoordinateWeight false I h α i (E i) (F i) (circleRepresentative (x i)) t) =
      ∏ i ∈ D, ∫ t in (0 : ℝ)..1,
      testedCoordinateWeight false I h α i (E i) (F i) (circleRepresentative (x i)) t := by
    rw [Finset.prod_coe_sort_eq_attach]
    exact Finset.prod_attach D (fun i => ∫ t in (0 : ℝ)..1,
      testedCoordinateWeight false I h α i (E i) (F i) (circleRepresentative (x i)) t)
  simp_rw [← hp]
  rw [hb]
  apply Finset.prod_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [] with x
  apply intervalIntegral.integral_congr
  intro t _
  simp only [G, IdealSampling.coordinateKernel, testedCoordinateWeight, coordinateWeight,
    Bool.false_eq_true, ite_false, if_false]
  rw [show circleRepresentative (x + (t : Circle)) =
      Int.fract (circleRepresentative x + t) from ProductCocycle.representative_add x t]
  ring

theorem idealLaw_real_cylinder_eq_integral {I D : Finset ℕ} (hID : I ⊆ D)
    {h α : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hα : 0 < α)
    (t : SamplingCylinderWeak.CylinderTest (Bool × ℕ)) (hD : cylinderSupport t ⊆ D) :
    (IdealSampling.law I D h α).real (SamplingCylinderWeak.endpointCylinder t) =
      ∫ x : Base, testedIdeal false D I h α
        (cylinderCoordinateSet t false) (cylinderCoordinateSet t true) x ∂baseMeasure := by
  rw [endpointCylinder_eq_rectangle t D hD]
  exact idealLaw_real_rectangle_eq_integral hID hh0 hh1 hα _ _
    (fun i _ => measurableSet_cylinderCoordinateSet t false i)
    (fun i _ => measurableSet_cylinderCoordinateSet t true i)

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingSourceWeak
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

namespace Invariant233.ProductModel.SamplingWeights
open SamplingCylinderWeak

theorem eventually_finset_subset_sourcePrefix {p : ProductScaleData}
    (hp : ProductScaleLaws p) (I : Finset ℕ) :
    ∀ᶠ l in atTop, I ⊆ Finset.range (p.prefixCount (l + 1)) := by
  have hcount (l : ℕ) : l ≤ p.prefixCount l := by
    calc
      l = ∑ _i ∈ Finset.range l, 1 := by simp
      _ ≤ ∑ i ∈ Finset.range l, p.m i :=
        Finset.sum_le_sum (fun i _ => hp.m_pos i)
  change ∀ᶠ l in atTop, ∀ i ∈ I, i ∈ Finset.range (p.prefixCount (l + 1))
  rw [Finset.eventually_all]
  intro i _hi
  filter_upwards [eventually_ge_atTop i] with l hl
  exact Finset.mem_range.mpr (lt_of_le_of_lt hl
    (lt_of_lt_of_le (Nat.lt_succ_self l) (hcount (l + 1))))

theorem memLp_cylinderTestAverage (D I N : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (θ : ℕ → ℝ)
    (t : CylinderTest (Bool × ℕ)) :
    MemLp (TailTrimming.cylinderTestAverage θ N (orbitWeight D I h α θ) t)
      2 baseMeasure := by
  unfold TailTrimming.cylinderTestAverage
  apply MemLp.const_mul
  apply memLp_finsetSum N
  intro n _hn
  exact (memLp_orbitWeight D I hh hα θ n 2).indicator
    ((TailTrimming.measurable_orbitPairMap θ n) (endpointCylinder_measurable t))

theorem source_orbitAverage_weaklyConverges_of_cylinder_energy
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) (θ : ℕ → ℝ) (I : Finset ℕ)
    (herror : ∀ t : CylinderTest (Bool × ℕ), Tendsto
      (fun l => ∫ x, (sourceTestedError p N false I
        (cylinderCoordinateSet t false) (cylinderCoordinateSet t true) l θ x) ^ 2
        ∂baseMeasure) atTop (𝓝 0)) :
    WeaklyConverges
      (fun l => TailTrimming.orbitAverageMeasure θ (N l)
        (fun n x => ENNReal.ofReal (orbitWeight
          (Finset.range (p.prefixCount (l + 1))) I
          ((p.m l : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m l : ℝ) ^ 2) θ n x)))
      (triangularLaw I) := by
  let D : ℕ → Finset ℕ := fun l => Finset.range (p.prefixCount (l + 1))
  let h : ℕ → ℝ := fun l => (p.m l : ℝ) ^ (-(3 / 5 : ℝ))
  let α : ℕ → ℝ := fun l => 1 / (p.m l : ℝ) ^ 2
  let w : ℕ → ℕ → Base → ℝ := fun l => orbitWeight (D l) I (h l) (α l) θ
  let g : CylinderTest (Bool × ℕ) → ℕ → Base → ℝ := fun t l =>
    testedIdeal false (D l) I (h l) (α l)
      (cylinderCoordinateSet t false) (cylinderCoordinateSet t true)
  have hm (l : ℕ) : 0 < (p.m l : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 100) (hp.m_ge_100 l))
  have hh (l : ℕ) : 0 < h l := Real.rpow_pos_of_pos (hm l) _
  have hα (l : ℕ) : 0 < α l := one_div_pos.mpr (sq_pos_of_pos (hm l))
  have hh1 (l : ℕ) : h l ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 100) (hp.m_ge_100 l))
    · norm_num
  have hf (t : CylinderTest (Bool × ℕ)) (l : ℕ) :
      MemLp (TailTrimming.cylinderTestAverage θ (N l) (w l) t) 2 baseMeasure :=
    memLp_cylinderTestAverage (D l) I (N l) (hh l) (hα l) θ t
  have hg (t : CylinderTest (Bool × ℕ)) (l : ℕ) : MemLp (g t l) 2 baseMeasure :=
    memLp_testedIdeal false (D l) I (hh l) (hα l) _ _
      (fun i _ => measurableSet_cylinderCoordinateSet t false i)
      (fun i _ => measurableSet_cylinderCoordinateSet t true i) 2
  apply TailTrimming.orbitAverage_weaklyConverges_of_tested_L2 θ N w
    (fun l n _ => measurable_orbitWeight (D l) I (h l) (α l) θ n)
    (fun l n _ x => (orbitWeight_bounds (D l) I (hh l) (hα l) θ n x).1)
    g hf hg (Sampling.triangularLaw_finite I)
  · intro t
    have he : Tendsto (fun l => ∫ x,
        (TailTrimming.cylinderTestAverage θ (N l) (w l) t x - g t l x) ^ 2
          ∂baseMeasure) atTop (𝓝 0) := by
      apply (herror t).congr'
      filter_upwards [eventually_cylinderSupport_subset_sourcePrefix hp t] with l hD
      congr 1
      funext x
      rw [cylinderTestAverage_eq_product_average (D l) I (N l) (h l) (α l) θ t hD]
      rfl
    have hn := SquaredIntegralLp.tendsto_eLpNorm_two_of_integral_sq
      baseMeasure baseMeasure
      (fun l x => TailTrimming.cylinderTestAverage θ (N l) (w l) t x - g t l x)
      (fun _ : Base => (0 : ℝ))
      (fun index => ((hf t index).sub (hg t index)).aestronglyMeasurable)
      aestronglyMeasurable_const
      (fun l => ((hf t l).sub (hg t l)).integrable_sq)
      (by simp) (by simpa using he)
    simpa using hn
  · intro t
    apply (IdealSampling.law_cylinder_real_tendsto_of_productScaleLaws I hp t).congr'
    filter_upwards [eventually_finset_subset_sourcePrefix hp I,
      eventually_cylinderSupport_subset_sourcePrefix hp t] with l hI hD
    exact idealLaw_real_cylinder_eq_integral hI (hh l) (hh1 l) (hα l) t hD

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductScaleSampling
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
namespace Invariant233.ProductScaleLaws

variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem eventually_exists_sampling_powers :
    ∀ᶠ j : ℕ in atTop, ∃ s : Finset ℕ, ProductSamplingPowersAt p j s := by
  have h := hp.m_strictMono.tendsto_atTop.eventually
    SeparatedPowers.eventually_exists_nat_sampling_powers
  filter_upwards [h] with j hj
  have hN : p.m j * p.K j ≤ p.m j ^ 2 := by
    calc
      _ ≤ p.m j * p.m j := Nat.mul_le_mul_left _ (hp.m_ge_K j)
      _ = _ := by ring
  obtain ⟨s, hrange, hcard, hpos, hsep⟩ := hj (p.m j * p.K j) hN
  exact ⟨s, hrange, hcard, hpos, hsep⟩

theorem exists_sampling_sequence :
    ∃ s : ℕ → Finset ℕ, ∀ᶠ j : ℕ in atTop, ProductSamplingPowersAt p j (s j) := by
  classical
  let s (j : ℕ) : Finset ℕ := if h : ∃ t, ProductSamplingPowersAt p j t then
    Classical.choose h else ∅
  refine ⟨s, ?_⟩
  filter_upwards [hp.eventually_exists_sampling_powers] with j hj
  dsimp [s]
  rw [dite_eq_left hj]
  exact Classical.choose_spec hj

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingTailReindex
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductModel

theorem HasUniformL2Marginals.comp {η : ℕ → Measure EndpointPair}
    (h : HasUniformL2Marginals η) (r : ℕ → ℕ) :
    HasUniformL2Marginals (fun l => η (r l)) := by
  obtain ⟨H, hH, h⟩ := h
  exact ⟨H, hH, fun l => h (r l)⟩

theorem WeaklyConverges.comp_tendsto {η : ℕ → Measure EndpointPair}
    {ν : Measure EndpointPair} (h : WeaklyConverges η ν)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) :
    WeaklyConverges (fun l => η (r l)) ν := by
  intro φ
  exact (h φ).comp hr

namespace TailTrimming

theorem orderedOrbitSampling_of_eventually_prefix_samples
    (θ : ℕ → ℝ) (I : Finset ℕ) (hθ : ∀ i, 0 ≤ θ i)
    (D N : ℕ → Finset ℕ) (M : ℕ → ℕ)
    (w : ∀ l, ℕ → (D l → Circle) → ℝ≥0∞)
    (hw : ∀ᶠ l in atTop, ∀ n ∈ N l, Measurable (w l n))
    (hN : ∀ᶠ l in atTop, ∀ n ∈ N l, 0 < n)
    (hM : ∀ᶠ l in atTop, ∀ n ∈ N l, n ≤ M l)
    (hprefix : ∀ᶠ l in atTop, ∀ n ∈ N l,
      ∀ᵐ x ∂baseMeasure.withDensity (fun x : Base => w l n (fun i : D l => x i)),
        ∀ i ∈ D l, circleRepresentative (x i) ≤
          circleRepresentative (rotationIterate θ (n : ℤ) x i))
    (hL2 : HasUniformL2Marginals
      (fun l => orbitAverageMeasure θ (N l) (fun n x => w l n (fun i : D l => x i))))
    (hweak : WeaklyConverges
      (fun l => orbitAverageMeasure θ (N l) (fun n x => w l n (fun i : D l => x i)))
      (triangularLaw I))
    (htail : Tendsto (fun l => ENNReal.ofReal (M l : ℝ) *
      ∑' i : {i : ℕ // i ∉ D l}, ENNReal.ofReal (θ i)) atTop (𝓝 0)) :
    OrderedOrbitSampling θ I := by
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hw.and (hN.and (hM.and hprefix)))
  have hshift : Tendsto (fun l : ℕ => l + J) atTop atTop :=
    tendsto_atTop_mono (fun l => Nat.le_add_right l J) tendsto_id
  have hstage (l : ℕ) := hJ (l + J) (Nat.le_add_left J l)
  exact orderedOrbitSampling_of_prefix_samples θ I hθ
    (fun l => D (l + J)) (fun l => N (l + J)) (fun l => M (l + J))
    (fun l => w (l + J)) (fun l => (hstage l).1)
    (fun l => (hstage l).2.1) (fun l => (hstage l).2.2.1)
    (fun l => (hstage l).2.2.2) (hL2.comp (fun l => l + J))
    (hweak.comp_tendsto hshift) (htail.comp hshift)

end TailTrimming
end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSourceSamplingAssembly
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingCylinderWeak.map_quotient_cut _root_.OAI.Invariant233.SamplingCylinderWeak.quotient_cutCoordinates _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Invariant233.ProductModel.SamplingWeights

theorem orderedOrbitSampling_of_source_limits
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ)
    (hN : ∀ᶠ j in atTop, ProductSamplingPowersAt p j (N j))
    (θ : ℕ → ℝ) (I : Finset ℕ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (hθblock : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ≤ 2 / ((p.m j : ℝ) * p.K j))
    (hL2 : HasUniformL2Marginals (fun j =>
      TailTrimming.orbitAverageMeasure θ (N j) (fun n x => ENNReal.ofReal
        (orbitWeight (Finset.range (p.prefixCount (j + 1))) I
          ((p.m j : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m j : ℝ) ^ 2) θ n x))))
    (hweak : WeaklyConverges (fun j =>
      TailTrimming.orbitAverageMeasure θ (N j) (fun n x => ENNReal.ofReal
        (orbitWeight (Finset.range (p.prefixCount (j + 1))) I
          ((p.m j : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m j : ℝ) ^ 2) θ n x)))
      (triangularLaw I)) :
    OrderedOrbitSampling θ I := by
  let D (j : ℕ) := Finset.range (p.prefixCount (j + 1))
  let h (j : ℕ) := (p.m j : ℝ) ^ (-(3 / 5 : ℝ))
  let α (j : ℕ) := 1 / (p.m j : ℝ) ^ 2
  let M (j : ℕ) := ⌊(p.m j : ℝ) ^ ((7 / 10 : ℝ) * p.m j)⌋₊
  have hh1 (j : ℕ) : h j ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast (show 1 ≤ p.m j by have := hp.m_ge_100 j; omega)
    · norm_num
  apply TailTrimming.orderedOrbitSampling_of_eventually_prefix_samples θ I hθ0 D N M
    (fun j n x => ENNReal.ofReal (prefixWeight (D j) I (h j) (α j) θ n x))
  · exact Filter.Eventually.of_forall (fun j n _ =>
      (measurable_prefixWeight (D j) I (h j) (α j) θ n).ennreal_ofReal)
  · filter_upwards [hN] with j hj
    exact hj.positive
  · filter_upwards [hN] with j hj
    exact fun n hn => Nat.le_floor (hj.range n hn).2
  · apply Filter.Eventually.of_forall
    intro j n hn
    simpa only [prefixWeight_restrict] using orbitWeight_ae_prefix_order (D j) I (hh1 j) θ n
  · simpa only [prefixWeight_restrict, D, h, α] using hL2
  · simpa only [prefixWeight_restrict, D, h, α] using hweak
  · apply TailTrimming.source_horizon_angle_tail_tendsto_zero hp θ hθ0 hθsum hθblock M
    intro j
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSourceSamplingFinal
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.ProductModel.SamplingWeights

theorem ae_hasAllFiniteCoordinateSampling
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hblock : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      S i = (p.m j : ℝ) * p.K j) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Icc (1 / S i) (2 / S i))),
      HasAllFiniteCoordinateSampling θ := by
  obtain ⟨N, hN⟩ := hp.exists_sampling_sequence
  filter_upwards [hp.ae_source_angles S hS hblock,
    ae_all_sourceCylinder_energy_tendsto_zero hp N hN S hS hblock,
    ae_all_source_univ_energy_tendsto_zero hp N hN S hS hblock] with θ hθ hC hU
  intro I
  apply orderedOrbitSampling_of_source_limits hp N hN θ I
    (fun i => (hθ.2.1 i).1.le) hθ.2.2.1
    (fun j i hi => (hθ.1 j i hi).2)
  · exact source_hasUniformL2Marginals_of_energy_convergence hp N θ I (hU I)
  · exact source_orbitAverage_weaklyConverges_of_cylinder_energy hp N θ I (hC I)

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Irrational rotation counterexamples, product realizations, and transitive commutants. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace Invariant233

theorem product_finite_coordinate_sampling
    (p : ProductScaleData) (hp : ProductScaleLaws p)
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hblock : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      S i = (p.m j : ℝ) * p.K j) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i =>
      ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))),
      ProductModel.HasAllFiniteCoordinateSampling θ := by
  exact ProductModel.SamplingWeights.ae_hasAllFiniteCoordinateSampling hp S hS hblock

end Invariant233
end

namespace Invariant233

namespace Results

theorem product_realization_oai :
    ∃ θ c : ℕ → ℝ, ProductModel.IsCounterexampleRealization θ c := by
  exact ProductModel.product_realization_of_ae_sampling Invariant233.product_finite_coordinate_sampling

end Results
end Invariant233

end OAI
end

theorem solution : type_of% @OAI.Invariant233.Results.product_realization_oai := @OAI.Invariant233.Results.product_realization_oai
