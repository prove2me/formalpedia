-- Prove2me | solution 1 for OAI.KadisonKastler.exists_partition_projection_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T14:28:14.323206+00:00
-- url     : https://prove2.me/submissions/57c43998-287b-44ef-86f8-de7ee48c01b5

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Nat
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K072
import Definitions.Def_Q260K041
import Definitions.Def_Q260K044

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteSignFourthMoment
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourth moments of finite independent signs

The finite probability space is the set of all Boolean sign assignments.
The four-sign identity and tracial Cauchy–Schwarz give the estimate used
in the bounded-vector test in manuscript §5.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private theorem finiteSign_flip_same (ε : ι → Bool) (i : ι) :
    finiteSign (flipSign i ε) i = -finiteSign ε i := by
  cases h : ε i <;> simp [finiteSign, flipSign, h]

omit [Fintype ι] in
private theorem finiteSign_flip_ne (ε : ι → Bool) {i j : ι} (h : j ≠ i) :
    finiteSign (flipSign i ε) j = finiteSign ε j := by
  simp [finiteSign, flipSign, Function.update_of_ne h]

/-- Coordinate sign orthogonality. -/
theorem finiteSign_pair (i j : ι) :
    (𝔼 ε : ι → Bool, finiteSign ε i * finiteSign ε j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp only [ite_true, if_true, ← pow_two, finiteSign_sq, Fintype.expect_const]
  · rw [ite_eq_right h]
    have he := Fintype.expect_equiv (flipSign i)
      (fun ε => finiteSign ε i * finiteSign ε j)
      (fun ε => -(finiteSign ε i * finiteSign ε j)) (by
        intro ε
        rw [finiteSign_flip_same, finiteSign_flip_ne ε (Ne.symm h)]
        ring)
    rw [Finset.expect_neg_distrib] at he
    linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveUnitaryTransport
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # Transporting positive matrix-central vectors by inner automorphisms

The modular quadratic unitary transports the concrete matrix algebra,
its positive central vector and the associated vector state together.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

theorem modularUnitary_coe (u : unitary (Algebra M)) :
    (modularUnitary J hJ u : H →L[ℂ] H) = modularQuadratic J u.val := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitaryStateDefect
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # State commutators control unitary central-vector defects

Powers–Størmer, followed by a unitary change of coordinates, gives the
reverse estimate needed to compare the state and vector centralizer tests.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem centralVectorDefect_unitary_norm_eq
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ : H) (u : unitary (Algebra M)) :
    ‖centralVectorDefect J ξ u.val.val‖ =
      ‖(modularUnitary J hJ (star u) : H →L[ℂ] H) ξ-ξ‖ := by
  have hmul : u.val.val*star u.val.val=1 :=
    congrArg (fun a : Algebra M => a.val) u.property.2
  have he : (ambientAlgebraUnitary u : H →L[ℂ] H)
      ((modularUnitary J hJ (star u) : H →L[ℂ] H) ξ-ξ) =
      -(centralVectorDefect J ξ u.val.val) := by
    change u.val.val ((star u.val.val*conjugationOperator J (star u.val.val)) ξ-ξ)=_
    rw [map_sub]
    have hfirst : u.val.val ((star u.val.val*conjugationOperator J (star u.val.val)) ξ) =
        conjugationOperator J (star u.val.val) ξ := by
      change (u.val.val*(star u.val.val*conjugationOperator J (star u.val.val))) ξ=_
      rw [← mul_assoc,hmul,one_mul]
    rw [hfirst,centralVectorDefect_apply]
    abel
  have hn := Unitary.norm_map (ambientAlgebraUnitary u)
    ((modularUnitary J hJ (star u) : H →L[ℂ] H) ξ-ξ)
  rw [he,norm_neg] at hn
  exact hn

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PartitionSignAverage
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.faithfulTensorHom_intertwines _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # The sign average of a finite projection partition -/

namespace KadisonKastler

open Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem partitionSignOperator_val (P : ι → AlgebraProjection M) (ε : ι → Bool) :
    (partitionSignOperator P ε).val=∑ i, finiteSign ε i • (P i).val.val := by
  change M.toStarSubalgebra.subtype (∑ i, finiteSign ε i • (P i).val)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ((finiteSign ε i : ℂ) • (P i).val).val=(finiteSign ε i : ℂ) • (P i).val.val
  rfl

omit [DecidableEq ι] in
theorem partitionSignOperator_star (P : ι → AlgebraProjection M) (ε : ι → Bool) :
    star (partitionSignOperator P ε)=partitionSignOperator P ε := by
  simp only [partitionSignOperator,star_sum,star_smul,star_trivial]
  exact Finset.sum_congr rfl fun i _ => congrArg (fun a : Algebra M => finiteSign ε i • a)
    (P i).property.isSelfAdjoint.star_eq

omit [DecidableEq ι] in
theorem partitionSignOperator_sq (P : ι → AlgebraProjection M)
    (hP : Pairwise (fun i j => (P i).val*(P j).val=0))
    (hs : (∑ i, (P i).val)=1) (ε : ι → Bool) :
    partitionSignOperator P ε*partitionSignOperator P ε=1 := by
  classical
  rw [partitionSignOperator,Finset.sum_mul]
  simp only [Finset.mul_sum,smul_mul_assoc,mul_smul_comm,smul_smul]
  have hd (i : ι) : ∑ j, (finiteSign ε j*finiteSign ε i) • ((P i).val*(P j).val)=(P i).val := by
    rw [Finset.sum_eq_single i]
    · rw [← pow_two,finiteSign_sq,one_smul,(P i).property.isIdempotentElem.eq]
    · intro j _ hji
      rw [hP (Ne.symm hji),smul_zero]
    · simp
  simpa only [hd] using hs

omit [DecidableEq ι] in
theorem partitionSignOperator_unitary (P : ι → AlgebraProjection M)
    (hP : Pairwise (fun i j => (P i).val*(P j).val=0))
    (hs : (∑ i, (P i).val)=1) (ε : ι → Bool) :
    partitionSignOperator P ε ∈ unitary (Algebra M) := by
  constructor <;> rw [partitionSignOperator_star,partitionSignOperator_sq P hP hs]

omit [CompleteSpace H] in
theorem conjugationOperator_real_smul (J : H ≃ₗᵢ⋆[ℂ] H) (t : ℝ) (a : H →L[ℂ] H) :
    conjugationOperator J (t • a)=t • conjugationOperator J a := by
  rw [← Complex.coe_smul,conjugationOperator_smul,Complex.star_def,Complex.conj_ofReal,
    Complex.coe_smul]

omit [CompleteSpace H] [DecidableEq ι] in
theorem conjugationOperator_finite_sum (J : H ≃ₗᵢ⋆[ℂ] H) (a : ι → H →L[ℂ] H) :
    conjugationOperator J (∑ i, a i)=∑ i, conjugationOperator J (a i) := by
  ext x
  simp only [conjugationOperator_apply,sum_apply,map_sum]

omit [DecidableEq ι] in
theorem partitionSignOperator_quadratic (J : H ≃ₗᵢ⋆[ℂ] H)
    (P : ι → AlgebraProjection M) (ε : ι → Bool) :
    modularQuadratic J (partitionSignOperator P ε)=
      ∑ i, ∑ j, (finiteSign ε i*finiteSign ε j) •
        ((P i).val.val*conjugationOperator J (P j).val.val) := by
  classical
  rw [modularQuadratic,partitionSignOperator_val,conjugationOperator_finite_sum]
  simp_rw [conjugationOperator_real_smul]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum,smul_mul_assoc,mul_smul_comm,smul_smul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [mul_comm (finiteSign ε j) (finiteSign ε i)]

attribute [local instance] OAI.KadisonKastler.partitionOperatorNNRat
theorem expect_partitionSignOperator_quadratic (J : H ≃ₗᵢ⋆[ℂ] H)
    (P : ι → AlgebraProjection M) :
    (𝔼 ε : ι → Bool, modularQuadratic J (partitionSignOperator P ε))=
      ∑ i, modularQuadratic J (P i).val := by
  simp only [partitionSignOperator_quadratic,Finset.expect_sum_comm]
  have hm (i j : ι) :
      (𝔼 ε : ι → Bool, (finiteSign ε i*finiteSign ε j) •
        ((P i).val.val*conjugationOperator J (P j).val.val))=
        (if i=j then 1 else 0 : ℝ) • ((P i).val.val*conjugationOperator J (P j).val.val) := by
    let L : ℝ →ₗ[ℚ≥0] (H →L[ℂ] H) :=
      (LinearMap.toSpanSingleton ℝ (H →L[ℂ] H)
        ((P i).val.val*conjugationOperator J (P j).val.val)).restrictScalars ℚ≥0
    have he := congrArg L (finiteSign_pair i j)
    rw [map_expect] at he
    exact he
  simp only [hm,ite_smul,one_smul,zero_smul]
  simp [modularQuadratic]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PartitionProjectionGap
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.faithfulTensorHom_intertwines _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # One projection retains a finite pinching gap

This is the finite sign-averaging argument in Haagerup, Acta Math. 158
(1987), Lemma 2.16. The reference error is bounded uniformly over all signs.
-/

namespace KadisonKastler

open Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem symmetryPositiveProjection_defect (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (u : Algebra M) (hu : star u=u) (h2 : u*u=1) (x : H) :
    centralVectorDefect J x (symmetryPositiveProjection u hu h2).val.val=
      (1/2:ℝ) • centralVectorDefect J x u.val := by
  change centralVectorDefect J x ((1/2:ℝ) • (1+u.val))=_
  rw [(centralVectorDefect J x).map_smul_of_tower,map_add,centralVectorDefect_one J hJ,
    zero_add]

omit [DecidableEq ι] in
theorem partition_sign_defect_on_pinching (J : H ≃ₗᵢ⋆[ℂ] H)
    (P : ι → AlgebraProjection M) (R : H →L[ℂ] H)
    (hc : ∀ i x, (P i).val.val (R x)=conjugationOperator J (P i).val.val (R x))
    (ε : ι → Bool) (x : H) :
    centralVectorDefect J (R x) (partitionSignOperator P ε).val=0 := by
  rw [partitionSignOperator_val]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [(centralVectorDefect J (R x)).map_smul_of_tower,centralVectorDefect_apply]
  have hs : star (P i).val.val=(P i).val.val :=
    congrArg Subtype.val (P i).property.isSelfAdjoint.star_eq
  rw [hs,hc,sub_self,smul_zero]

attribute [local instance] OAI.KadisonKastler.projectionOperatorNNRat
attribute [local instance] OAI.KadisonKastler.projectionVectorNNRat
theorem exists_partition_projection_gap_oai
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (P : ι → AlgebraProjection M)
    (hP : Pairwise (fun i j => (P i).val*(P j).val=0))
    (hs : (∑ i, (P i).val)=1) (R : H →L[ℂ] H)
    (hR : (∑ i, modularQuadratic J (P i).val)=R)
    (hc : ∀ i x, (P i).val.val (R x)=conjugationOperator J (P i).val.val (R x))
    (ξ η : H) :
    ∃ p : AlgebraProjection M,
      ‖centralVectorDefect J ξ p.val.val‖^2 ≤ ‖(1-R) ξ‖^2 ∧
      (1/4:ℝ)*‖(1-R) η‖^2 ≤ ‖centralVectorDefect J η p.val.val‖^2 := by
  let ev : (H →L[ℂ] H) →ₗ[ℚ≥0] H :=
    { toFun := fun T => T η
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hav : (𝔼 ε : ι → Bool, modularQuadratic J (partitionSignOperator P ε) η)=R η := by
    change (𝔼 ε : ι → Bool, ev (modularQuadratic J (partitionSignOperator P ε)))=ev R
    rw [← map_expect ev]
    exact congrArg ev ((expect_partitionSignOperator_quadratic J P).trans hR)
  have he : (𝔼 ε : ι → Bool, (η-modularQuadratic J (partitionSignOperator P ε) η))=η-R η := by
    rw [Finset.expect_sub_distrib,Fintype.expect_const,hav]
  have hn : ‖η-R η‖ ≤ 𝔼 ε : ι → Bool, ‖η-modularQuadratic J (partitionSignOperator P ε) η‖ := by
    rw [← he]
    apply Finset.le_expect_of_subadditive norm_zero norm_add_le
    intro q x
    rw [← NNRat.cast_smul_eq_nnqsmul ℝ,norm_smul,Real.norm_of_nonneg (by positivity)]
    simpa only [smul_eq_mul] using
      NNRat.cast_smul_eq_nnqsmul ℝ ((q : ℚ≥0)⁻¹) ‖x‖
  obtain ⟨ε,_,hε⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hn
  let u := partitionSignOperator P ε
  have hu : star u=u := partitionSignOperator_star P ε
  have h2 : u*u=1 := partitionSignOperator_sq P hP hs ε
  have hum : u∈unitary (Algebra M) := partitionSignOperator_unitary P hP hs ε
  let p := symmetryPositiveProjection u hu h2
  have hdu (x : H) : ‖centralVectorDefect J x u.val‖=‖x-modularQuadratic J u x‖ := by
    have hu' : star (⟨u,hum⟩ : unitary (Algebra M))=⟨u,hum⟩ := Subtype.ext hu
    rw [centralVectorDefect_unitary_norm_eq J hJ x ⟨u,hum⟩,hu',modularUnitary_coe,norm_sub_rev]
  have hsmall : ‖centralVectorDefect J ξ u.val‖ ≤ 2*‖(1-R) ξ‖ := by
    have hz := partition_sign_defect_on_pinching J P R hc ε ξ
    have hd : centralVectorDefect J (ξ-R ξ) u.val=centralVectorDefect J ξ u.val := by
      simp only [centralVectorDefect_apply,map_sub] at hz ⊢
      rw [sub_sub_sub_comm,hz,sub_zero]
    have hh := centralVectorDefect_norm_le J hJ (ξ-R ξ) u.val
    rw [hd] at hh
    exact hh.trans (by
      change 2*‖ξ-R ξ‖*‖u‖ ≤ 2*‖ξ-R ξ‖
      exact mul_le_of_le_one_right (by positivity) (norm_unitary_le_one ⟨u,hum⟩))
  have hpdef (x : H) : ‖centralVectorDefect J x p.val.val‖=
      (1/2:ℝ)*‖centralVectorDefect J x u.val‖ := by
    rw [symmetryPositiveProjection_defect J hJ u hu h2,norm_smul]
    norm_num
  refine ⟨p,?_,?_⟩
  · rw [hpdef]
    have hn0 := norm_nonneg (centralVectorDefect J ξ u.val)
    have hn1 := norm_nonneg ((1-R) ξ)
    nlinarith only [hsmall,hn0,hn1]
  · rw [hpdef,hdu]
    change (1/4:ℝ)*‖η-R η‖^2 ≤ ((1/2:ℝ)*‖η-modularQuadratic J u η‖)^2
    have hn0 := norm_nonneg (η-R η)
    have hn1 := norm_nonneg (η-modularQuadratic J u η)
    nlinarith only [hε,hn0,hn1]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.exists_partition_projection_gap_oai.{u_1, u_2} := @OAI.KadisonKastler.exists_partition_projection_gap_oai.{u_1, u_2}
