-- Prove2me | solution 1 for OAI.KadisonKastler.constructedStabilityCoreInputs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T19:08:53.210242+00:00
-- url     : https://prove2.me/submissions/7ce4a35c-298f-4638-afba-eef48c107d3a

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Subalgebra.Basic
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
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.CStarAlgebra.Unitization
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
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
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
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
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
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.Log
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
import Mathlib.Data.Finset.Sort
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
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.NoncommPiCoprod
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
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
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
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.ProductMeasure
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.SetTheory.Cardinal.Free
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
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Algebra.UniformRing
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
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.Ultrafilter
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K065
import Definitions.Def_Q260K034
import Theorems.Thm_OAI_KadisonKastler_exists_universal_modular_rows
import Theorems.Thm_OAI_KadisonKastler_multiplication_correction_of_quadratic_cochains
import Theorems.Thm_OAI_KadisonKastler_publishedBoundary
import Theorems.Thm_OAI_KadisonKastler_publishedProperInfiniteProjectionCopies
import Theorems.Thm_OAI_KadisonKastler_publishedSimpleDerivationInner
import Theorems.Thm_OAI_KadisonKastler_publishedTypeIIIProjectionComparison
import Theorems.Thm_OAI_KadisonKastler_publishedVonNeumannSpectralCut
import Theorems.Thm_OAI_KadisonKastler_quadraticCochainSolver_of_modular_rows
import Theorems.Thm_OAI_KadisonKastler_scalar_center_of_near_II1
import Theorems.Thm_OAI_KadisonKastler_tomiyama_map_projection_mul
import Theorems.Thm_OAI_KadisonKastler_weakOperatorField_closed_projection_span_eq_top

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryImprovement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The quadratic step in boundary cocycle correction

Only the structural properties of the boundary mean occur here.  The mean
need not be normal.  Covariance cancellation and polar normalization give
the quadratic improvement used in the measurable iteration.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

private theorem boundary_sqrt_scalar_sub_one_sq_le {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t - 1) ^ 2 ≤ (t - 1) ^ 2 := by
  have hlarge : 1 ≤ (Real.sqrt t + 1) ^ 2 := by nlinarith [Real.sqrt_nonneg t]
  calc
    _ ≤ (Real.sqrt t - 1) ^ 2 * (Real.sqrt t + 1) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hlarge (sq_nonneg (Real.sqrt t - 1))]
    _ = _ := by rw [← mul_pow]; congr 1; nlinarith [Real.sq_sqrt ht]

section Ordered

variable [PartialOrder B] [StarOrderedRing B]

/-- The square root cannot increase the operator-norm error from one. -/
theorem norm_sqrt_sub_one_le (a : B) (ha : 0 ≤ a) :
    ‖CFC.sqrt a - 1‖ ≤ ‖a - 1‖ := by
  let b := CFC.sqrt a
  have hb : star b = b := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have haStar : star a = a := ha.isSelfAdjoint.star_eq
  have hbCFC : b = cfc Real.sqrt a := by
    dsimp [b]
    rw [CFC.sqrt_eq_real_sqrt a ha, cfcₙ_eq_cfc]
  have hleft : cfc (fun t : ℝ => (Real.sqrt t - 1) ^ 2) a =
      star (b - 1) * (b - 1) := by
    rw [cfc_pow (fun t : ℝ => Real.sqrt t - 1) 2 a,
      cfc_sub Real.sqrt (fun _ : ℝ => 1) a,
      cfc_const_one ℝ a, ← hbCFC, star_sub, hb, star_one, pow_two]
  have hright : cfc (fun t : ℝ => (t - 1) ^ 2) a =
      star (a - 1) * (a - 1) := by
    rw [cfc_pow (fun t : ℝ => t - 1) 2 a,
      cfc_sub (fun t : ℝ => t) (fun _ : ℝ => 1) a,
      cfc_id' ℝ a, cfc_const_one ℝ a, star_sub, haStar, star_one, pow_two]
  have horder : star (b - 1) * (b - 1) ≤ star (a - 1) * (a - 1) := by
    rw [← hleft, ← hright]
    apply (cfc_le_iff _ _ a).mpr
    intro t ht
    exact boundary_sqrt_scalar_sub_one_sq_le (spectrum_nonneg_of_nonneg ha ht)
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg horder (star_mul_self_nonneg _)
  rw [CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at hn
  change ‖b - 1‖ ≤ ‖a - 1‖
  nlinarith [norm_nonneg (b - 1), norm_nonneg (a - 1)]

end Ordered

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteNeighbor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finiteness of a nearby von Neumann algebra

A finite factor has unitary polar decompositions.  An isometry close to
its unit ball is therefore close to a unitary, hence invertible.  This
proves the finiteness part of the manuscript's finite-neighbor lemma.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- The defect of a contraction near an isometry is at most twice its error. -/
theorem norm_isometry_defect_le {x v : A} (hx : ‖x‖ ≤ 1)
    (hv : star v * v = 1) :
    ‖star x * x - 1‖ ≤ 2 * ‖x - v‖ := by
  have hvn : ‖v‖ ≤ 1 := by
    have h := congrArg norm hv
    rw [CStarRing.norm_star_mul_self] at h
    have h1 : ‖(1 : A)‖ ≤ 1 := norm_unitary_le_one (1 : unitary A)
    nlinarith [norm_nonneg v]
  have he : star x * x - 1 = star x * (x - v) + star (x - v) * v := by
    rw [star_sub, mul_sub, sub_mul, hv]
    noncomm_ring
  calc
    _ ≤ ‖star x * (x - v)‖ + ‖star (x - v) * v‖ := he ▸ norm_add_le _ _
    _ ≤ ‖x‖ * ‖x - v‖ + ‖x - v‖ * ‖v‖ := by
      simpa only [norm_star] using add_le_add
        (norm_mul_le (star x) (x - v)) (norm_mul_le (star (x - v)) v)
    _ ≤ 1 * ‖x - v‖ + ‖x - v‖ * 1 := add_le_add
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hvn (norm_nonneg _))
    _ = _ := by ring

/-- A unitary polar factor is close to its element by its isometry defect. -/
theorem norm_unitary_polar_sub_le (x : A) (u : unitary A)
    [PartialOrder A] [StarOrderedRing A]
    (hu : (u : A) * CFC.abs x = x) :
    ‖(u : A) - x‖ ≤ ‖star x * x - 1‖ := by
  have he : (u : A) - x = (u : A) * (1 - CFC.abs x) := by
    rw [mul_sub, mul_one, hu]
  rw [he, CStarRing.norm_coe_unitary_mul, norm_sub_rev]
  exact norm_sqrt_sub_one_le _ (star_mul_self_nonneg _)

/-- Being within one of a unitary forces an isometry to be unitary. -/
theorem isometry_coisometry_of_near_unitary {v : A}
    (hv : star v * v = 1) (u : unitary A) (hclose : ‖v - (u : A)‖ < 1) :
    v * star v = 1 := by
  nontriviality A
  have hinv : ‖(((Unitary.toUnits u)⁻¹ : Aˣ) : A)‖ = 1 := by
    change ‖star (u : A)‖ = 1
    rw [norm_star, CStarRing.norm_coe_unitary]
  have hunit : IsUnit v :=
    (Units.ofNearby (Unitary.toUnits u) v (by
      simpa only [Unitary.val_toUnits_apply, hinv, inv_one] using hclose)).isUnit
  exact (hunit.mem_unitary_of_star_mul_self hv).2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M N : VonNeumannAlgebra H}

local instance finiteNeighborOrder_r2b9fdc_1 : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance finiteNeighborStarOrder_r2b9fdc_1 : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
/-- Finiteness is preserved by a sufficiently small gap from a finite factor.
This is the finiteness assertion of the manuscript's finite-neighbor lemma;
factoriality is a separate assertion. -/
theorem finite_of_near_finite_factor
    (hfactor : ∀ x : Algebra M, (∀ y : Algebra M, y * x = x * y) →
      ∃ c : ℂ, x = c • (1 : Algebra M))
    (hfinite : ∀ v : Algebra M, star v * v = 1 → v * star v = 1)
    (hgap : kkDistance M N < 1 / 10) :
    ∀ v : Algebra N, star v * v = 1 → v * star v = 1 := by
  intro v hv
  have hvambient : star (v : H →L[ℂ] H) * v = 1 := congrArg Subtype.val hv
  have hvn : ‖(v : H →L[ℂ] H)‖ ≤ 1 := by
    have h := congrArg norm hvambient
    rw [CStarRing.norm_star_mul_self] at h
    have h1 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 :=
      norm_unitary_le_one (1 : unitary (H →L[ℂ] H))
    nlinarith [norm_nonneg (v : H →L[ℂ] H)]
  obtain ⟨x, hx, hclose⟩ := exists_unitBall_approx (M := N) (N := M)
    ⟨v.property, hvn⟩ (by simpa only [kkDistance_comm N M] using hgap)
  rw [norm_sub_rev] at hclose
  let a : Algebra M := ⟨x, hx.1⟩
  obtain ⟨u, hu⟩ := Generator.Tracial.exists_unitary_polar_decomposition hfactor hfinite a
  let U : unitary (H →L[ℂ] H) :=
    Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype) u
  have hdefect : ‖star a * a - 1‖ < 2 * (1 / 10 : ℝ) := by
    have h := norm_isometry_defect_le hx.2 hvambient
    change ‖star a * a - 1‖ ≤ 2 * ‖x - (v : H →L[ℂ] H)‖ at h
    exact h.trans_lt (by nlinarith [hclose])
  have hup : ‖(u : Algebra M) - a‖ < 2 * (1 / 10 : ℝ) :=
    (norm_unitary_polar_sub_le a u hu).trans_lt hdefect
  change ‖(u : Algebra M).val - x‖ < 2 * (1 / 10 : ℝ) at hup
  have hnear : ‖(v : H →L[ℂ] H) - (U : H →L[ℂ] H)‖ < 1 := by
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (v : H →L[ℂ] H) x (U : H →L[ℂ] H)
    have hux : ‖x - (U : H →L[ℂ] H)‖ < 2 * (1 / 10 : ℝ) := by
      change ‖x - (u : Algebra M).val‖ < _
      simpa only [norm_sub_rev] using hup
    rw [norm_sub_rev (v : H →L[ℂ] H) x] at htri
    linarith
  apply Subtype.ext
  exact isometry_coisometry_of_near_unitary hvambient U hnear

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CenterAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering scalar centre from central projections

The centre is represented as the intersection with the concrete commutant.
Spectral approximation in this von Neumann algebra reduces scalarity of its
whole algebra to triviality of its projections.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


/-- The full finite-neighbor conclusion for an initial II₁ factor: the
nearby algebra is finite and has scalar centre. -/
theorem finite_factor_of_near_II1 {M N : VonNeumannAlgebra H}
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hgap : kkDistance M N < 1 / 10) :
    (∀ c : Algebra N, (∀ a : Algebra N, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra N)) ∧
    (∀ v : Algebra N, star v * v = 1 → v * star v = 1) := by
  refine ⟨scalar_center_of_near_II1 hM hgap, ?_⟩
  exact finite_of_near_finite_factor (fun c hc => by
    obtain ⟨z, hz⟩ := hM.factor c hc
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩) hM.finite hgap

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteLinearOperations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Elementary operations on complete bounds -/

namespace KadisonKastler

noncomputable section

variable {A B C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem CompletelyBoundedBy.mono {F : A →ₗ[ℂ] B} {c d : ℝ}
    (hF : CompletelyBoundedBy F c) (hcd : c ≤ d) : CompletelyBoundedBy F d := by
  intro p q X
  exact (hF p q X).trans (mul_le_mul_of_nonneg_right hcd (norm_nonneg X))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DiagonalLocality
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Pointwise locality of operators commuting with scalar multipliers

Cutting down the operator norm inequality by every measurable indicator
gives the same inequality pointwise. This is the boundedness step in
constructing the diagonal field, before choosing any representatives.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Commuting with all scalar projections makes the ambient operator
norm a pointwise bound on every vector-valued function. -/
theorem ae_norm_apply_le_of_commute_indicators
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ (s : Set ℝ) (hs : MeasurableSet s),
      Commute T (regularIndicatorProjection s hs)) (f : RegularCoreHilbert H) :
    ∀ᵐ t : ℝ, ‖T f t‖ ≤ ‖T‖ * ‖f t‖ := by
  have hsq : (fun t : ℝ => ‖T f t‖ ^ 2) ≤ᵐ[volume]
      (fun t => ‖T‖ ^ 2 * ‖f t‖ ^ 2) := by
    apply ae_le_of_forall_setIntegral_le
      ((Lp.memLp (T f)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
      (((Lp.memLp f).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).const_mul _)
    intro s hs _
    rw [integral_const_mul, regular_setIntegral_norm_sq s hs,
      regular_setIntegral_norm_sq s hs]
    have heq : regularIndicatorProjection s hs (T f) =
        T (regularIndicatorProjection s hs f) :=
      congrArg (fun S : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => S f)
        (hT s hs).eq.symm
    rw [heq, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2
  filter_upwards [hsq] with t ht
  rw [← mul_pow] at ht
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp ht

omit [CompleteSpace H] in
/-- The published diagonal-commutant hypothesis supplies exactly the
indicator commutation used in the local norm argument. -/
theorem commute_indicators_of_commute_scalarMultipliers
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ)
      (hC : ∀ t, ‖φ t‖ ≤ C), Commute T (regularScalarMultiplier φ hφ C hC))
    (s : Set ℝ) (hs : MeasurableSet s) :
    Commute T (regularIndicatorProjection s hs) :=
  hT _ _ _ _

theorem ae_norm_apply_sub_le_of_commute_indicators
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ (s : Set ℝ) (hs : MeasurableSet s),
      Commute T (regularIndicatorProjection s hs)) (f g : RegularCoreHilbert H) :
    ∀ᵐ t : ℝ, ‖T f t - T g t‖ ≤ ‖T‖ * ‖f t - g t‖ := by
  have hb := ae_norm_apply_le_of_commute_indicators T hT (f - g)
  rw [map_sub] at hb
  filter_upwards [hb, Lp.coeFn_sub f g, Lp.coeFn_sub (T f) (T g)]
    with t ht hfg hTfg
  simpa only [hfg, hTfg, Pi.sub_apply] using ht

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DiagonalLocalVectors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Local vector representatives for a diagonal operator

Apply the operator to constant vectors cut off on `[-n,n]`. Locality
makes these representatives agree on overlaps. Selecting the interval
of radius `ceil |t|` gives measurable vector values on the whole line.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem diagonalTestVector_ae (n : ℕ) (ξ : H) :
    diagonalTestVector n ξ =ᵐ[volume]
      (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator (fun _ => ξ) :=
  indicatorConstLp_coeFn

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem diagonalTestVector_add (n : ℕ) (ξ η : H) :
    diagonalTestVector n (ξ + η) = diagonalTestVector n ξ + diagonalTestVector n η :=
  indicatorConstLp_add.symm

omit [CompleteSpace H] in
theorem diagonalTestVector_smul (n : ℕ) (c : ℂ) (ξ : H) :
    diagonalTestVector n (c • ξ) = c • diagonalTestVector n ξ := by
  apply Lp.ext
  filter_upwards [diagonalTestVector_ae n (c • ξ), diagonalTestVector_ae n ξ,
    Lp.coeFn_smul c (diagonalTestVector n ξ)] with t hc hξ hs
  rw [hc, hs]
  simp only [Pi.smul_apply, hξ]
  by_cases ht : t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) <;> simp [ht]

theorem diagonalRawVector_measurable [TopologicalSpace.SeparableSpace H]
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (ξ : H) :
    AEStronglyMeasurable (diagonalRawVector T ξ) volume := by
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  have hev : Measurable (fun p : ℕ × (ℕ → H) => p.2 p.1) :=
    measurable_from_prod_countable_right fun n => measurable_pi_apply n
  have hseq : AEMeasurable (fun t : ℝ => fun n : ℕ => T (diagonalTestVector n ξ) t)
      volume := AEMeasurable.of_eval fun n => (Lp.aestronglyMeasurable _).aemeasurable
  exact (hev.comp_aemeasurable
    ((Nat.measurable_ceil.comp measurable_abs).aemeasurable.prodMk hseq)).aestronglyMeasurable

omit [CompleteSpace H] in
theorem diagonalRawVector_add_ae
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (ξ η : H) :
    diagonalRawVector T (ξ + η) =ᵐ[volume]
      fun t => diagonalRawVector T ξ t + diagonalRawVector T η t := by
  have hall : ∀ᵐ t : ℝ, ∀ n : ℕ,
      T (diagonalTestVector n (ξ + η)) t =
        T (diagonalTestVector n ξ) t + T (diagonalTestVector n η) t := by
    apply ae_all_iff.mpr
    intro n
    rw [diagonalTestVector_add, map_add]
    exact Lp.coeFn_add _ _
  exact hall.mono fun t ht => ht (Nat.ceil |t|)

omit [CompleteSpace H] in
theorem diagonalRawVector_smul_ae
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (c : ℂ) (ξ : H) :
    diagonalRawVector T (c • ξ) =ᵐ[volume] fun t => c • diagonalRawVector T ξ t := by
  have hall : ∀ᵐ t : ℝ, ∀ n : ℕ,
      T (diagonalTestVector n (c • ξ)) t = c • T (diagonalTestVector n ξ) t := by
    apply ae_all_iff.mpr
    intro n
    rw [diagonalTestVector_smul, map_smul]
    exact Lp.coeFn_smul _ _
  exact hall.mono fun t ht => ht (Nat.ceil |t|)

variable (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
  (hT : ∀ (s : Set ℝ) (hs : MeasurableSet s),
    Commute T (regularIndicatorProjection s hs))

include hT

theorem diagonalRawVector_norm_ae (ξ : H) :
    ∀ᵐ t : ℝ, ‖diagonalRawVector T ξ t‖ ≤ ‖T‖ * ‖ξ‖ := by
  have hall : ∀ᵐ t : ℝ, ∀ n : ℕ,
      ‖T (diagonalTestVector n ξ) t‖ ≤ ‖T‖ * ‖diagonalTestVector n ξ t‖ :=
    ae_all_iff.mpr fun n => ae_norm_apply_le_of_commute_indicators T hT _
  have hvec : ∀ᵐ t : ℝ, ∀ n : ℕ,
      diagonalTestVector n ξ t = (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator (fun _ => ξ) t :=
    ae_all_iff.mpr fun n => diagonalTestVector_ae n ξ
  filter_upwards [hall, hvec] with t ht hξ
  have hmem : t ∈ Set.Icc (-(Nat.ceil |t| : ℝ)) (Nat.ceil |t| : ℝ) :=
    Set.mem_Icc.mpr (abs_le.mp (Nat.le_ceil |t|))
  simpa only [diagonalRawVector, hξ, Set.indicator_of_mem hmem] using ht (Nat.ceil |t|)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VectorCoreField
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarOperatorKernel.CoherentCore.extendedFunctional_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable operator fields from a countable vector core

Pointwise bounded rational-linear maps commuting with multiplication by
`i` extend to complex-linear operators. Countability gives simultaneous
identities off one null set; dense coefficient tests give measurability.
-/

namespace KadisonKastler

open MeasureTheory Filter TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace CoherentVectorCore

variable {C : RationalComplexCore H} {B : ℝ} {g : C.space → H}

theorem operator_coe (h : CoherentVectorCore C B g) (x : C.space) :
    h.operator (x : H) = g x := C.extendComplex_coe _ _ _ x

theorem norm_operator_le (h : CoherentVectorCore C B g) (hB : 0 ≤ B) :
    ‖h.operator‖ ≤ B :=
  ContinuousLinearMap.opNorm_le_bound _ hB (C.norm_extendComplex_le _ h.bound h.mulI)

end CoherentVectorCore

variable (C : RationalComplexCore H) (B : ℝ) (g : C.space → ℝ → H)

attribute [local instance] OAI.KadisonKastler.vectorCoreNormedSpace
omit [CompleteSpace H] in
theorem coherentVectorCore_ae
    (ha : ∀ x y, (fun t => g (x + y) t) =ᵐ[volume] fun t => g x t + g y t)
    (hr : ∀ (r : ℚ) x, (fun t => g (r • x) t) =ᵐ[volume] fun t => r • g x t)
    (hi : ∀ x, (fun t => g (C.mulI x) t) =ᵐ[volume] fun t => Complex.I • g x t)
    (hb : ∀ x, ∀ᵐ t : ℝ, ‖g x t‖ ≤ B * ‖(x : H)‖) :
    ∀ᵐ t : ℝ, CoherentVectorCore C B (fun x => g x t) := by
  let : Countable C.space := C.countable
  have h1 := ae_all_iff.mpr (fun x => ae_all_iff.mpr (ha x))
  have h2 := ae_all_iff.mpr (fun r => ae_all_iff.mpr (hr r))
  have h3 := ae_all_iff.mpr hi
  have h4 := ae_all_iff.mpr hb
  filter_upwards [h1, h2, h3, h4] with t h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- A bounded operator field agreeing with the supplied core vectors.
The bad set is assigned the zero operator. -/
theorem exists_field_of_vectorCore [SeparableSpace H] (hB : 0 ≤ B)
    (hm : ∀ x, AEStronglyMeasurable (g x) volume)
    (hc : ∀ᵐ t : ℝ, CoherentVectorCore C B (fun x => g x t)) :
    ∃ F : ℝ → H →L[ℂ] H,
      (∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume) ∧
      (∀ t, ‖F t‖ ≤ B) ∧ ∀ x : C.space, (fun t => F t (x : H)) =ᵐ[volume] g x := by
  classical
  let F : ℝ → H →L[ℂ] H := fun t =>
    if ht : CoherentVectorCore C B (fun x => g x t) then ht.operator else 0
  have he (x : C.space) : (fun t => F t (x : H)) =ᵐ[volume] g x := by
    filter_upwards [hc] with t ht
    dsimp [F]
    rw [dite_eq_left ht]
    exact ht.operator_coe x
  have hFn (t : ℝ) : ‖F t‖ ≤ B := by
    dsimp [F]
    split_ifs with ht
    · exact ht.norm_operator_le hB
    · simpa only [norm_zero] using hB
  refine ⟨F, ?_, hFn, he⟩
  let : Countable C.space := C.countable
  have hmcoeff (η ξ : C.space) :
      AEStronglyMeasurable (fun t => inner ℂ (η : H) (F t (ξ : H))) volume := by
    exact ((hm ξ).const_inner (c := (η : H))).congr
      ((he ξ).mono fun t ht => congrArg (fun x : H => inner ℂ (η : H) x) ht.symm)
  exact fun ξ => (operator_field_aestronglyMeasurable_of_dense_coefficients
    ((↑) : C.space → H) C.dense.denseRange_val F hmcoeff ξ).1

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DiagonalDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The real-line diagonal-commutant decomposition

The local representatives determine a bounded operator on the rational
core at almost every point. The pointwise difference bound then proves
that the resulting field represents the original operator on every
L2 vector, without choosing an uncountable common conull set.
-/

namespace KadisonKastler

open MeasureTheory Filter TopologicalSpace

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SeparableSpace H]

theorem exists_diagonalField_of_commute_indicators
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ (s : Set ℝ) (hs : MeasurableSet s),
      Commute T (regularIndicatorProjection s hs)) :
    ∃ F : ℝ → H →L[ℂ] H,
      (∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume) ∧
      (∀ t, ‖F t‖ ≤ ‖T‖) ∧ RepresentsOperatorField volume F T := by
  let C : RationalComplexCore H := Classical.choice (exists_rationalComplexCore H)
  let : Countable C.space := C.countable
  let g : C.space → ℝ → H := fun ξ => diagonalRawVector T (ξ : H)
  have hg : ∀ᵐ t : ℝ, CoherentVectorCore C ‖T‖ (fun ξ => g ξ t) := by
    apply coherentVectorCore_ae
    · intro ξ η
      exact diagonalRawVector_add_ae T ξ η
    · intro r ξ
      simpa only [g, Submodule.coe_smul, ← Rat.cast_smul_eq_qsmul ℂ] using
        diagonalRawVector_smul_ae T (r : ℂ) ξ
    · intro ξ
      exact diagonalRawVector_smul_ae T Complex.I ξ
    · exact fun ξ => diagonalRawVector_norm_ae T hT ξ
  obtain ⟨F, hFm, hFn, hFcore⟩ := exists_field_of_vectorCore C ‖T‖ g
    (norm_nonneg _) (fun ξ => diagonalRawVector_measurable T ξ) hg
  refine ⟨F, hFm, hFn, ?_⟩
  intro f
  have hbound (ξ : C.space) : ∀ᵐ t : ℝ,
      ‖T f t - F t (ξ : H)‖ ≤ ‖T‖ * ‖f t - (ξ : H)‖ := by
    have hall : ∀ᵐ t : ℝ, ∀ n : ℕ,
        ‖T f t - T (diagonalTestVector n (ξ : H)) t‖ ≤
          ‖T‖ * ‖f t - diagonalTestVector n (ξ : H) t‖ :=
      ae_all_iff.mpr fun n => ae_norm_apply_sub_le_of_commute_indicators T hT f _
    have hvec : ∀ᵐ t : ℝ, ∀ n : ℕ,
        diagonalTestVector n (ξ : H) t =
          (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator (fun _ => (ξ : H)) t :=
      ae_all_iff.mpr fun n => diagonalTestVector_ae n (ξ : H)
    filter_upwards [hall, hvec, hFcore ξ] with t ht hξ hFt
    rw [hFt]
    have hmem : t ∈ Set.Icc (-(Nat.ceil |t| : ℝ)) (Nat.ceil |t| : ℝ) :=
      Set.mem_Icc.mpr (abs_le.mp (Nat.le_ceil |t|))
    simpa only [g, diagonalRawVector, hξ, Set.indicator_of_mem hmem] using
      ht (Nat.ceil |t|)
  filter_upwards [ae_all_iff.mpr hbound] with t ht
  have hclosed : IsClosed {ξ : H | ‖T f t - F t ξ‖ ≤ ‖T‖ * ‖f t - ξ‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hpoint : ‖T f t - F t (f t)‖ ≤ ‖T‖ * ‖f t - f t‖ :=
    isClosed_property C.dense.denseRange_val hclosed ht (f t)
  simp only [sub_self, norm_zero, mul_zero] at hpoint
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hpoint (norm_nonneg _)))

/-- Blackadar III.1.6.2--3, for the exact constant Hilbert field over
Lebesgue measure required by the regular-core argument. -/
theorem publishedRealDiagonalDecomposition : PublishedRealDiagonalDecomposition.{u} := by
  intro H _ _ _ _ T hT
  obtain ⟨F, hm, hn, hF⟩ := exists_diagonalField_of_commute_indicators T
    (commute_indicators_of_commute_scalarMultipliers T hT)
  exact ⟨F, hm, Eventually.of_forall hn, hF⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteDimensionalGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite dimensionality across a small algebra gap

A finite net in the second unit ball produces a net of radius less than
one in the first unit ball. Riesz's lemma then forces finite dimensionality.
Only the fixed small constant needed in the type-stability argument is used.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem finiteDimensional_of_unitBall_approx
    (S T : Submodule ℂ B) [FiniteDimensional ℂ T]
    (happrox : ∀ x : S, ‖x‖ ≤ 1 →
      ∃ y : T, ‖y‖ ≤ 1 ∧ ‖(x : B) - (y : B)‖ < 1 / 10) :
    FiniteDimensional ℂ S := by
  classical
  obtain ⟨t, _, ht, hcover⟩ := (isCompact_closedBall (0 : T) 1).finite_cover_balls
    (show (0 : ℝ) < 1 / 10 by norm_num)
  let center (y : T) : S := if h : ∃ x : S, ‖(x : B) - (y : B)‖ < 1 / 5
    then h.choose else 0
  have hcenter (y : T) (h : ∃ x : S, ‖(x : B) - (y : B)‖ < 1 / 5) :
      ‖(center y : B) - (y : B)‖ < 1 / 5 := by
    dsimp [center]
    rw [dite_eq_left h]
    exact h.choose_spec
  let L : Submodule ℂ S := Submodule.span ℂ (center '' t)
  have hfg : L.FG := Submodule.fg_span (ht.image center)
  have : FiniteDimensional ℂ L := Module.Finite.of_fg hfg
  by_contra hdim
  have hproper : ∃ x : S, x ∉ L := by
    by_contra! h
    have htop : L = ⊤ := top_unique (fun x _ => h x)
    rw [htop] at hfg
    exact hdim (Module.Finite.of_fg_top hfg)
  obtain ⟨x, _, hxnorm, hfar⟩ := riesz_lemma_of_lt_one
    (Submodule.closed_of_finiteDimensional L) hproper (show (1 / 2 : ℝ) < 1 by norm_num)
  obtain ⟨y, hynorm, hxy⟩ := happrox x hxnorm.le
  have hyball : y ∈ Metric.closedBall (0 : T) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hynorm
  obtain ⟨z, hzt, hyz⟩ := Set.mem_iUnion₂.mp (hcover hyball)
  have hyz' : ‖(y : B) - (z : B)‖ < 1 / 10 := by
    rw [Metric.mem_ball, dist_eq_norm] at hyz
    change ‖((y - z : T) : B)‖ < 1 / 10 at hyz
    exact hyz
  have hxz : ‖(x : B) - (z : B)‖ < 1 / 5 := by
    have hh : ‖(x : B) - (z : B)‖ ≤
        ‖(x : B) - (y : B)‖ + ‖(y : B) - (z : B)‖ := by
      simpa only [dist_eq_norm] using dist_triangle (x : B) (y : B) (z : B)
    linarith
  have hcz := hcenter z ⟨x, hxz⟩
  have hnear : ‖x - center z‖ < 2 / 5 := by
    have hh : ‖(x : B) - (center z : B)‖ ≤
        ‖(x : B) - (z : B)‖ + ‖(z : B) - (center z : B)‖ := by
      simpa only [dist_eq_norm] using dist_triangle (x : B) (z : B) (center z : B)
    rw [norm_sub_rev (z : B) (center z : B)] at hh
    change ‖(x : B) - (center z : B)‖ < 2 / 5
    linarith
  have hlow := hfar (center z) (Submodule.subset_span ⟨z, hzt, rfl⟩)
  linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A neighbor of a finite-dimensional algebra at the constant used in
the finite-type theorem is itself finite-dimensional. -/
theorem finiteDimensional_of_near_finiteDimensional
    (M N : VonNeumannAlgebra H) [FiniteDimensional ℂ (Algebra N)]
    (hgap : kkDistance M N < 1 / 10) : FiniteDimensional ℂ (Algebra M) := by
  apply finiteDimensional_of_unitBall_approx M.toStarSubalgebra.toSubmodule
    N.toStarSubalgebra.toSubmodule
  intro x hx
  obtain ⟨y, hy, hxy⟩ := exists_unitBall_approx ⟨x.property, hx⟩ hgap
  exact ⟨⟨y, hy.1⟩, hy.2, hxy⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DiffuseInfiniteDimensional
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Diffuse projection algebras are infinite dimensional

Splitting a nonzero projection strictly decreases the dimension of its
right ideal. Finite dimensionality therefore contradicts diffuseness.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (M : VonNeumannAlgebra H)

theorem projectionRightIdeal_strict {p q : Algebra M}
    (hp : IsStarProjection p) (hqp : q * p = q) (hpq : p * q = q) (hne : q ≠ p) :
    projectionRightIdeal M q < projectionRightIdeal M p := by
  apply lt_of_le_of_ne
  · intro x hx
    change p * x = x
    change q * x = x at hx
    rw [← hx, ← mul_assoc, hpq, hx]
  · intro he
    have hmem : p ∈ projectionRightIdeal M q := by
      rw [he]
      exact hp.isIdempotentElem.eq
    exact hne (hqp.symm.trans hmem)

/-- The ordinary II₁-factor projection predicate forces its concrete
operator algebra to be infinite dimensional. -/
theorem not_finiteDimensional_of_isII1Factor (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    ¬ FiniteDimensional ℂ (Algebra M) := by
  intro hdim
  let := hdim
  have hz : ∀ n : ℕ, ∀ p : Algebra M, IsStarProjection p →
      Module.finrank ℂ (projectionRightIdeal M p) = n → p = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hp hpn
      by_contra hne
      obtain ⟨q, hq, hqne, hneq, hpq, hqp⟩ := hM.diffuse p hp hne
      have hlt := Submodule.finrank_lt_finrank_of_lt
        (projectionRightIdeal_strict M hp hqp hpq hneq)
      rw [hpn] at hlt
      exact hqne (ih _ hlt q hq rfl)
  have hone := hz _ 1 (IsStarProjection.one _) rfl
  exact hM.nonzero (congrArg Subtype.val hone).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteOperatorAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finiteness of all operators forces finite Hilbert dimension

An infinite Hilbert basis admits a proper shift. The associated orthogonal
sum is an isometry whose range misses one basis vector.
-/

namespace KadisonKastler

noncomputable section

private theorem exists_injective_avoiding (ι : Type*) [Infinite ι] :
    ∃ (j : ι → ι) (i₀ : ι), Function.Injective j ∧ ∀ i, j i ≠ i₀ := by
  classical
  let e := Infinite.natEmbedding ι
  let d : (ℕ ⊕ ↥((Set.range e)ᶜ)) ≃ ι :=
    (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range e))
  let f : ℕ ⊕ ↥((Set.range e)ᶜ) → ℕ ⊕ ↥((Set.range e)ᶜ) := Sum.map Nat.succ id
  have hf : Function.Injective f := Sum.map_injective.mpr ⟨Nat.succ_injective, Function.injective_id⟩
  refine ⟨fun i => d (f (d.symm i)), d (Sum.inl 0),
    d.injective.comp (hf.comp d.symm.injective), ?_⟩
  intro i hi
  have hh := d.injective hi
  rcases h : d.symm i with n | x <;> simp [f, h] at hh

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finiteDimensional_of_all_isometries_coisometric
    (hfinite : ∀ v : H →L[ℂ] H, star v * v = 1 → v * star v = 1) :
    FiniteDimensional ℂ H := by
  classical
  obtain ⟨I, b, _⟩ := exists_hilbertBasis ℂ H
  by_cases hI : Finite I
  · let := hI
    let := Fintype.ofFinite I
    exact b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  have : Infinite I := not_finite_iff_infinite.mp hI
  obtain ⟨j, i₀, hj, hmiss⟩ := exists_injective_avoiding I
  have ho := b.orthonormal.comp j hj
  let V : H →ₗᵢ[ℂ] H := ho.orthogonalFamily.linearIsometry.comp b.repr.toLinearIsometry
  let v : H →L[ℂ] H := V.toContinuousLinearMap
  have hv : star v * v = 1 := V.adjoint_comp_self
  have hv' := hfinite v hv
  have horth (x : H) : inner ℂ (b i₀) (v x) = 0 := by
    have hsum := (ho.orthogonalFamily.hasSum_linearIsometry (b.repr x)).mapL
      (innerSL ℂ (b i₀))
    have hz (i : I) : inner ℂ (b i₀)
        (LinearIsometry.toSpanSingleton ℂ H (ho.1 i) (b.repr x i)) = 0 := by
      rw [LinearIsometry.toSpanSingleton_apply, inner_smul_right]
      change (b.repr x i) * inner ℂ (b i₀) (b (j i)) = 0
      rw [b.orthonormal.inner_eq_zero (Ne.symm (hmiss i)), mul_zero]
    have he : (fun i : I => innerSL ℂ (b i₀)
        (LinearIsometry.toSpanSingleton ℂ H (ho.1 i) (b.repr x i))) = fun _ => 0 := by
      funext i
      exact hz i
    rw [he] at hsum
    exact hsum.unique hasSum_zero
  have hx : v (star v (b i₀)) = b i₀ :=
    congrArg (fun T : H →L[ℂ] H => T (b i₀)) hv'
  have hzero := horth (star v (b i₀))
  have hone : inner ℂ (b i₀) (b i₀) = 1 := by
    simpa using (orthonormal_iff_ite.mp b.orthonormal i₀ i₀)
  rw [hx, hone] at hzero
  exact False.elim (_root_.one_ne_zero hzero)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeICyclicRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.concreteTraceEmbedding_inner _root_.OAI.KadisonKastler.concreteTraceLeftAction_embedding _root_.OAI.KadisonKastler.concreteTraceLeftUnitary_coe _root_.OAI.KadisonKastler.concreteTraceRightAction_embedding _root_.OAI.KadisonKastler.concreteTraceRightUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.mem_projectionFamilyRemainderSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tomitaPolarCoordinates_root _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The irreducible cyclic representation afforded by a minimal projection

A nonzero vector in a minimal projection determines a faithful irreducible
cyclic representation of a factor.  The construction uses the actual closed
orbit in the given Hilbert space; no classification theorem is invoked.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem exists_nonzero_fixed_vector (p : AlgebraProjection M) (hp : p.val ≠ 0) :
    ∃ ξ : H, ξ ≠ 0 ∧ p.val.val ξ = ξ := by
  have hn : p.val.val ≠ 0 := fun h => hp (Subtype.ext h)
  obtain ⟨x, hx⟩ : ∃ x : H, p.val.val x ≠ 0 := by
    by_contra h
    apply hn
    ext x
    simpa using (not_exists.mp h x)
  refine ⟨p.val.val x, hx, ?_⟩
  exact congrArg (fun a : Algebra M => a.val x) p.property.isIdempotentElem.eq

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIFactorStability
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The type I branch and the projection dichotomy

The diffuse predicate is exactly the projection clause of
`Generator.IsII1Factor` and `TypeIIInfinityFactor`. Its alternative, for
a scalar-center algebra, is the existence of a minimal projection. This
dichotomy is proved directly. The separable type I branch uses the constructed
finite-group embedding.
-/

namespace KadisonKastler

open Generator.Tracial

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A factor either has a minimal projection or every nonzero projection
has a proper nonzero subprojection. No spectral or classification input
is used in this alternative. -/
theorem isTypeIFactor_or_projectionDiffuse {M : VonNeumannAlgebra H}
    (hM : ScalarCenter M) : IsTypeIFactor M ∨ ProjectionDiffuse M := by
  classical
  by_cases htype : IsTypeIFactor M
  · exact Or.inl htype
  right
  intro p hp hp0
  by_contra hnone
  apply htype
  refine ⟨hM, ⟨⟨p, hp⟩, hp0, ?_⟩⟩
  intro q hqp
  by_cases hq0 : q.val = 0
  · exact Or.inl hq0
  right
  apply Subtype.ext
  by_contra hne
  apply hnone
  exact ⟨q.val, q.property, hq0, hne, hqp, projection_mul_of_le hqp⟩

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteType
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.rescaledGraphSubspace_complete _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Discharging preservation of the finite diffuse type

A finite type I factor is finite dimensional. A nearby II₁ factor would
then be finite dimensional as well, contradicting its projection splitting.
Thus its finite neighboring factor is diffuse.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem IsTypeIFactor.finiteDimensional {M : VonNeumannAlgebra H}
    (hM : IsTypeIFactor M)
    (hfinite : ∀ v : Algebra M, star v * v = 1 → v * star v = 1) :
    FiniteDimensional ℂ (Algebra M) := by
  obtain ⟨p, hp⟩ := hM.minimal
  obtain ⟨ξ, hξ, hpξ⟩ := exists_nonzero_fixed_vector p hp.1
  let K := typeICyclicSpace M ξ
  let e : Algebra M ≃⋆ₐ[ℂ] (K →L[ℂ] K) :=
    typeICyclicEquiv hM.factor p hp ξ hξ hpξ
  let f : (K →L[ℂ] K) →⋆ₐ[ℂ] Algebra M := e.symm.toStarAlgHom
  let g : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K) := e.toStarAlgHom
  have : FiniteDimensional ℂ K := by
    apply finiteDimensional_of_all_isometries_coisometric
    intro v hv
    have hpre : star (f v) * f v = 1 := by
      rw [← map_star, ← map_mul, hv, map_one]
    have hh := congrArg g (hfinite (f v) hpre)
    have hgf : g (f v) = v := e.apply_symm_apply v
    simpa only [map_mul, map_star, hgf, map_one] using hh
  exact FiniteDimensional.of_injective e.toAlgEquiv.toLinearMap e.injective

/-- The finite-neighbor type input follows from the constructed type I
representation and the elementary finite-dimensional gap argument. -/
theorem publishedFiniteType : PublishedFiniteType (H := H) := by
  intro M N _ hM hgap
  obtain ⟨hcenter, hfinite⟩ := finite_factor_of_near_II1 hM hgap
  have hN : ScalarCenter N := by
    intro x hx hcomm
    obtain ⟨z, hz⟩ := hcenter ⟨x, hx⟩ (fun a => Subtype.ext (hcomm a.val a.property))
    exact ⟨z, congrArg Subtype.val hz⟩
  by_cases htype : IsTypeIFactor N
  · have := htype.finiteDimensional hfinite
    exact False.elim ((not_finiteDimensional_of_isII1Factor M hM)
      (finiteDimensional_of_near_finiteDimensional M N hgap))
  · exact (isTypeIFactor_or_projectionDiffuse hN).resolve_left htype

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralCommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spectral commutation for real character multipliers

Character commutation passes to every unitary of their commutant.
Finite vector measures then give scalar-multiplier commutation, and
the linear span of unitaries gives the assertion for every operator.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The concrete real-line specialization of Stone's spectral commutant
theorem cited in the downstream regular-core construction. -/
theorem publishedRealSpectralCommutant : PublishedRealSpectralCommutant.{u} := by
  intro H _ _ _ T hT φ hφ C hC
  exact commute_scalarMultiplier_of_characters T hT φ hφ C hC

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonKernelContinuity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Quantitative translation continuity of the Poisson kernel -/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory

noncomputable section

theorem realPoissonKernel_nonneg (t s : ℝ) {r : ℝ} (hr : 0 < r) :
    0 ≤ realPoissonKernel t r s := by
  unfold realPoissonKernel
  positivity

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurablePoisson
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Poisson integration of bounded vector-measurable operator fields

The analytic multiplier fields need only be measurable on each vector.
These averages therefore use vector integrals, without asserting norm
measurability of a field valued in the bounded operators.
-/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem measurablePoissonAverage_apply (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (t r : ℝ) (hr : 0 < r) (x : H) :
    measurablePoissonAverage F hF C hC t r hr x =
      ∫ s, realPoissonKernel t r s • F s x := by
  change (∫ s, F s x ∂cauchyMeasure t (NNReal.mk r hr.le)) = _
  rw [cauchyMeasure_of_scale_ne_zero t (by
    intro h
    exact hr.ne' (congrArg (fun (z : NNReal) => (z : ℝ)) h)),
    integral_withDensity_eq_integral_toReal_smul (measurable_cauchyPDF t (NNReal.mk r hr.le))
      (ae_of_all _ fun s => ENNReal.ofReal_lt_top)]
  congr 1
  funext s
  rw [cauchyPDF, ENNReal.toReal_ofReal (cauchyPDF_pos t (by
    intro h
    exact hr.ne' (congrArg (fun (z : NNReal) => (z : ℝ)) h)) s).le,
    ← realPoissonKernel_eq_cauchyPDFReal t s hr.le]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyUnitKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unit Hardy kernels and their Poisson compression -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Compressing a represented multiplication field gives its Poisson average. -/
theorem hardyKernelCompression_eq_poisson {z : ℂ} (hz : 0 < z.re)
    (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : RepresentsOperatorField volume F T) :
    hardyKernelCompression z hz T = measurablePoissonAverage F hF C hC
      (z.im / (2 * Real.pi)) (z.re / (2 * Real.pi)) (div_pos hz (by positivity)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((hardyKernelInclusion z hz).toContinuousLinearMap.adjoint
    (T (hardyKernelInclusion z hz x))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def,
    measurablePoissonAverage_apply]
  have hint : Integrable (fun s => realPoissonKernel (z.im / (2 * Real.pi))
      (z.re / (2 * Real.pi)) s • F s x) := by
    have hi := (integrable_realPoissonKernel (z.im / (2 * Real.pi)) (r := z.re / (2 * Real.pi))
      (div_pos hz (by positivity))).mul_const (C * ‖x‖)
    apply hi.mono' ((integrable_realPoissonKernel (z.im / (2 * Real.pi)) (r := z.re / (2 * Real.pi))
      (div_pos hz (by positivity))).aestronglyMeasurable.smul (hF x))
    filter_upwards [hC] with s hs
    change ‖realPoissonKernel (z.im / (2 * Real.pi)) (z.re / (2 * Real.pi)) s • F s x‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (realPoissonKernel_nonneg _ _
      (div_pos hz (by positivity)))]
    exact mul_le_mul_of_nonneg_left
      (((F s).le_opNorm x).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg x)))
      (realPoissonKernel_nonneg _ _ (div_pos hz (by positivity)))
  change _ = (innerSL ℂ y) (∫ s, realPoissonKernel (z.im / (2 * Real.pi))
    (z.re / (2 * Real.pi)) s • F s x)
  rw [← (innerSL ℂ y).integral_comp_comm hint]
  apply integral_congr_ae
  filter_upwards [hT (hardyKernelInclusion z hz x),
    regularTensorVector_apply_ae (hardyUnitKernel z hz) x,
    regularTensorVector_apply_ae (hardyUnitKernel z hz) y,
    hardyUnitKernel_density hz] with s hs hx hy hk
  change inner ℂ (regularTensorVector (hardyUnitKernel z hz) y s)
    (T (regularTensorVector (hardyUnitKernel z hz) x) s) = _
  change T (regularTensorVector (hardyUnitKernel z hz) x) s =
    F s (regularTensorVector (hardyUnitKernel z hz) x s) at hs
  rw [hs, hx, hy, map_smul, inner_smul_left, inner_smul_right]
  change star (hardyUnitKernel z hz s) *
    (hardyUnitKernel z hz s * inner ℂ y (F s x)) = _
  rw [← mul_assoc, RCLike.star_def, Complex.conj_mul']
  have hc : (‖hardyUnitKernel z hz s‖ : ℂ) ^ 2 =
      (realPoissonKernel (z.im / (2 * Real.pi)) (z.re / (2 * Real.pi)) s : ℂ) := by
    exact_mod_cast hk
  rw [hc]
  change _ = inner ℂ y (realPoissonKernel (z.im / (2 * Real.pi))
    (z.re / (2 * Real.pi)) s • F s x)
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyEvaluationConstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Constructed evaluation of positive-frequency multipliers

The normalized Cauchy kernel gives the Poisson compression. Its character
shifts and Fourier uniqueness prove invariance of the evaluation kernel.
Thus the compression is an algebra homomorphism on the multiplier algebra.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

universe u

/-- Hardy multiplier evaluation by Poisson compression. -/
theorem publishedHardyMultiplierEvaluation : PublishedHardyMultiplierEvaluation.{u} := by
  intro H _ _ _ _ t r hr
  let z : ℂ := (2 * Real.pi * r : ℝ) + (2 * Real.pi * t : ℝ) * Complex.I
  have hz : 0 < z.re := by
    change 0 < ((2 * Real.pi * r : ℝ) + (2 * Real.pi * t : ℝ) * Complex.I : ℂ).re
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    positivity
  have hcenter : z.im / (2 * Real.pi) = t := by
    dsimp [z]
    simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    field_simp
  have hradius : z.re / (2 * Real.pi) = r := by
    dsimp [z]
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    field_simp
  refine ⟨hardyEvaluationAt (H := H) z hz, ?_⟩
  intro F hF C hC T hT hr'
  rw [hardyEvaluationAt_apply]
  have he := hardyKernelCompression_eq_poisson hz F hF C hC T.val hT
  simpa only [hcenter, hradius] using he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomiyamaNormGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Norm geometry used in the projection theorem

A quadratic norm bound at the identity of a corner forces the real
first-order term to vanish.  This is the elementary norm argument in
Tomiyama's proof, separated from any operator-field representation.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B : Type*} [CStarAlgebra B]

attribute [local instance] OAI.KadisonKastler.tomiyamaOrder
local instance tomiyamaStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

private theorem le_zero_of_inverse_bounds (a b : B)
    (h : ∀ n : ℕ, a ≤ (((n : ℝ) + 1)⁻¹) • b) : a ≤ 0 := by
  have ht : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹) • b) atTop (𝓝 (0 : B)) := by
    simpa only [one_div, zero_smul] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const b)
  exact ge_of_tendsto ht (Eventually.of_forall h)

private theorem corner_real_term_nonpos (p x : B) (hp : IsStarProjection p)
    (hpx : p * x = x) (hxp : x * p = x) (C : ℝ)
    (h : ∀ t : ℝ, ‖p + t • x‖ ^ 2 ≤ 1 + C * t ^ 2) :
    x + star x ≤ 0 := by
  have hps : p * star x = star x := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hxp
  have hsp : star x * p = star x := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hpx
  have hstep (t : ℝ) (ht : 0 < t) : x + star x ≤ t • (C • p) := by
    let z := p + t • x
    have hpz : p * z = z := by
      dsimp [z]
      rw [mul_add, mul_smul_comm, hp.isIdempotentElem.eq, hpx]
    have hzp : z * p = z := by
      dsimp [z]
      rw [add_mul, smul_mul_assoc, hp.isIdempotentElem.eq, hxp]
    have hpsz : p * star z = star z := by
      simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hzp
    have hb : star z * z ≤ (1 + C * t ^ 2) • (1 : B) := by
      calc
        star z * z ≤ algebraMap ℝ B (‖z‖ ^ 2) :=
          CStarAlgebra.star_mul_le_algebraMap_norm_sq
        _ ≤ (1 + C * t ^ 2) • (1 : B) := by
          rw [Algebra.algebraMap_eq_smul_one]
          exact smul_le_smul_of_nonneg_right (h t) zero_le_one
    have hb' := hp.isSelfAdjoint.conjugate_le_conjugate hb
    have hleft : p * (star z * z) * p = star z * z := by
      rw [← mul_assoc p, hpsz, mul_assoc, hzp]
    have hright : p * ((1 + C * t ^ 2) • (1 : B)) * p =
        (1 + C * t ^ 2) • p := by
      rw [mul_smul_comm, mul_one, smul_mul_assoc, hp.isIdempotentElem.eq]
    rw [hleft, hright] at hb'
    have hexpand : star z * z =
        p + t • (x + star x) + t ^ 2 • (star x * x) := by
      simp only [z, star_add, star_smul, star_trivial, hp.isSelfAdjoint.star_eq,
        add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        hp.isIdempotentElem.eq, hpx, hsp]
      module
    rw [hexpand] at hb'
    have hquad : (0 : B) ≤ t ^ 2 • (star x * x) :=
      smul_nonneg (sq_nonneg t) (star_mul_self_nonneg x)
    have hle : p + t • (x + star x) ≤ (1 + C * t ^ 2) • p :=
      (le_add_of_nonneg_right hquad).trans hb'
    have hsplit : (1 + C * t ^ 2) • p = p + t • (t • (C • p)) := by
      module
    rw [hsplit] at hle
    exact (smul_le_smul_iff_of_pos_left ht).mp ((add_le_add_iff_left p).mp hle)
  apply le_zero_of_inverse_bounds (x + star x) (C • p)
  intro n
  exact hstep _ (inv_pos.mpr (by positivity))

/-- A quadratic norm bound at a projection makes a corner element
skew-adjoint. This also applies to the zero corner. -/
theorem corner_skewAdjoint_of_quadratic_bound (p x : B) (hp : IsStarProjection p)
    (hpx : p * x = x) (hxp : x * p = x) (C : ℝ)
    (h : ∀ t : ℝ, ‖p + t • x‖ ^ 2 ≤ 1 + C * t ^ 2) :
    star x = -x := by
  have hle := corner_real_term_nonpos p x hp hpx hxp C h
  have hneg := corner_real_term_nonpos p (-x) hp
    (by rw [mul_neg, hpx]) (by rw [neg_mul, hxp]) C (fun t => by
      simpa only [smul_neg, neg_smul, neg_sq] using h (-t))
  have hge : 0 ≤ x + star x := by
    simpa only [star_neg, ← neg_add, neg_nonpos] using hneg
  have he : x + star x = 0 := le_antisymm hle hge
  exact eq_neg_of_add_eq_zero_left (by rwa [add_comm])

/-- Applying the tangent argument to the imaginary multiple detects
self-adjointness using only the norm. -/
theorem isSelfAdjoint_of_quadratic_norm_bound (x : B) (C : ℝ)
    (h : ∀ t : ℝ, ‖1 + t • (Complex.I • x)‖ ^ 2 ≤ 1 + C * t ^ 2) :
    IsSelfAdjoint x := by
  have hs := corner_skewAdjoint_of_quadratic_bound 1 (Complex.I • x)
    (IsStarProjection.one B) (one_mul _) (mul_one _) C h
  have he : (-Complex.I) • star x = (-Complex.I) • x := by
    simpa only [star_smul, Complex.star_def, Complex.conj_I, neg_smul] using hs
  exact (smul_right_injective B (neg_ne_zero.mpr Complex.I_ne_zero)) he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomiyamaPositive
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positivity of unital contractions

This is the first step of the norm-one projection argument.  Positivity
and adjoint preservation are derived from the norm bound and the unit.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

local instance tomiyamaSourceOrder_r2b9fdc_1 : PartialOrder A := CStarAlgebra.spectralOrder A
local instance tomiyamaSourceStarOrder_r2b9fdc_1 : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
attribute [local instance] OAI.KadisonKastler.tomiyamaTargetOrder
local instance tomiyamaTargetStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

private theorem cstar_norm_one_le (A : Type*) [CStarAlgebra A] : ‖(1 : A)‖ ≤ 1 := by
  have h : ‖star (1 : A) * (1 : A)‖ = ‖(1 : A)‖ * ‖(1 : A)‖ :=
    CStarRing.norm_star_mul_self
  simp only [star_one, one_mul] at h
  nlinarith [norm_nonneg (1 : A)]

private theorem norm_imaginary_perturbation_sq (x : A) (hx : IsSelfAdjoint x) (t : ℝ) :
    ‖1 + t • (Complex.I • x)‖ ^ 2 ≤ 1 + ‖x‖ ^ 2 * t ^ 2 := by
  have he : star (1 + t • (Complex.I • x)) * (1 + t • (Complex.I • x)) =
      1 + t ^ 2 • (star x * x) := by
    simp only [star_add, star_one, star_smul, star_trivial, Complex.star_def,
      Complex.conj_I, hx.star_eq, add_mul, mul_add, one_mul, mul_one,
      smul_mul_assoc, mul_smul_comm]
    match_scalars
    all_goals ring_nf
    all_goals norm_num [Complex.I_sq]
  calc
    ‖1 + t • (Complex.I • x)‖ ^ 2 =
        ‖star (1 + t • (Complex.I • x)) * (1 + t • (Complex.I • x))‖ := by
      rw [CStarRing.norm_star_mul_self, pow_two]
    _ = ‖1 + t ^ 2 • (star x * x)‖ := congrArg norm he
    _ ≤ ‖(1 : A)‖ + ‖t ^ 2 • (star x * x)‖ := norm_add_le _ _
    _ ≤ 1 + ‖x‖ ^ 2 * t ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t),
        CStarRing.norm_star_mul_self]
      nlinarith [cstar_norm_one_le A]

/-- A unital complex-linear contraction preserves self-adjointness. -/
theorem unital_contraction_isSelfAdjoint (P : A →L[ℂ] B)
    (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (h1 : P 1 = 1)
    (x : A) (hx : IsSelfAdjoint x) : IsSelfAdjoint (P x) := by
  apply isSelfAdjoint_of_quadratic_norm_bound (P x) (‖x‖ ^ 2)
  intro t
  have he : P (1 + t • (Complex.I • x)) = 1 + t • (Complex.I • P x) := by
    rw [map_add, h1, P.map_smul_of_tower, map_smul]
  calc
    ‖1 + t • (Complex.I • P x)‖ ^ 2 = ‖P (1 + t • (Complex.I • x))‖ ^ 2 := by rw [he]
    _ ≤ ‖1 + t • (Complex.I • x)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hP _) 2
    _ ≤ 1 + ‖x‖ ^ 2 * t ^ 2 := norm_imaginary_perturbation_sq x hx t

/-- Adjoint preservation follows from the same norm-one hypotheses. -/
theorem unital_contraction_map_star (P : A →L[ℂ] B)
    (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (h1 : P 1 = 1) (x : A) :
    P (star x) = star (P x) := by
  obtain ⟨a, ha, _, hx⟩ := CStarAlgebra.exists_sum_four_nonneg x
  have hs (i : Fin 4) : star (P (a i)) = P (a i) :=
    (unital_contraction_isSelfAdjoint P hP h1 (a i) (ha i).isSelfAdjoint).star_eq
  rw [hx, star_sum, map_sum, map_sum, star_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [star_smul, map_smul, (ha i).star_eq, hs i]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomiyamaDenseProjections
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Extension from projections to their norm-closed span -/

namespace KadisonKastler

open scoped Topology CStarAlgebra

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- The algebraic projection identities extend to a target whose
projections have norm-dense linear span. -/
theorem tomiyama_map_mul_of_dense_projections
    (hdense : (Submodule.span ℂ {e : B | IsStarProjection e}).topologicalClosure = ⊤)
    (φ : B →⋆ₐ[ℂ] A) (P : A →L[ℂ] B)
    (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (hfix : ∀ b, P (φ b) = b) :
    (∀ b x, P (φ b * x) = b * P x) ∧ (∀ x b, P (x * φ b) = P x * b) := by
  have hleft (b : B) (x : A) : P (φ b * x) = b * P x := by
    have hs : (Submodule.span ℂ {e : B | IsStarProjection e} : Set B) ⊆
        {b | P (φ b * x) = b * P x} := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem e he => exact tomiyama_map_projection_mul φ P hP hfix e he x
      | zero =>
        change P (φ 0 * x) = 0 * P x
        simp only [map_zero, zero_mul]
      | add a b ha hb hia hib =>
        change P (φ a * x) = a * P x at hia
        change P (φ b * x) = b * P x at hib
        change P (φ (a + b) * x) = (a + b) * P x
        simp only [map_add, add_mul, hia, hib]
      | smul c a ha hia =>
        change P (φ a * x) = a * P x at hia
        change P (φ (c • a) * x) = (c • a) * P x
        simp only [map_smul, smul_mul_assoc, hia]
    have hc : IsClosed {b : B | P (φ b * x) = b * P x} :=
      isClosed_eq (P.continuous.comp ((map_continuous φ).mul_const x))
        (continuous_id.mul_const (P x))
    have hb : b ∈ closure (Submodule.span ℂ {e : B | IsStarProjection e} : Set B) := by
      rw [← Submodule.topologicalClosure_coe, hdense]
      trivial
    exact (closure_minimal hs hc) hb
  refine ⟨hleft, fun x b => ?_⟩
  have hstar := unital_contraction_map_star P hP
    (by simpa only [map_one] using hfix 1)
  have h := congrArg star (hleft (star b) (star x))
  simpa only [← hstar, star_mul, star_star, ← map_star] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MultiplicationCorrectionFromRows
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Multiplication correction from Christensen--Sinclair row averaging

A modular row limit supplies the cochain estimate for multiplication correction.
-/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.correctionRowsOrder
attribute [local instance] OAI.KadisonKastler.correctionRowsStarOrder
/-- A single modular row net suffices for quantitative multiplication correction. -/
theorem publishedMultiplicationCorrection_of_modular_rows (M : VonNeumannAlgebra H)
    {ι : Type*} (ω : Ultrafilter ι) (n : ι → ℕ)
    (r : (i : ι) → Fin (n i) → Algebra M)
    (hr : ∀ i, ∑ k, r i k * star (r i k) = 1)
    (hav : ∀ (F : Algebra M →ₗ[ℂ] Algebra M) (c : ℝ), 0 ≤ c → CompletelyBoundedBy F c →
      ∃ z : Algebra M, ∀ y ξ η, Tendsto
        (fun i => inner ℂ η ((finiteRightAverage (r i) F y : H →L[ℂ] H) ξ))
        (ω : Filter ι) (𝓝 (inner ℂ η (((z * y : Algebra M) : H →L[ℂ] H) ξ)))) :
    PublishedMultiplicationCorrection M := by
  intro m hm hs c hc hc1 hf
  obtain ⟨L, hL, hLs, hLb⟩ := multiplication_correction_of_quadratic_cochains
    (quadraticCochainSolver_of_modular_rows M ω n r hr hav) m hm hs hc hc1 hf
  exact ⟨L, hL, hLs, hLb.mono (by linarith)⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MultiplicationCorrectionConstruction
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.traceFreeCopy_inner _root_.OAI.Generator.Tracial.traceFreeHilbertCoefficient_apply _root_.OAI.Generator.Tracial.traceFreeInclusion_inner _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.concreteTraceEmbedding_inner _root_.OAI.KadisonKastler.concreteTraceLeftAction_embedding _root_.OAI.KadisonKastler.concreteTraceLeftUnitary_coe _root_.OAI.KadisonKastler.concreteTraceRightAction_embedding _root_.OAI.KadisonKastler.concreteTraceRightUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tomitaPolarCoordinates_root _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Ricard--Roydor multiplication correction

The common modular row limit and complete-norm Newton iteration give
the correction and its quantitative bound.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.correctionConstructionOrder
local instance correctionConstructionStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

theorem publishedMultiplicationCorrection (M : VonNeumannAlgebra H) :
    PublishedMultiplicationCorrection M := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · let := hH
    intro m _ _ q hq _ _
    refine ⟨LinearEquiv.refl ℂ (Algebra M), fun _ _ => Subsingleton.elim _ _,
      fun _ => Subsingleton.elim _ _, ?_⟩
    have he : (LinearEquiv.refl ℂ (Algebra M)).toLinearMap - LinearMap.id = 0 := by
      ext a
      simp
    rw [he]
    intro p r X
    rw [matrix_map_zero, norm_zero]
    positivity
  · let := hH
    obtain ⟨ω, n, r, hr, hm⟩ := exists_universal_modular_rows M
    exact publishedMultiplicationCorrection_of_modular_rows M ω n r hr hm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomiyamaField
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Tomiyama's bimodule identity for measurable operator fields

The measurable representative algebra has norm-dense projection span, by
the pointwise spectral construction. This property descends through its
quotient map. The projection identities for contractive retractions
therefore give the field version of Tomiyama's theorem.
-/

namespace KadisonKastler

open scoped Topology CStarAlgebra

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : MeasureTheory.Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasureTheory.IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

omit [Group G] [DiscreteTopology G] [MeasureTheory.IsFiniteMeasure μ]
  [TopologicalSpace.SeparableSpace H] in
/-- The constant-field specialization of Tomiyama's theorem is proved
from the C-star norm geometry and measurable spectral projections. -/
theorem publishedFieldTomiyama : PublishedFieldTomiyama (G := G) (H := H) (μ := μ) := by
  intro E hE hfix
  exact tomiyama_map_mul_of_dense_projections
    (weakOperatorField_closed_projection_span_eq_top (H := H) (μ := μ))
    (operatorFieldDiagonal (G := G) (H := H) (μ := μ)) E hE hfix

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HomogeneityStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Universal strong stability from faithful-state homogeneity alone

The concrete two-ratio product has a scalar bicentralizer and an expected
matrix subfactor in every required representation. Faithful-state
homogeneity supplies the state comparisons needed for the stability bound.
-/

namespace KadisonKastler
noncomputable section
universe u

/-- Modular core estimates independent of expected subfactors. -/
theorem constructedStabilityCoreInputs_oai : ModularCorePublishedInputs.{u} := {
  finite := {
    boundary := publishedBoundary
    tomiyama := by
      intro H _ _ _ _ G D _ _ _ _ μ _
      exact publishedFieldTomiyama
    finiteType := fun H _ _ _ _ => publishedFiniteType }
  coreCommutant := publishedRegularCommutant
  realSpectral := publishedRealSpectralCommutant
  diagonal := publishedRealDiagonalDecomposition
  copies := publishedProperInfiniteProjectionCopies
  spectral := publishedVonNeumannSpectralCut
  comparison := publishedTypeIIIProjectionComparison
  sakai := publishedSimpleDerivationInner
  hardy := publishedHardyMultiplierEvaluation
  correction := fun H _ _ _ M => publishedMultiplicationCorrection M }

end
end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.constructedStabilityCoreInputs_oai.{u} := @OAI.KadisonKastler.constructedStabilityCoreInputs_oai.{u}
