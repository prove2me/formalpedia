-- Prove2me | solution 1 for OAI.KadisonKastler.regularCore_spatial_of_typeIIInfinity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T14:32:20.940362+00:00
-- url     : https://prove2.me/submissions/24f798b8-7223-4235-af2b-b2d8f4fd0f66

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
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
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
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
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
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
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
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K044
import Theorems.Thm_OAI_KadisonKastler_FullMatrixCorner_exists_injective_algebra_containing_entries
import Theorems.Thm_OAI_KadisonKastler_FullMatrixCorner_spatial_of_injective_matrix_subalgebra
import Theorems.Thm_OAI_KadisonKastler_TypeIIInfinityFactor_nonempty_finiteMatrixCornerData
import Theorems.Thm_OAI_KadisonKastler_concrete_unitary_of_regularCore_conjugacy

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The concrete Kadison–Kastler distance

The distance is the operator-norm Hausdorff distance between the closed unit
balls of two concrete, unital von Neumann algebras.  All Hilbert spaces are
allowed, including the zero space. The elementary estimates belong to §2 of
*Universal strong Kadison–Kastler stability* (2026).
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kkDistance_nonneg (M N : VonNeumannAlgebra H) : 0 ≤ kkDistance M N :=
  Metric.hausdorffDist_nonneg

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InvariantOperatorMean
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Operator averaging from an actual scalar invariant mean

The scalar mean is data on bounded scalar functions. Riesz representation
constructs the operator average from its coefficients. No operator-valued
mean, fixed-point projection, or amenability conclusion is assumed.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction BigOperators Topology CStarAlgebra

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

namespace ScalarInvariantMean

variable (m : ScalarInvariantMean G)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem operatorMean_translate (g : G) (F : G →ᵇ (H →L[ℂ] H)) :
    m.operatorMean (translateFamily g F) = m.operatorMean F := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [m.inner_operatorMean, m.inner_operatorMean]
  have he : coefficient (translateFamily g F) x y =
      scalarMeanTranslate g (coefficient F x y) := by ext t; rfl
  rw [he, m.invariant]

attribute [local instance] OAI.KadisonKastler.ScalarInvariantMean.invariantMeanFamilyStarOrder
theorem averageConjugation_apply (U : G →* unitary (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    m.averageConjugation U T = m.operatorMean (conjugationFamily U T) := rfl

theorem averageConjugation_one (U : G →* unitary (H →L[ℂ] H)) :
    m.averageConjugation U 1 = 1 := by
  change m.operatorMean (conjugationFamilyHom U 1) = 1
  rw [show conjugationFamilyHom U 1 = 1 from (conjugationFamilyHom U).map_one]
  exact m.operatorMeanCP_one

theorem averageConjugation_fixed (U : G →* unitary (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : ∀ g, unitaryConj (U g) T = T) : m.averageConjugation U T = T := by
  rw [averageConjugation_apply]
  have h : conjugationFamily U T = BoundedContinuousFunction.const G T := by
    apply BoundedContinuousFunction.ext
    intro g
    exact hT g
  rw [h, m.operatorMean_const]

theorem averageConjugation_invariant (U : G →* unitary (H →L[ℂ] H))
    (T : H →L[ℂ] H) (g : G) :
    unitaryConj (U g) (m.averageConjugation U T) = m.averageConjugation U T := by
  have he : translateFamily (g⁻¹) (conjugationFamily U T) =
      BoundedContinuousFunction.const G (U g : H →L[ℂ] H) * conjugationFamily U T *
        BoundedContinuousFunction.const G (star (U g : H →L[ℂ] H)) := by
    apply BoundedContinuousFunction.ext
    intro t
    change unitaryConj (U ((g⁻¹)⁻¹ * t)) T = _
    rw [inv_inv, map_mul, unitaryConj_mul]
    rfl
  have h := m.operatorMean_translate (g⁻¹) (conjugationFamily U T)
  rw [he, m.operatorMean_right, m.operatorMean_left] at h
  exact h

/-- Invariant algebras are preserved by the actual operator average. -/
theorem averageConjugation_mem (U : G →* unitary (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (hT : ∀ g, unitaryConj (U g) T ∈ M) : m.averageConjugation U T ∈ M :=
  m.operatorMean_mem M _ hT

end ScalarInvariantMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FixedPointGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fixed-point algebras and the common-action gap

The fixed algebra is an actual von Neumann algebra, defined as a commutant.
The scalar invariant mean constructed in `InvariantOperatorMean` averages
ordinary unit-ball approximants into fixed-point approximants without
increasing either their norm or their error. No existence of a scalar mean
or fixed-point averaging map is postulated here.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {G H : Type*} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fixedPointAlgebra_le (U : G →* unitary (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) : fixedPointAlgebra U M ≤ M :=
  fun T hT => ((mem_fixedPointAlgebra_iff U M T).mp hT).1

namespace ScalarInvariantMean

variable [TopologicalSpace G] [DiscreteTopology G]
variable (m : ScalarInvariantMean G) (U : G →* unitary (H →L[ℂ] H))

/-- Actual averaging takes invariant-algebra elements to its fixed algebra. -/
theorem averageConjugation_mem_fixed (M : VonNeumannAlgebra H)
    (hM : ∀ g T, T ∈ M → unitaryConj (U g) T ∈ M)
    {T : H →L[ℂ] H} (hT : T ∈ M) :
    m.averageConjugation U T ∈ fixedPointAlgebra U M := by
  rw [mem_fixedPointAlgebra_iff]
  exact ⟨m.averageConjugation_mem U M T (fun g => hM g T hT),
    m.averageConjugation_invariant U T⟩

theorem averageConjugation_fixed_on_fixed (M : VonNeumannAlgebra H)
    {T : H →L[ℂ] H} (hT : T ∈ fixedPointAlgebra U M) :
    m.averageConjugation U T = T :=
  m.averageConjugation_fixed U T ((mem_fixedPointAlgebra_iff U M T).mp hT).2

theorem averageConjugation_norm_le (T : H →L[ℂ] H) :
    ‖m.averageConjugation U T‖ ≤ ‖T‖ :=
  unital_completelyPositive_norm_le _ (m.averageConjugation_one U) T

include m in
theorem exists_fixedPoint_unitBall_approx
    (M N : VonNeumannAlgebra H)
    (hN : ∀ g T, T ∈ N → unitaryConj (U g) T ∈ N)
    {r : ℝ} (hr : kkDistance M N < r)
    (T : H →L[ℂ] H) (hT : T ∈ unitBall (fixedPointAlgebra U M)) :
    ∃ S ∈ unitBall (fixedPointAlgebra U N), ‖T - S‖ < r := by
  obtain ⟨S, hS, hTS⟩ := exists_unitBall_approx
    (M := M) (N := N) ⟨fixedPointAlgebra_le U M hT.1, hT.2⟩ hr
  refine ⟨m.averageConjugation U S,
    ⟨m.averageConjugation_mem_fixed U N hN hS.1,
      (m.averageConjugation_norm_le U S).trans hS.2⟩, ?_⟩
  have hfix := m.averageConjugation_fixed_on_fixed U M hT.1
  calc
    ‖T - m.averageConjugation U S‖ =
        ‖m.averageConjugation U T - m.averageConjugation U S‖ := by rw [hfix]
    _ = ‖m.averageConjugation U (T - S)‖ := by rw [map_sub]
    _ ≤ ‖T - S‖ := m.averageConjugation_norm_le U _
    _ < r := hTS

include m in
/-- A common unitary action cannot increase the ordinary Kadison--Kastler
gap upon passage to fixed points. -/
theorem kkDistance_fixedPointAlgebra_le
    (M N : VonNeumannAlgebra H)
    (hM : ∀ g T, T ∈ M → unitaryConj (U g) T ∈ M)
    (hN : ∀ g T, T ∈ N → unitaryConj (U g) T ∈ N) :
    kkDistance (fixedPointAlgebra U M) (fixedPointAlgebra U N) ≤ kkDistance M N := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply Metric.hausdorffDist_le_of_mem_dist
    (add_nonneg (kkDistance_nonneg M N) hε.le)
  · intro T hT
    obtain ⟨S, hS, hTS⟩ := m.exists_fixedPoint_unitBall_approx U M N hN
      (lt_add_of_pos_right _ hε) T hT
    exact ⟨S, hS, by simpa only [dist_eq_norm] using hTS.le⟩
  · intro S hS
    obtain ⟨T, hT, hST⟩ := m.exists_fixedPoint_unitBall_approx U N M hM
      (by rw [kkDistance_comm]; exact lt_add_of_pos_right _ hε) S hS
    exact ⟨T, hT, by simpa only [dist_eq_norm] using hST.le⟩

end ScalarInvariantMean

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreActions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normalization by the two actual regular actions

The translation and character formulas imply the required tensor-algebra
normalization. The two actions commute as conjugations, although their
implementing unitary groups commute only up to scalar characters.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Translation preserves the tensor algebra, without any action on `P`. -/
theorem regularTranslation_normalizes_tensor (P : VonNeumannAlgebra H)
    (s : Multiplicative ℝ) {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ regularTensorAlgebra P) :
    unitaryConj (regularRightTranslation (H := H) s) T ∈ regularTensorAlgebra P :=
  tensor_mem_conjugate_of_constant_commute P _
    (fun z => (regularConstant_commute_translation z s).symm) hT

private theorem regularConstant_conjugation (u : unitary (H →L[ℂ] H))
    (z : H →L[ℂ] H) :
    unitaryConj (regularConstantUnitary u) (regularConstantHom volume z) =
      regularConstantHom volume (unitaryConj u z) := by
  change regularConstantHom volume (u : H →L[ℂ] H) * regularConstantHom volume z *
      star (regularConstantHom volume (u : H →L[ℂ] H)) =
    regularConstantHom volume ((u : H →L[ℂ] H) * z * star (u : H →L[ℂ] H))
  rw [map_mul, map_mul, StarHomClass.map_star]

private theorem conjugate_commutant_of_normalizes (P : VonNeumannAlgebra H)
    (u : unitary (H →L[ℂ] H))
    (hu : ∀ x ∈ P, unitaryConj u x ∈ P) {z : H →L[ℂ] H} (hz : z ∈ P.commutant) :
    unitaryConj (star u) z ∈ P.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro x hx
  apply commute_conjugated_of_conjugate_commute (star u)
  have h := VonNeumannAlgebra.mem_commutant_iff.mp hz _ (hu x hx)
  change unitaryConj (star (star u)) x * z = z * unitaryConj (star (star u)) x
  simpa only [star_star] using h

private theorem regularConstant_normalizes_tensor (P : VonNeumannAlgebra H)
    (u : unitary (H →L[ℂ] H)) (hu : ∀ x ∈ P, unitaryConj u x ∈ P)
    {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ regularTensorAlgebra P) :
    unitaryConj (regularConstantUnitary u) T ∈ regularTensorAlgebra P := by
  apply (mem_regularTensorAlgebra_iff P _).mpr
  intro z hz
  apply commute_conjugated_of_conjugate_commute
  have hstar : star (regularConstantUnitary u) = regularConstantUnitary (star u) :=
    (map_inv regularConstantUnitary u).symm
  rw [hstar, regularConstant_conjugation]
  exact (mem_regularTensorAlgebra_iff P T).mp hT _
    (conjugate_commutant_of_normalizes P u hu hz)

/-- The common regular action preserves the tensor algebra whenever the
original group normalizes `P`. -/
theorem regularCoreAction_normalizes_tensor
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (P : VonNeumannAlgebra H)
    (hP : ∀ s x, x ∈ P → unitaryConj (U s) x ∈ P)
    (s : Multiplicative ℝ) {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hT : T ∈ regularTensorAlgebra P) :
    unitaryConj (regularCoreAction U s) T ∈ regularTensorAlgebra P := by
  have he : regularCoreAction U s =
      regularConstantUnitary (U s) * regularRightTranslation (H := H) s := rfl
  rw [he, unitaryConj_mul]
  exact regularConstant_normalizes_tensor P (U s) (hP s)
    (regularTranslation_normalizes_tensor P s hT)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AbelianActionStability
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Abelian action correction and descent

Finite-Cesaro means give the scalar averaging used in the action and
fixed-point arguments. These results apply to the additive real modular
group and its character group, viewed as discrete abelian groups.
-/

namespace KadisonKastler

noncomputable section

universe u v w s

section CommonAction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {G : Type w} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]

/-- Passage to fixed points of an abelian action decreases the gap. -/
theorem kkDistance_abelian_fixedPointAlgebra_le
    (U : G →* unitary (H →L[ℂ] H)) (M N : VonNeumannAlgebra H)
    (hM : ∀ g T, T ∈ M → unitaryConj (U g) T ∈ M)
    (hN : ∀ g T, T ∈ N → unitaryConj (U g) T ∈ N) :
    kkDistance (fixedPointAlgebra U M) (fixedPointAlgebra U N) ≤ kkDistance M N :=
  (abelianScalarInvariantMean G).kkDistance_fixedPointAlgebra_le U M N hM hN

end CommonAction

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreGap
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The regular core gap from the tensor gap

The fixed-point comparison uses the actual invariant mean for the additive
real group. It does not assert that an ordinary gap survives tensor
amplification: the tensor gap remains explicit in this theorem.
-/

namespace KadisonKastler

open MeasureTheory
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- For one common regular action, passage from the tensor algebras to
their actual generated cores decreases the gap. -/
theorem kkDistance_regularCore_le_tensor
    (hComm : PublishedRegularCommutant.{u})
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ ξ, Continuous (fun t : ℝ =>
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
    (M N : VonNeumannAlgebra H)
    (hM : ∀ s T, T ∈ M → unitaryConj (U s) T ∈ M)
    (hN : ∀ s T, T ∈ N → unitaryConj (U s) T ∈ N) :
    kkDistance (regularCoreAlgebra U hU M) (regularCoreAlgebra U hU N) ≤
      kkDistance (regularTensorAlgebra M) (regularTensorAlgebra N) := by
  rw [regularCoreAlgebra_eq_fixed_of_published hComm U hU M hM,
    regularCoreAlgebra_eq_fixed_of_published hComm U hU N hN]
  let : TopologicalSpace (Multiplicative ℝ) := ⊥
  let : DiscreteTopology (Multiplicative ℝ) := ⟨rfl⟩
  exact kkDistance_abelian_fixedPointAlgebra_le (regularCoreAction U)
    (regularTensorAlgebra M) (regularTensorAlgebra N)
    (regularCoreAction_normalizes_tensor U M hM)
    (regularCoreAction_normalizes_tensor U N hN)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreStability
attribute [-instance] _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instSeparableSpaceSubtypePreLpPointedPowerConfigurationComplexMemAddSubgroupPointedPowerHilbert _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulTensorHom_intertwines _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # The finite-corner argument for the actual regular cores

This specializes the proved injective-matrix argument and character descent
to the concrete regular representation.  The semifinite matrix subalgebra
and its finite initial corner are explicit data.  In particular, none of
the action, fixed-point, or range-identification conclusions is assumed.
-/

namespace KadisonKastler

open MeasureTheory
open scoped Topology CStarAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

attribute [local instance] OAI.KadisonKastler.regularCoreStabilityFactorOrder
attribute [local instance] OAI.KadisonKastler.regularCoreStabilityFactorStarOrder
/-- A tensor gap, an injective matrix subalgebra in the source regular
core, and an II₁ initial corner give the original-space conjugacy. -/
theorem regularCore_spatial_of_injective_matrix_subalgebra
    (h : FiniteFactorPublishedInputs.{u})
    (hComm : PublishedRegularCommutant.{u})
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (M N : VonNeumannAlgebra H)
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ ξ, Continuous (fun t : ℝ =>
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
    (hM : ∀ s T, T ∈ M → unitaryConj (U s) T ∈ M)
    (hN : ∀ s T, T ∈ N → unitaryConj (U s) T ∈ N)
    (S : VonNeumannAlgebra (RegularCoreHilbert H))
    (hSM : S ≤ regularCoreAlgebra U hU M) (hS : IsInjective S)
    (E : Submodule ℂ (RegularCoreHilbert H)) [CompleteSpace E]
    (F : FullMatrixCorner E) (hFS : ∀ i j, F.entry i j ∈ S)
    (hCorner : Generator.IsII1Factor
      (representedCorner E (regularCoreAlgebra U hU M)
        (F.zero_zero ▸ hSM (hFS 0 0))).toStarSubalgebra)
    {t g : ℝ} (ht : 0 < t) (htEmbed : 302 * t < 1 / 100)
    (htPosition : 302 * (302 * t) < 174 / 1000000000000000)
    (hgapTensor : kkDistance (regularTensorAlgebra M) (regularTensorAlgebra N) < t)
    (hgap : kkDistance M N < g)
    (htStandard : 3 * 50948 * Real.sqrt (302 * (302 * t)) < 1 / 100000)
    (htSpatial : commonPositionError (302 * (302 * t)) < 1 / 4000000)
    (htCP : 2 * matrixCornerError t < 1 / 1000)
    (hge : g + 2 * matrixCornerError t < 1) :
    ∃ v : unitary (H →L[ℂ] H), Conjugates v M N ∧
      ‖(v : H →L[ℂ] H) - 1‖ ≤ 256 * matrixCornerError t := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hgapCore : kkDistance (regularCoreAlgebra U hU M)
      (regularCoreAlgebra U hU N) < t :=
    (kkDistance_regularCore_le_tensor hComm U hU M N hM hN).trans_lt hgapTensor
  obtain ⟨z, hz, hn⟩ := F.spatial_of_injective_matrix_subalgebra h
    (regularCoreAlgebra U hU M) (regularCoreAlgebra U hU N)
    S hSM hS hFS hCorner ht htEmbed htPosition hgapCore htStandard htSpatial
  obtain ⟨v, hv, hvn⟩ := concrete_unitary_of_regularCore_conjugacy
    hComm hSpectral hDiagonal M N hCorrection hCommutant U hU hM hN z hz
    hgap (by linarith) (by linarith)
  exact ⟨v, hv, hvn.trans (mul_le_mul_of_nonneg_left hn (by norm_num))⟩

/-- The injective matrix subalgebra is constructed from the actual full
matrix corner by increasing factorial-period stages.  Thus the only
semifinite data left here are the full corner and its II₁ initial corner. -/
theorem regularCore_spatial_of_matrix_corner
    (h : FiniteFactorPublishedInputs.{u})
    (hComm : PublishedRegularCommutant.{u})
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (M N : VonNeumannAlgebra H)
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ ξ, Continuous (fun t : ℝ =>
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
    (hM : ∀ s T, T ∈ M → unitaryConj (U s) T ∈ M)
    (hN : ∀ s T, T ∈ N → unitaryConj (U s) T ∈ N)
    (E : Submodule ℂ (RegularCoreHilbert H)) [CompleteSpace E]
    (F : FullMatrixCorner E) (hF : ∀ i j, F.entry i j ∈ regularCoreAlgebra U hU M)
    (hCorner : Generator.IsII1Factor
      (representedCorner E (regularCoreAlgebra U hU M)
        (F.zero_zero ▸ hF 0 0)).toStarSubalgebra)
    {t g : ℝ} (ht : 0 < t) (htEmbed : 302 * t < 1 / 100)
    (htPosition : 302 * (302 * t) < 174 / 1000000000000000)
    (hgapTensor : kkDistance (regularTensorAlgebra M) (regularTensorAlgebra N) < t)
    (hgap : kkDistance M N < g)
    (htStandard : 3 * 50948 * Real.sqrt (302 * (302 * t)) < 1 / 100000)
    (htSpatial : commonPositionError (302 * (302 * t)) < 1 / 4000000)
    (htCP : 2 * matrixCornerError t < 1 / 1000)
    (hge : g + 2 * matrixCornerError t < 1) :
    ∃ v : unitary (H →L[ℂ] H), Conjugates v M N ∧
      ‖(v : H →L[ℂ] H) - 1‖ ≤ 256 * matrixCornerError t := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨S, hSM, hS, hFS⟩ := F.exists_injective_algebra_containing_entries
    (regularCoreAlgebra U hU M) hF
  exact regularCore_spatial_of_injective_matrix_subalgebra h hComm hSpectral hDiagonal
    M N hCorrection hCommutant U hU hM hN S hSM hS E F hFS hCorner
    ht htEmbed htPosition hgapTensor hgap htStandard htSpatial htCP hge

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreSemifinite
attribute [-instance] _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instSeparableSpaceSubtypePreLpPointedPowerConfigurationComplexMemAddSubgroupPointedPowerHilbert _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulTensorHom_intertwines _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # Descent from a type II∞ regular core

All matrix, injectivity, and finite-corner data are constructed from the
ordinary projection-theoretic type II∞ predicate and the published countable
copy theorem. The source-core orientation is retained.
-/

namespace KadisonKastler

open MeasureTheory
open scoped Topology CStarAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

attribute [local instance] OAI.KadisonKastler.regularCoreSemifiniteOrder
attribute [local instance] OAI.KadisonKastler.regularCoreSemifiniteStarOrder
/-- A type II∞ source core yields conjugacy on the original Hilbert space. -/
theorem regularCore_spatial_of_typeIIInfinity_oai
    (h : FiniteFactorPublishedInputs.{u})
    (hComm : PublishedRegularCommutant.{u})
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (M N : VonNeumannAlgebra H)
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ ξ, Continuous (fun t : ℝ =>
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
    (hM : ∀ s T, T ∈ M → unitaryConj (U s) T ∈ M)
    (hN : ∀ s T, T ∈ N → unitaryConj (U s) T ∈ N)
    (hCopies : PublishedProperInfiniteProjectionCopies.{u})
    (hCore : TypeIIInfinityFactor (regularCoreAlgebra U hU M))
    {t g : ℝ} (ht : 0 < t) (htEmbed : 302 * t < 1 / 100)
    (htPosition : 302 * (302 * t) < 174 / 1000000000000000)
    (hgapTensor : kkDistance (regularTensorAlgebra M) (regularTensorAlgebra N) < t)
    (hgap : kkDistance M N < g)
    (htStandard : 3 * 50948 * Real.sqrt (302 * (302 * t)) < 1 / 100000)
    (htSpatial : commonPositionError (302 * (302 * t)) < 1 / 4000000)
    (htCP : 2 * matrixCornerError t < 1 / 1000)
    (hge : g + 2 * matrixCornerError t < 1) :
    ∃ v : unitary (H →L[ℂ] H), Conjugates v M N ∧
      ‖(v : H →L[ℂ] H) - 1‖ ≤ 256 * matrixCornerError t := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let D : FiniteFullMatrixCornerData (regularCoreAlgebra U hU M) :=
    Classical.choice (hCore.nonempty_finiteMatrixCornerData hCopies)
  exact regularCore_spatial_of_matrix_corner h hComm hSpectral hDiagonal
    M N hCorrection hCommutant U hU hM hN (typeIIIInitialSpace D.projection)
    D.matrix D.matrix_mem D.corner_isII1
    ht htEmbed htPosition hgapTensor hgap htStandard htSpatial htCP hge

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.regularCore_spatial_of_typeIIInfinity_oai.{u} := @OAI.KadisonKastler.regularCore_spatial_of_typeIIInfinity_oai.{u}
