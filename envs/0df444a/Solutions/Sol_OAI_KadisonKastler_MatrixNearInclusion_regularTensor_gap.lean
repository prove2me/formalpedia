-- Prove2me | solution 1 for OAI.KadisonKastler.MatrixNearInclusion.regularTensor_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:51:52.626974+00:00
-- url     : https://prove2.me/submissions/2abe57bb-5d2d-4cc3-bb1c-b57d18e7d3ec

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
import Definitions.Def_Q260K023
import Definitions.Def_Q260K071

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InfiniteCornerInflation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Inflation through countably many matrix corners

The hypotheses are the algebraic matrix-unit relations and the strong sum
of their diagonal projections. They give an actual Hilbert direct-sum
decomposition. A corner operator is then applied on each summand; in
particular a corner unitary inflates with no loss in displacement.
-/

namespace KadisonKastler

open scoped BigOperators Topology
open Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

namespace FullMatrixCorner

variable {E} (F : FullMatrixCorner E)

theorem column_adjoint_apply (i : ℕ) (x : H) :
    (F.column i).toContinuousLinearMap.adjoint x =
      E.orthogonalProjectionOnto (F.entry 0 i x) := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (F.entry i 0 y) x =
    inner ℂ y (E.orthogonalProjectionOnto (F.entry 0 i x))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  rw [← F.star_entry i 0, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

theorem coordinates_apply (x : H) (i : ℕ) :
    F.coordinates x i = E.orthogonalProjectionOnto (F.entry 0 i x) := by
  rw [← F.column_adjoint_apply]
  apply ext_inner_left ℂ
  intro y
  calc
    inner ℂ y (F.coordinates x i) =
        inner ℂ (lp.single 2 i y) (F.coordinates x) :=
      (lp.inner_single_left (𝕜 := ℂ) i y (F.coordinates x)).symm
    _ = inner ℂ (F.coordinates.symm (lp.single 2 i y))
        (F.coordinates.symm (F.coordinates x)) :=
      (F.coordinates.symm.inner_map_map _ _).symm
    _ = inner ℂ (F.column i y) x := by
      rw [F.coordinates_symm_single, F.coordinates.symm_apply_apply]
    _ = inner ℂ y ((F.column i).toContinuousLinearMap.adjoint x) :=
      (ContinuousLinearMap.adjoint_inner_right (F.column i).toContinuousLinearMap y x).symm

theorem matrixEntry_apply (T : H →L[ℂ] H) (i j : ℕ) (x : E) :
    F.matrixEntry T i j x =
      E.orthogonalProjectionOnto (F.entry 0 i (T (F.entry j 0 x))) := by
  exact F.column_adjoint_apply i _

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InflatedConjugacy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.FullMatrixCorner.regroupingIsometry_column _root_.OAI.KadisonKastler.FullMatrixCorner.regroupingOperator_column _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransport_entry _root_.OAI.KadisonKastler.canonicalMatrixCorner_entry _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering the full algebra from its common matrix corners -/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem extension_matrixEntry (T : H →L[ℂ] H) (i j : ℕ) :
    cornerExtension E (F.matrixEntry T i j) = F.entry 0 i * T * F.entry j 0 := by
  have he : F.matrixEntry T i j =
      cornerCompression E (F.entry 0 i * T * F.entry j 0) := by
    apply ContinuousLinearMap.ext
    intro x
    exact F.matrixEntry_apply T i j x
  rw [he, cornerExtension_compression, ← F.zero_zero]
  calc
    F.entry 0 0 * (F.entry 0 i * T * F.entry j 0) * F.entry 0 0 =
        (F.entry 0 0 * F.entry 0 i) * T * (F.entry j 0 * F.entry 0 0) := by
      noncomm_ring
    _ = _ := by rw [F.mul_entry, F.mul_entry]; simp

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AmplifiedAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransport_entry _root_.OAI.KadisonKastler.canonicalCoordinate_apply _root_.OAI.KadisonKastler.canonicalInitialEquiv_apply _root_.OAI.KadisonKastler.canonicalInitialEquiv_symm_apply _root_.OAI.KadisonKastler.canonicalMatrixCorner_column _root_.OAI.KadisonKastler.canonicalMatrixCorner_entry _root_.OAI.KadisonKastler.canonicalMatrixUnit_apply _root_.OAI.KadisonKastler.canonicalSingle_apply _root_.OAI.KadisonKastler.countableOperatorEntry_apply _root_.OAI.KadisonKastler.countableOperatorEntry_diagonal_mul _root_.OAI.KadisonKastler.countableOperatorEntry_mul_diagonal _root_.OAI.KadisonKastler.countableTensorAlgebraic_tmul _root_.OAI.KadisonKastler.countableTensorEquiv_symm_single _root_.OAI.KadisonKastler.countableTensorEquiv_tmul _root_.OAI.KadisonKastler.countableTensorIsometry_tmul _root_.OAI.KadisonKastler.countableTensorVector_apply _root_.OAI.KadisonKastler.countableTensorVector_single _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_canonicalInitialSpace _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A concrete infinite amplification

The amplification of a corner algebra is the commutant of its diagonally
represented commutant. Its matrix entries are exactly the operators in the
corner algebra. This construction uses the actual countable matrix units.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem norm_partialDiagonal_apply_le (s : Finset ℕ) (x : H) :
    ‖F.partialDiagonal s x‖ ≤ ‖x‖ := by
  rw [← F.coordinates.norm_map, ← F.coordinates.norm_map x]
  apply lp.norm_mono (by norm_num)
  intro i
  have he : F.coordinates (F.partialDiagonal s x) i =
      if i ∈ s then F.coordinates x i else 0 := by
    have hv : F.coordinates (F.partialDiagonal s x) =
        ∑ k ∈ s, lp.single 2 k (F.coordinates x k) := by
      simp only [partialDiagonal, sum_apply, map_sum, F.diagonal_apply,
        F.coordinates_column, ← F.coordinates_apply]
    rw [hv]
    change (⇑(∑ k ∈ s, lp.single 2 k (F.coordinates x k))) i = _
    rw [lp.coeFn_sum]
    simp [Finset.sum_apply, lp.single_apply, Pi.single_apply]
  rw [he]
  split_ifs <;> simp

theorem norm_partialDiagonal_le (s : Finset ℕ) : ‖F.partialDiagonal s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using F.norm_partialDiagonal_apply_le s x

theorem inner_matrixEntry (T : H →L[ℂ] H) (i j : ℕ) (x y : E) :
    inner ℂ y (F.matrixEntry T i j x) = inner ℂ (F.column i y) (T (F.column j x)) := by
  exact ContinuousLinearMap.adjoint_inner_right (F.column i).toContinuousLinearMap y _

theorem matrixEntry_inflate_mul (S : E →L[ℂ] E) (T : H →L[ℂ] H) (i j : ℕ) :
    F.matrixEntry (F.inflateHom S * T) i j = S * F.matrixEntry T i j := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [F.inner_matrixEntry]
  change inner ℂ (F.column i y) (F.inflateHom S (T (F.column j x))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (star (F.inflateHom S) (F.column i y)) (T (F.column j x)) = _
  rw [← map_star, F.inflateHom_column, ← F.inner_matrixEntry]
  exact ContinuousLinearMap.adjoint_inner_left S (F.matrixEntry T i j x) y

theorem matrixEntry_mul_inflate (S : E →L[ℂ] E) (T : H →L[ℂ] H) (i j : ℕ) :
    F.matrixEntry (T * F.inflateHom S) i j = F.matrixEntry T i j * S := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [F.inner_matrixEntry]
  change inner ℂ (F.column i y) (T (F.inflateHom S (F.column j x))) = _
  rw [F.inflateHom_column, ← F.inner_matrixEntry]
  rfl

theorem ext_matrixEntry {T U : H →L[ℂ] H}
    (h : ∀ i j, F.matrixEntry T i j = F.matrixEntry U i j) : T = U := by
  apply F.ext_on_columns
  intro j x
  apply F.eq_of_inner_columns
  intro i y
  rw [← F.inner_matrixEntry, ← F.inner_matrixEntry, h]

theorem mem_amplifiedAlgebra_iff_commute (M : VonNeumannAlgebra E) (T : H →L[ℂ] H) :
    T ∈ F.amplifiedAlgebra M ↔
      ∀ S ∈ M.commutant, Commute (F.inflateHom S) T := by
  change T ∈ StarSubalgebra.centralizer ℂ _ ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h S hS
    exact (h (F.inflateHom S) ⟨S, hS, rfl⟩).1
  · intro h _ hS
    obtain ⟨S, hS, rfl⟩ := hS
    refine ⟨(h S hS).eq, ?_⟩
    rw [← map_star]
    exact (h (star S) (star_mem hS)).eq

/-- Matrix-entry membership characterizes the concrete amplification. -/
theorem mem_amplifiedAlgebra_iff (M : VonNeumannAlgebra E) (T : H →L[ℂ] H) :
    T ∈ F.amplifiedAlgebra M ↔ ∀ i j, F.matrixEntry T i j ∈ M := by
  rw [F.mem_amplifiedAlgebra_iff_commute]
  constructor
  · intro h i j
    rw [← M.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
    intro S hS
    have hh := congrArg (fun R => F.matrixEntry R i j) (h S hS).eq
    simpa only [F.matrixEntry_inflate_mul, F.matrixEntry_mul_inflate] using hh
  · intro h S hS
    apply F.ext_matrixEntry
    intro i j
    rw [F.matrixEntry_inflate_mul, F.matrixEntry_mul_inflate]
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hS _ (h i j)).symm

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteBlockExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransport_entry _root_.OAI.KadisonKastler.canonicalMatrixCorner_column _root_.OAI.KadisonKastler.canonicalMatrixCorner_entry _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite blocks of a countable amplification

Finite operator matrices act on the first finitely many matrix summands.
Their extension is an isometric nonunital star homomorphism. These are the
bounded approximants used for the infinite-amplification gap estimate.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem matrixEntry_blockElement (i j k l : ℕ) (T : E →L[ℂ] E) :
    F.matrixEntry (F.blockElement k l T) i j = if i = k ∧ l = j then T else 0 := by
  have hinj : Function.Injective (cornerExtension E) :=
    Function.LeftInverse.injective (cornerCompression_extension E)
  apply hinj
  rw [F.extension_matrixEntry]
  have he : F.entry 0 i * F.blockElement k l T * F.entry j 0 =
      (F.entry 0 i * F.entry k 0) * cornerExtension E T * (F.entry 0 l * F.entry j 0) := by
    unfold blockElement
    noncomm_ring
  rw [he, F.mul_entry, F.mul_entry]
  by_cases hik : i = k <;> by_cases hlj : l = j
  · simp only [hik, hlj, ite_true, if_true, F.zero_zero, true_and]
    rw [starProjection_mul_cornerExtension, cornerExtension_mul_starProjection]
  · simp [hik, hlj]
  · simp [hik, hlj]
  · simp [hik, hlj]

theorem matrixEntry_sum {ι : Type*} (s : Finset ι) (T : ι → H →L[ℂ] H) (i j : ℕ) :
    F.matrixEntry (∑ a ∈ s, T a) i j = ∑ a ∈ s, F.matrixEntry (T a) i j := by
  apply ContinuousLinearMap.ext
  intro x
  simp [matrixEntry, sum_apply, map_sum]

theorem matrixEntry_finiteBlock {n : ℕ}
    (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) (i j : Fin n) :
    F.matrixEntry (F.finiteBlock X) i j = X i j := by
  simp only [finiteBlock, F.matrixEntry_sum, F.matrixEntry_blockElement]
  have hsum (f : Fin n → Fin n → (E →L[ℂ] E)) :
      (∑ k : Fin n, ∑ l : Fin n,
        if (i : ℕ) = k ∧ (l : ℕ) = j then f k l else 0) = f i j := by
    rw [Finset.sum_eq_single i]
    · simp [Fin.val_inj]
    · intro k _ hki
      have hi : (i : ℕ) ≠ k := fun h => hki (Fin.ext h.symm)
      simp [hi]
    · simp
  exact hsum (fun k l => X k l)

theorem finiteBlockHom_injective (n : ℕ) : Function.Injective (F.finiteBlockHom n) := by
  intro X Y h
  apply Matrix.ext
  intro i j
  have hh := congrArg (fun T => F.matrixEntry T i j) h
  change F.matrixEntry (F.finiteBlock X) i j = F.matrixEntry (F.finiteBlock Y) i j at hh
  simpa only [F.matrixEntry_finiteBlock] using hh

attribute [local instance] OAI.KadisonKastler.FullMatrixCorner.finiteBlockOperatorOrder
attribute [local instance] OAI.KadisonKastler.FullMatrixCorner.finiteBlockOperatorStarOrder
theorem norm_finiteBlock {n : ℕ} (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) :
    ‖F.finiteBlock X‖ = ‖X‖ :=
  NonUnitalStarAlgHom.norm_map (F.finiteBlockHom n) (F.finiteBlockHom_injective n) X

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteBlockCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransport_entry _root_.OAI.KadisonKastler.canonicalMatrixCorner_entry _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Contractive finite compressions of the countable amplification -/

namespace KadisonKastler

open Filter
open scoped BigOperators CStarAlgebra Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

attribute [local instance] OAI.KadisonKastler.FullMatrixCorner.compressionOperatorStarOrder
theorem blockElement_matrixEntry (T : H →L[ℂ] H) (i j : ℕ) :
    F.blockElement i j (F.matrixEntry T i j) = F.entry i i * T * F.entry j j := by
  rw [blockElement, F.extension_matrixEntry]
  calc
    _ = (F.entry i 0 * F.entry 0 i) * T * (F.entry j 0 * F.entry 0 j) := by
      noncomm_ring
    _ = _ := by rw [F.mul_entry, F.mul_entry]; simp

theorem finiteBlock_compression (n : ℕ) (T : H →L[ℂ] H) :
    F.finiteBlock (F.finiteCompression n T) =
      F.partialDiagonal (Finset.range n) * T * F.partialDiagonal (Finset.range n) := by
  have hd : (∑ i : Fin n, F.entry i i) = F.partialDiagonal (Finset.range n) :=
    Fin.sum_univ_eq_sum_range (fun i => F.entry i i) n
  simp only [finiteBlock, finiteCompression, F.blockElement_matrixEntry]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [hd]

attribute [local instance] OAI.KadisonKastler.FullMatrixCorner.compressionOperatorOrder
theorem norm_finiteCompression_le (n : ℕ) (T : H →L[ℂ] H) :
    ‖F.finiteCompression n T‖ ≤ ‖T‖ := by
  rw [← F.norm_finiteBlock, F.finiteBlock_compression]
  calc
    _ ≤ (‖F.partialDiagonal (Finset.range n)‖ * ‖T‖) *
        ‖F.partialDiagonal (Finset.range n)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖T‖) * 1 := by
      gcongr <;> exact F.norm_partialDiagonal_le _
    _ = ‖T‖ := by ring

theorem blockElement_mem_amplifiedAlgebra (M : VonNeumannAlgebra E)
    (i j : ℕ) {T : E →L[ℂ] E} (hT : T ∈ M) :
    F.blockElement i j T ∈ F.amplifiedAlgebra M := by
  rw [F.mem_amplifiedAlgebra_iff]
  intro k l
  rw [F.matrixEntry_blockElement]
  split_ifs
  · exact hT
  · exact M.zero_mem

theorem finiteBlock_mem_amplifiedAlgebra (M : VonNeumannAlgebra E) {n : ℕ}
    (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) (hX : ∀ i j, X i j ∈ M) :
    F.finiteBlock X ∈ F.amplifiedAlgebra M := by
  apply (F.amplifiedAlgebra M).sum_mem
  intro i _
  apply (F.amplifiedAlgebra M).sum_mem
  intro j _
  exact F.blockElement_mem_amplifiedAlgebra M i j (hX i j)

theorem finiteBlock_compression_tendsto (T : H →L[ℂ] H) (x y : H) :
    Tendsto (fun n => inner ℂ y (F.finiteBlock (F.finiteCompression n T) x))
      atTop (𝓝 (inner ℂ y (T x))) := by
  have ht (z : H) := (F.partialDiagonal_tendsto z).comp tendsto_finset_range
  have hi := (ht y).inner (𝕜 := ℂ) (T.continuous.continuousAt.tendsto.comp (ht x))
  apply hi.congr
  intro n
  rw [F.finiteBlock_compression, mul_apply_eq_comp, mul_apply_eq_comp]
  rw [← ContinuousLinearMap.adjoint_inner_left (F.partialDiagonal (Finset.range n))
    (T (F.partialDiagonal (Finset.range n) x)) y]
  simp only [← ContinuousLinearMap.star_eq_adjoint, F.partialDiagonal_star]
  rfl

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Faithful representations are completely isometric

Injective star-algebra homomorphisms preserve C⋆-norms at each square
matrix level. The isometric corner embedding then gives the same statement
for every rectangular matrix size used in the perturbation estimates.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

/-- Faithfulness preserves the norm of each square amplification. -/
theorem injective_starAlgHom_matrix_norm (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    {n : Type*} [Fintype n] (X : CStarMatrix n n A) :
    ‖CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X‖ = ‖X‖ := by
  change ‖CStarMatrix.mapₙₐ φ.toNonUnitalStarAlgHom X‖ = ‖X‖
  exact NonUnitalStarAlgHom.norm_map _ (injective_starAlgHom_matrix φ hφ) X

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakCPLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positivity and norm bounds in pointwise weak operator limits

These lemmas retain the complete positivity of the maps obtained from
finite Hilbert-space tests. No normality of the limiting map is needed.
-/

namespace KadisonKastler

open Filter
open scoped Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} {l : Filter ι} [l.NeBot]

omit [CompleteSpace H] in
/-- A uniform operator norm bound survives a weak coefficient limit. -/
theorem norm_le_of_weak_limit {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (T : ι → H →L[ℂ] K) (S : H →L[ℂ] K)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C)
    (ht : ∀ x y, Tendsto (fun i => inner ℂ y (T i x)) l (𝓝 (inner ℂ y (S x)))) :
    ‖S‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC
  intro x y hx hy
  change (inner ℂ (S x) y).re ≤ C
  have hb (i : ι) : (inner ℂ y (T i x)).re ≤ C := by
    calc
      _ ≤ ‖inner ℂ y (T i x)‖ := Complex.re_le_norm _
      _ ≤ ‖y‖ * ‖T i x‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (C * ‖x‖) := mul_le_mul_of_nonneg_left
        ((T i).le_of_opNorm_le (hT i) x) (norm_nonneg y)
      _ = C := by rw [hx, hy]; ring
  have hr := (Complex.continuous_re.tendsto _).comp (ht x y)
  rw [show (inner ℂ (S x) y).re = (inner ℂ y (S x)).re from
    inner_re_symm (𝕜 := ℂ) (S x) y]
  exact le_of_tendsto hr (Eventually.of_forall hb)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AmplificationGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Passing matrix approximants to the infinite amplification

Finite compressions have norm at most one. Weak operator compactness gives
a single limiting approximant in the target amplification, retaining the
same error at every coefficient and therefore in operator norm.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators CStarAlgebra Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

attribute [local instance] OAI.KadisonKastler.FullMatrixCorner.amplificationGapOrder
attribute [local instance] OAI.KadisonKastler.FullMatrixCorner.amplificationGapStarOrder
/-- Uniform finite matrix approximation implies approximation in the
actual countable amplification, with no loss of constant. -/
theorem exists_amplified_approx_of_matrix_approx
    (M N : VonNeumannAlgebra E) {r : ℝ} (hr : 0 ≤ r)
    (hnear : ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)),
      (∀ i j, X i j ∈ M) → ‖X‖ ≤ 1 →
      ∃ Y : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E),
        (∀ i j, Y i j ∈ N) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ r)
    (T : H →L[ℂ] H) (hT : T ∈ unitBall (F.amplifiedAlgebra M)) :
    ∃ S ∈ unitBall (F.amplifiedAlgebra N), ‖T - S‖ ≤ r := by
  have hex (n : ℕ) := hnear n (F.finiteCompression n T)
    (fun i j => (F.mem_amplifiedAlgebra_iff M T).mp hT.1 i j)
    ((F.norm_finiteCompression_le n T).trans hT.2)
  choose Y hYN hYn hclose using hex
  let a (n : ℕ) := F.finiteBlock (Y n)
  have ha (n : ℕ) : a n ∈ F.amplifiedAlgebra N :=
    F.finiteBlock_mem_amplifiedAlgebra N (Y n) (hYN n)
  have han (n : ℕ) : ‖a n‖ ≤ 1 := (F.norm_finiteBlock (Y n)).le.trans (hYn n)
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨S, hSn, hlim⟩ := Generator.Tracial.exists_weak_operator_ultralimit ω a 1
    zero_le_one han
  have hSN : S ∈ F.amplifiedAlgebra N :=
    Generator.Tracial.weak_operator_limit_mem (F.amplifiedAlgebra N)
      (fun n => ⟨a n, ha n⟩) S hlim
  refine ⟨S, ⟨hSN, hSn⟩, ?_⟩
  let D (n : ℕ) := F.finiteBlock (F.finiteCompression n T) - a n
  have hDn (n : ℕ) : ‖D n‖ ≤ r := by
    have he : D n = F.finiteBlock (F.finiteCompression n T - Y n) := by
      exact (map_sub (F.finiteBlockHom n) _ _).symm
    rw [he, F.norm_finiteBlock]
    exact hclose n
  apply norm_le_of_weak_limit (l := (ω : Filter ℕ)) D (T - S) hr hDn
  intro x y
  have hleft := (F.finiteBlock_compression_tendsto T x y).mono_left hω
  simpa only [D, sub_apply, inner_sub_right] using hleft.sub (hlim x y)

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CanonicalAmplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.rescaledGraphSubspace_complete _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial transport and the canonical infinite amplification

Transport into the initial coordinate preserves the unit balls and their
Hausdorff distance. The abstract diagonal action obtained from the matrix
units is exactly the coordinatewise action on the Hilbert direct sum.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem norm_spatialConjugate (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    ‖e.conjStarAlgEquiv T‖ = ‖T‖ :=
  NonUnitalStarAlgHom.norm_map e.conjStarAlgEquiv e.conjStarAlgEquiv.injective T

theorem unitBall_spatialTransportAlgebra (e : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H) :
    unitBall (spatialTransportAlgebra e M) = e.conjStarAlgEquiv '' unitBall M := by
  ext T
  constructor
  · rintro ⟨⟨S, hS, rfl⟩, hn⟩
    change ‖e.conjStarAlgEquiv S‖ ≤ 1 at hn
    exact ⟨S, ⟨hS, by simpa only [norm_spatialConjugate] using hn⟩, rfl⟩
  · rintro ⟨S, ⟨hS, hn⟩, rfl⟩
    exact ⟨⟨S, hS, rfl⟩, by simpa only [norm_spatialConjugate] using hn⟩

/-- Hilbert-space transport does not change the ordinary operator gap. -/
theorem kkDistance_spatialTransportAlgebra (e : H ≃ₗᵢ[ℂ] K)
    (M N : VonNeumannAlgebra H) :
    kkDistance (spatialTransportAlgebra e M) (spatialTransportAlgebra e N) =
      kkDistance M N := by
  unfold kkDistance
  rw [unitBall_spatialTransportAlgebra, unitBall_spatialTransportAlgebra]
  exact Metric.hausdorffDist_image
    (NonUnitalStarAlgHom.isometry e.conjStarAlgEquiv e.conjStarAlgEquiv.injective)

variable (H)

theorem canonicalMatrixCorner_inflate (T : H →L[ℂ] H) :
    (canonicalMatrixCorner H).inflateHom ((canonicalInitialEquiv H).conjStarAlgEquiv T) =
      l2Diagonal T := by
  apply (canonicalMatrixCorner H).ext_on_columns
  intro i x
  obtain ⟨y, rfl⟩ := (canonicalInitialEquiv H).surjective x
  rw [(canonicalMatrixCorner H).inflateHom_column]
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply, canonicalMatrixCorner_column, l2Diagonal_single]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularTensorGap
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Complete matrix bounds control the regular tensor gap

The scalar Hilbert coordinates identify the actual regular tensor algebra
with the canonical countable amplification. Uniform finite-matrix
approximation, or actual common countable matrix units, therefore bounds
its gap. No ordinary-gap amplification principle is assumed.
-/

namespace KadisonKastler

open MeasureTheory
open scoped Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem spatialTransportAlgebra_commutant (e : H ≃ₗᵢ[ℂ] K)
    (M : VonNeumannAlgebra H) :
    (spatialTransportAlgebra e M).commutant = spatialTransportAlgebra e M.commutant := by
  apply SetLike.coe_injective
  rw [VonNeumannAlgebra.coe_commutant]
  change Set.centralizer (e.conjStarAlgEquiv '' (M : Set (H →L[ℂ] H))) =
    e.conjStarAlgEquiv '' (M.commutant : Set (H →L[ℂ] H))
  rw [VonNeumannAlgebra.coe_commutant]
  exact centralizer_image_spatial e _

theorem mem_canonicalAmplifiedAlgebra_iff (M : VonNeumannAlgebra H)
    (T : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) :
    T ∈ canonicalAmplifiedAlgebra H M ↔
      ∀ S ∈ M.commutant, l2Diagonal S * T = T * l2Diagonal S := by
  change T ∈ (canonicalMatrixCorner H).amplifiedAlgebra (canonicalCornerAlgebra H M) ↔ _
  rw [(canonicalMatrixCorner H).mem_amplifiedAlgebra_iff_commute]
  change (∀ S ∈ (spatialTransportAlgebra (canonicalInitialEquiv H) M).commutant,
    Commute ((canonicalMatrixCorner H).inflateHom S) T) ↔ _
  rw [spatialTransportAlgebra_commutant]
  constructor
  · intro h S hS
    have hh := h ((canonicalInitialEquiv H).conjStarAlgEquiv S) ⟨S, hS, rfl⟩
    simpa only [canonicalMatrixCorner_inflate] using hh.eq
  · rintro h S ⟨R, hR, rfl⟩
    change (canonicalMatrixCorner H).inflateHom ((canonicalInitialEquiv H).conjStarAlgEquiv R) * T =
      T * (canonicalMatrixCorner H).inflateHom ((canonicalInitialEquiv H).conjStarAlgEquiv R)
    simpa only [canonicalMatrixCorner_inflate] using h R hR

/-- The actual regular tensor algebra in scalar Hilbert coordinates. -/
theorem spatialTransport_regularTensorAlgebra (M : VonNeumannAlgebra H) :
    spatialTransportAlgebra (regularHilbertCoordinates (H := H) regularScalarBasis)
      (regularTensorAlgebra M) = canonicalAmplifiedAlgebra H M := by
  let e := regularHilbertCoordinates (H := H) regularScalarBasis
  have hc (S : H →L[ℂ] H) : e.conjStarAlgEquiv
      (regularConstantHom (volume : Measure ℝ) S) = l2Diagonal S :=
    regularHilbertCoordinates_constant regularScalarBasis S
  ext T
  rw [mem_spatialTransportAlgebra, mem_regularTensorAlgebra_iff,
    mem_canonicalAmplifiedAlgebra_iff]
  constructor
  · intro h S hS
    have he := congrArg e.conjStarAlgEquiv (h S hS)
    rw [map_mul, map_mul] at he
    change e.conjStarAlgEquiv ((regularConstantHom volume) S) *
        e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm T) =
      e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm T) *
        e.conjStarAlgEquiv ((regularConstantHom volume) S) at he
    rwa [hc, e.conjStarAlgEquiv.apply_symm_apply] at he
  · intro h S hS
    apply e.conjStarAlgEquiv.injective
    rw [map_mul, map_mul]
    change e.conjStarAlgEquiv ((regularConstantHom volume) S) *
        e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm T) =
      e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm T) *
        e.conjStarAlgEquiv ((regularConstantHom volume) S)
    rw [hc, e.conjStarAlgEquiv.apply_symm_apply]
    exact h S hS

/-- The regular tensor gap is exactly the canonical amplification gap. -/
theorem kkDistance_regularTensorAlgebra (M N : VonNeumannAlgebra H) :
    kkDistance (regularTensorAlgebra M) (regularTensorAlgebra N) =
      kkDistance (canonicalAmplifiedAlgebra H M) (canonicalAmplifiedAlgebra H N) := by
  rw [← spatialTransport_regularTensorAlgebra M, ← spatialTransport_regularTensorAlgebra N]
  exact (kkDistance_spatialTransportAlgebra
    (regularHilbertCoordinates (H := H) regularScalarBasis) _ _).symm

attribute [local instance] OAI.KadisonKastler.regularTensorGapOrder
attribute [local instance] OAI.KadisonKastler.regularTensorGapStarOrder
/-- Finite-matrix approximation transports across an actual Hilbert isometry. -/
theorem matrixApprox_spatialTransport (e : H ≃ₗᵢ[ℂ] K)
    (M N : VonNeumannAlgebra H) {r : ℝ}
    (hnear : ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)),
      (∀ i j, X i j ∈ M) → ‖X‖ ≤ 1 →
      ∃ Y : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H),
        (∀ i j, Y i j ∈ N) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ r)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K))
    (hX : ∀ i j, X i j ∈ spatialTransportAlgebra e M) (hn : ‖X‖ ≤ 1) :
    ∃ Y : CStarMatrix (Fin n) (Fin n) (K →L[ℂ] K),
      (∀ i j, Y i j ∈ spatialTransportAlgebra e N) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ r := by
  let φ := e.conjStarAlgEquiv.toStarAlgHom
  let ψ := e.conjStarAlgEquiv.symm.toStarAlgHom
  let X₀ := CStarMatrix.mapₗ ψ.toAlgHom.toLinearMap X
  have hX₀ : ∀ i j, X₀ i j ∈ M := fun i j =>
    (mem_spatialTransportAlgebra e M (X i j)).mp (hX i j)
  have hX₀n : ‖X₀‖ ≤ 1 :=
    (injective_starAlgHom_matrix_norm ψ e.conjStarAlgEquiv.symm.injective X).le.trans hn
  obtain ⟨Y₀, hY₀, hY₀n, hclose⟩ := hnear n X₀ hX₀ hX₀n
  refine ⟨CStarMatrix.mapₗ φ.toAlgHom.toLinearMap Y₀, ?_, ?_, ?_⟩
  · intro i j
    exact ⟨Y₀ i j, hY₀ i j, rfl⟩
  · exact (injective_starAlgHom_matrix_norm φ e.conjStarAlgEquiv.injective Y₀).le.trans hY₀n
  · have he : X = CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X₀ := by
      apply Matrix.ext
      intro i j
      change X i j = e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm (X i j))
      exact (e.conjStarAlgEquiv.apply_symm_apply (X i j)).symm
    rw [he, ← map_sub]
    exact (injective_starAlgHom_matrix_norm φ e.conjStarAlgEquiv.injective (X₀ - Y₀)).le.trans
      hclose

/-- Two-sided complete matrix approximation controls the regular tensor gap. -/
theorem kkDistance_regularTensorAlgebra_le_of_matrix_approx
    (M N : VonNeumannAlgebra H) {r : ℝ} (hr : 0 ≤ r)
    (hMN : ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)),
      (∀ i j, X i j ∈ M) → ‖X‖ ≤ 1 →
      ∃ Y : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H),
        (∀ i j, Y i j ∈ N) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ r)
    (hNM : ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)),
      (∀ i j, X i j ∈ N) → ‖X‖ ≤ 1 →
      ∃ Y : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H),
        (∀ i j, Y i j ∈ M) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ r) :
    kkDistance (regularTensorAlgebra M) (regularTensorAlgebra N) ≤ r := by
  rw [kkDistance_regularTensorAlgebra]
  apply Metric.hausdorffDist_le_of_mem_dist hr
  · intro T hT
    obtain ⟨S, hS, hn⟩ := (canonicalMatrixCorner H).exists_amplified_approx_of_matrix_approx
      (canonicalCornerAlgebra H M) (canonicalCornerAlgebra H N) hr
      (matrixApprox_spatialTransport (canonicalInitialEquiv H) M N hMN) T hT
    exact ⟨S, hS, by simpa only [dist_eq_norm] using hn⟩
  · intro T hT
    obtain ⟨S, hS, hn⟩ := (canonicalMatrixCorner H).exists_amplified_approx_of_matrix_approx
      (canonicalCornerAlgebra H N) (canonicalCornerAlgebra H M) hr
      (matrixApprox_spatialTransport (canonicalInitialEquiv H) N M hNM) T hT
    exact ⟨S, hS, by simpa only [dist_eq_norm] using hn⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixNearInclusion
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Matrix unit-ball proximity and graph row estimates

The cb distance supplies a separate approximant at each matrix level.
No linear selection of those approximants is assumed.
-/

namespace KadisonKastler

open scoped WithCStarModule InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace MatrixNearInclusion

variable {M N : VonNeumannAlgebra H} {γ η : ℝ}

attribute [local instance] OAI.KadisonKastler.MatrixNearInclusion.matrixNearStarOrder
/-- Matrix proximity in both directions controls the regular tensor product. -/
theorem regularTensor_gap_oai (hMN : MatrixNearInclusion M N γ)
    (hNM : MatrixNearInclusion N M γ) (hγ : 0 ≤ γ) :
    kkDistance (regularTensorAlgebra M) (regularTensorAlgebra N) ≤ γ :=
  kkDistance_regularTensorAlgebra_le_of_matrix_approx M N hγ hMN hNM

end MatrixNearInclusion

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.MatrixNearInclusion.regularTensor_gap_oai.{u_1} := @OAI.KadisonKastler.MatrixNearInclusion.regularTensor_gap_oai.{u_1}
