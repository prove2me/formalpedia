-- Prove2me | solution 1 for OAI.KadisonKastler.publishedCentralPairDecomposition
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T19:08:50.693941+00:00
-- url     : https://prove2.me/submissions/00e37614-fe14-45c1-bc12-0b6b2df92832
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
import Mathlib.Analysis.CStarAlgebra.Unitization
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
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
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
import Mathlib.Analysis.Normed.Operator.LinearIsometry
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
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
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
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.WithDensityFinite
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
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
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
import Definitions.Def_Q260K028
import Definitions.Def_Q260K029
import Theorems.Thm_OAI_KadisonKastler_blockAlgebraDecomposition_coordinate_transport
import Theorems.Thm_OAI_KadisonKastler_commonRank_algebra_decomposition
import Theorems.Thm_OAI_KadisonKastler_commonRank_factor_fibers
import Theorems.Thm_OAI_KadisonKastler_exists_centralPairCommonSource
import Theorems.Thm_OAI_KadisonKastler_liftedRankRepresentation_measurable
import Theorems.Thm_OAI_KadisonKastler_liftedRank_field_decomposition
import Theorems.Thm_OAI_KadisonKastler_liftedRank_scalarCenter
import Theorems.Thm_OAI_KadisonKastler_representationVonNeumannAlgebra_eq_generated
import Theorems.Thm_OAI_KadisonKastler_representation_joint_eq_center_commutant
import Theorems.Thm_OAI_KadisonKastler_sourceInclusion_comp
import Theorems.Thm_OAI_KadisonKastler_spatialTransportAlgebra_trans
import Theorems.Thm_OAI_KadisonSimilarity_exists_separable_central_source
import Theorems.Thm_OAI_KadisonSimilarity_subtype_star_range

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralPairFromRankModel
attribute [-instance] _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Packaging the constructed rank model as the exact central-pair data -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

universe u

variable {H Z : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [CommCStarAlgebra Z] [TopologicalSpace.SeparableSpace Z]
  {π : Z →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

theorem centralPairDecomposition_of_rankModel
    (M N : VonNeumannAlgebra H) (A B C S : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (A : Set (H →L[ℂ] H))] [IsClosed (B : Set (H →L[ℂ] H))]
    [IsClosed (C : Set (H →L[ℂ] H))] [IsClosed (S : Set (H →L[ℂ] H))]
    [TopologicalSpace.SeparableSpace S]
    (model : BorelCommonModel π D S.subtype)
    (hAC : A ≤ C) (hBC : B ≤ C) (hCS : C ≤ S)
    (Q R : ∀ n, VonNeumannAlgebra (Lp ℓ²(projectionDimensionIndex n, ℂ) 2
      (commonRankSourceMeasure model n)))
    (hQ : BlockAlgebraDecomposition Q (spatialTransportAlgebra (commonRankCoordinates model) M))
    (hR : BlockAlgebraDecomposition R (spatialTransportAlgebra (commonRankCoordinates model) N))
    (hQf : ∀ n, OperatorFieldDecomposition (commonRankSourceMeasure model n)
      (commonRankFiberAlgebra model (StarSubalgebra.inclusion (hAC.trans hCS)) n) (Q n))
    (hRf : ∀ n, OperatorFieldDecomposition (commonRankSourceMeasure model n)
      (commonRankFiberAlgebra model (StarSubalgebra.inclusion (hBC.trans hCS)) n) (R n))
    (hf : ∀ n, ∀ᵐ x ∂commonRankSourceMeasure model n,
      ScalarCenter (commonRankFiberAlgebra model (StarSubalgebra.inclusion (hAC.trans hCS)) n x) ∧
      ScalarCenter (commonRankFiberAlgebra model (StarSubalgebra.inclusion (hBC.trans hCS)) n x)) :
    Nonempty (CentralPairDecomposition M N A B C hAC hBC) := by
  refine ⟨{
    stratum := commonRankStratum model
    coordinates := liftedRankCoordinates model
    leftBlock := fun n => spatialTransportAlgebra (commonRankStratumEquiv model n) (Q n)
    rightBlock := fun n => spatialTransportAlgebra (commonRankStratumEquiv model n) (R n)
    leftBlocks := ?_
    rightBlocks := ?_
    representation := fun n x => (liftedRankRepresentation model n x).comp (StarSubalgebra.inclusion hCS)
    representation_measurable := ?_
    leftFields := ?_
    rightFields := ?_
    factors := ?_ }⟩
  · have h := blockAlgebraDecomposition_coordinate_transport (commonRankStratumEquiv model)
      Q (spatialTransportAlgebra (commonRankCoordinates model) M) hQ
    rw [spatialTransportAlgebra_trans] at h
    exact h
  · have h := blockAlgebraDecomposition_coordinate_transport (commonRankStratumEquiv model)
      R (spatialTransportAlgebra (commonRankCoordinates model) N) hR
    rw [spatialTransportAlgebra_trans] at h
    exact h
  · intro n c v
    exact liftedRankRepresentation_measurable model n (StarSubalgebra.inclusion hCS c) v
  · intro n
    have h := liftedRank_field_decomposition model (StarSubalgebra.inclusion (hAC.trans hCS))
      n (Q n) (hQf n)
    simpa only [sourceInclusion_comp] using h
  · intro n
    have h := liftedRank_field_decomposition model (StarSubalgebra.inclusion (hBC.trans hCS))
      n (R n) (hRf n)
    simpa only [sourceInclusion_comp] using h
  · intro n
    filter_upwards [hf n] with x hx
    constructor
    · simpa only [sourceInclusion_comp] using
        liftedRank_scalarCenter model (StarSubalgebra.inclusion (hAC.trans hCS)) n x hx.1
    · simpa only [sourceInclusion_comp] using
        liftedRank_scalarCenter model (StarSubalgebra.inclusion (hBC.trans hCS)) n x hx.2

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralPairConstruction
attribute [-instance] _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Construction of the common central decomposition

A common source, rank coordinates and bounded-field reconstruction
give the factor fibers of the central decomposition.
-/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped IsMulCommutative

noncomputable section

universe u

private theorem concreteCenter_eq (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    concreteCenter M = vonNeumannCenter M := by
  apply VonNeumannAlgebra.ext
  intro T
  rfl

private theorem commutant_le_centralCommutant {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    M.commutant.toStarSubalgebra ≤ (vonNeumannCenter M).commutant.toStarSubalgebra := by
  intro T hT
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro z hz
  exact VonNeumannAlgebra.mem_commutant_iff.mp hT z hz.1

theorem publishedCentralPairDecomposition_oai : PublishedCentralPairDecomposition.{u} := by
  intro H _ _ _ _ M N hcenter A B C hAc hBc hCc _hAs _hBs hCs hAg hBg hAC hBC hCcentral
  let : IsClosed (A : Set (H →L[ℂ] H)) := hAc
  let : IsClosed (B : Set (H →L[ℂ] H)) := hBc
  let : IsClosed (C : Set (H →L[ℂ] H)) := hCc
  obtain ⟨s⟩ := exists_centralPairCommonSource M N hcenter C hCs hCcentral
  let S := s.source
  let : IsClosed (S : Set (H →L[ℂ] H)) := s.source_closed
  let : TopologicalSpace.SeparableSpace S := s.source_separable
  let : IsClosed (s.leftComm : Set (H →L[ℂ] H)) := s.left_closed
  let : IsClosed (s.rightComm : Set (H →L[ℂ] H)) := s.right_closed
  obtain ⟨Z, hZc, hZs, hZcomm, hZM, hZgen⟩ := exists_separable_central_source M
  let : IsClosed (Z : Set (H →L[ℂ] H)) := hZc
  let : TopologicalSpace.SeparableSpace Z := hZs
  let : IsMulCommutative Z := hZcomm
  let π := Z.subtype
  let D := cyclicDecompositionData π.range
  have hπ : starSubalgebraCommutant π.range = (vonNeumannCenter M).commutant := by
    simpa only [π, subtype_star_range] using hZgen
  have hSN (b : S) (a : Z) : b.val * a.val = a.val * b.val := by
    have ha : a.val ∈ concreteCenter M := by
      rw [concreteCenter_eq H M]
      exact hZM a.property
    exact (VonNeumannAlgebra.mem_commutant_iff.mp (s.central b.property) a.val ha).symm
  let model := borelCommonModel π D S.subtype hSN
  have hAS : A ≤ S := hAC.trans s.original_le
  have hBS : B ≤ S := hBC.trans s.original_le
  let ιA := StarSubalgebra.inclusion hAS
  let ιB := StarSubalgebra.inclusion hBS
  let κM := StarSubalgebra.inclusion s.left_le
  let κN := StarSubalgebra.inclusion s.right_le
  have hAgen : representationVonNeumannAlgebra (S.subtype.comp ιA) = M := by
    change representationVonNeumannAlgebra A.subtype = M
    rw [representationVonNeumannAlgebra_eq_generated, subtype_star_range, hAg]
  have hBgen : representationVonNeumannAlgebra (S.subtype.comp ιB) = N := by
    change representationVonNeumannAlgebra B.subtype = N
    rw [representationVonNeumannAlgebra_eq_generated, subtype_star_range, hBg]
  have hLgen : representationVonNeumannAlgebra (S.subtype.comp κM) = M.commutant := by
    change (starSubalgebraCommutant s.leftComm.subtype.range).commutant = M.commutant
    rw [subtype_star_range]
    exact s.left_generates
  have hRgen : representationVonNeumannAlgebra (S.subtype.comp κN) = N.commutant := by
    change (starSubalgebraCommutant s.rightComm.subtype.range).commutant = N.commutant
    rw [subtype_star_range]
    exact s.right_generates
  have hAM : A ≤ M.toStarSubalgebra := by
    intro T hT
    rw [← hAg]
    exact subset_generatedVonNeumannAlgebra A hT
  have hBN : B ≤ N.toStarSubalgebra := by
    intro T hT
    rw [← hBg]
    exact subset_generatedVonNeumannAlgebra B hT
  have hAL (a : A) (c : s.leftComm) : a.val * c.val = c.val * a.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp (s.left_mem c.property) a.val (hAM a.property)
  have hBR (b : B) (c : s.rightComm) : b.val * c.val = c.val * b.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp (s.right_mem c.property) b.val (hBN b.property)
  have hMc : M.toStarSubalgebra ≤ (starSubalgebraCommutant π.range).toStarSubalgebra := by
    rw [hπ]
    exact le_center_commutant M
  have hM'c : M.commutant.toStarSubalgebra ≤ (starSubalgebraCommutant π.range).toStarSubalgebra := by
    rw [hπ]
    exact commutant_le_centralCommutant M
  have hcenters : vonNeumannCenter M = vonNeumannCenter N := by
    simpa only [concreteCenter_eq] using hcenter
  have hNc : N.toStarSubalgebra ≤ (starSubalgebraCommutant π.range).toStarSubalgebra := by
    rw [hπ, hcenters]
    exact le_center_commutant N
  have hN'c : N.commutant.toStarSubalgebra ≤ (starSubalgebraCommutant π.range).toStarSubalgebra := by
    rw [hπ, hcenters]
    exact commutant_le_centralCommutant N
  obtain ⟨Q, hQ, hQf⟩ := commonRank_algebra_decomposition model ιA κM M hAgen hLgen hMc hM'c
    (fun a c => Subtype.ext (hAL a c))
  obtain ⟨R, hR, hRf⟩ := commonRank_algebra_decomposition model ιB κN N hBgen hRgen hNc hN'c
    (fun b c => Subtype.ext (hBR b c))
  have hAj : representationVonNeumannAlgebra (jointCStarSource A s.leftComm).subtype =
      starSubalgebraCommutant π.range := by
    exact (representation_joint_eq_center_commutant M A s.leftComm hAg s.left_generates
      hAM s.left_mem).trans hπ.symm
  have hBj : representationVonNeumannAlgebra (jointCStarSource B s.rightComm).subtype =
      starSubalgebraCommutant π.range := by
    rw [hπ, hcenters]
    exact representation_joint_eq_center_commutant N B s.rightComm hBg s.right_generates
      hBN s.right_mem
  apply centralPairDecomposition_of_rankModel M N A B C S model hAC hBC s.original_le
    Q R hQ hR hQf hRf
  intro n
  have ha := commonRank_factor_fibers S model A s.leftComm hAS s.left_le hAL hAj n
  have hb := commonRank_factor_fibers S model B s.rightComm hBS s.right_le hBR hBj n
  filter_upwards [ha, hb] with x hx hy
  exact ⟨hx, hy⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.publishedCentralPairDecomposition_oai.{u} := @OAI.KadisonKastler.publishedCentralPairDecomposition_oai.{u}
