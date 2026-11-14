-- Prove2me | solution 1 for OAI.KadisonKastler.state_bicentralizer_scalar_of_modular_coisometries
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T19:08:55.641523+00:00
-- url     : https://prove2.me/submissions/2508137f-7fe9-4ac5-a7ee-426a04255e09

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
import Definitions.Def_Q260K036
import Definitions.Def_Q260K037
import Theorems.Thm_OAI_KadisonKastler_exists_uniform_projection_gap

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralDefectStateBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vector centrality controls the predual state commutator -/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem vectorStateCommutator_defect_identity
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (a b : Algebra M) :
    vectorStateCommutator ξ a b =
      inner ℂ (centralVectorDefect J ξ (star a).val) (b.val ξ) -
        inner ℂ ξ (b.val (centralVectorDefect J ξ a.val)) := by
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp (hright (star a)) b.val b.property
  have hs : (conjugationOperator J a.val).adjoint = conjugationOperator J (star a).val :=
    (conjugationOperator_star J hJ a.val).symm
  have hm : inner ℂ (conjugationOperator J a.val ξ) (b.val ξ) =
      inner ℂ ξ (b.val (conjugationOperator J (star a).val ξ)) := by
    rw [← ContinuousLinearMap.adjoint_inner_right,hs]
    exact congrArg (inner ℂ ξ) (congrArg (fun T : H →L[ℂ] H => T ξ) hc.symm)
  have ha : inner ℂ (star a.val ξ) (b.val ξ) = inner ℂ ξ (a.val (b.val ξ)) := by
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
  simp only [StarMemClass.coe_star] at hm
  change inner ℂ ξ (a.val (b.val ξ) - b.val (a.val ξ)) = _
  simp only [centralVectorDefect_apply,StarMemClass.coe_star,star_star,
    map_sub,inner_sub_left,inner_sub_right]
  rw [ha,hm]
  abel

theorem vectorStateCommutator_norm_le
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ = ξ) (a : Algebra M) :
    ‖vectorStateCommutator ξ a‖ ≤ 2 * ‖ξ‖ * ‖centralVectorDefect J ξ a.val‖ := by
  apply (vectorStateCommutator ξ a).opNorm_le_bound
    (M := 2 * ‖ξ‖ * ‖centralVectorDefect J ξ a.val‖) (by positivity)
  intro b
  rw [vectorStateCommutator_defect_identity J hJ hright]
  calc
    _ ≤ ‖inner ℂ (centralVectorDefect J ξ (star a).val) (b.val ξ)‖ +
        ‖inner ℂ ξ (b.val (centralVectorDefect J ξ a.val))‖ := norm_sub_le _ _
    _ ≤ ‖centralVectorDefect J ξ (star a).val‖ * ‖b.val ξ‖ +
        ‖ξ‖ * ‖b.val (centralVectorDefect J ξ a.val)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖centralVectorDefect J ξ (star a).val‖ * (‖b.val‖ * ‖ξ‖) +
        ‖ξ‖ * (‖b.val‖ * ‖centralVectorDefect J ξ a.val‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (b.val.le_opNorm ξ) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (b.val.le_opNorm _) (norm_nonneg _))
    _ = _ := by
      rw [StarMemClass.coe_star,centralVectorDefect_star_norm J hJ ξ hξ]
      change _ = _ * ‖b.val‖
      ring

theorem AsymptoticallyCentral.state_commutator
    {J : H ≃ₗᵢ⋆[ℂ] H} (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    {ξ : H} (hξ : J ξ = ξ) {x : BoundedSequence (Algebra M)}
    (hx : AsymptoticallyCentral J ξ x) :
    Tendsto (fun n => ‖vectorStateCommutator ξ (x n)‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => vectorStateCommutator_norm_le J hJ hright ξ hξ (x n))
  simpa only [mul_zero] using hx.const_mul (2 * ‖ξ‖)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VectorBicentralizerTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unitary tests for the vector form of the bicentralizer

The closed asymptotic sequence algebra is a C-star algebra. Its four-unitary
decomposition shows that testing all its bounded sequences is equivalent
to testing its unitaries. This does not assert triviality of the bicentralizer.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
  (ξ : H) (hξ : J ξ = ξ)

theorem vectorBicentralizerMember_iff_unitary (a : Algebra M) :
    vectorBicentralizerMember J ξ a ↔
      ∀ u : unitary (centralSequenceAlgebra J hJ hright ξ hξ), ∀ η : H,
        Tendsto (fun n => (a*(u.val.val n)-(u.val.val n)*a).val η) atTop (𝓝 0) := by
  constructor
  · intro h u η
    exact h u.val.val u.val.property η
  · intro h x hx η
    let y : centralSequenceAlgebra J hJ hright ξ hξ := ⟨x,hx⟩
    obtain ⟨u,c,hy,_⟩ := CStarAlgebra.exists_sum_four_unitary y
    let T := commutatorSequenceEvaluation J hJ hright ξ hξ a η
    have he (n : ℕ) : T n y = ∑ i : Fin 4, c i • T n (u i).val := by
      rw [hy,map_sum]
      simp only [map_smul]
    have ht (i : Fin 4) : Tendsto (fun n => c i • T n (u i).val) atTop (𝓝 0) := by
      have hi : Tendsto (fun n => T n (u i).val) atTop (𝓝 0) := h (u i) η
      simpa only [smul_zero] using hi.const_smul (c i)
    have hall := tendsto_finsetSum Finset.univ (fun i _ => ht i)
    change Tendsto (fun n => T n y) atTop (𝓝 0)
    simpa only [← he,Finset.sum_const_zero] using hall

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VectorBicentralizerLocal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.faithfulCyclicSpace_nontrivial _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.instNontrivialSubtypePreLpPointedPowerConfigurationComplexMemAddSubgroupPointedPowerHilbert _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform local tests for vector bicentralizers

The sequential definition is equivalent to a uniform estimate on the
unit ball at each vector. The forward implication constructs an actual
bounded counterexample sequence; the reverse uses the proved unitary tests.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
  (ξ : H) (hξ : J ξ = ξ)

include hJ hright hξ in
theorem vectorBicentralizerMember_iff_local (a : Algebra M) :
    vectorBicentralizerMember J ξ a ↔
      ∀ η : H, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ b : Algebra M, ‖b‖ ≤ 1 → ‖centralVectorDefect J ξ b.val‖ < δ →
          ‖(a*b-b*a).val η‖ < ε := by
  constructor
  · intro ha η ε hε
    by_contra h
    push Not at h
    choose b hb using fun n : ℕ => h (1 / ((n : ℝ)+1)) (by positivity)
    let x : BoundedSequence (Algebra M) :=
      BoundedContinuousFunction.ofNormedAddCommGroupDiscrete b 1 (fun n => (hb n).1)
    have hx : AsymptoticallyCentral J ξ x := by
      apply squeeze_zero (fun _ => norm_nonneg _)
        (fun n => (hb n).2.1.le)
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have ht : Tendsto (fun n => ‖(a*b n-b n*a).val η‖) atTop (𝓝 0) := by
      have ht := (ha x hx η).norm
      change Tendsto (fun n => ‖(a*b n-b n*a).val η‖) atTop (𝓝 ‖(0 : H)‖) at ht
      simpa only [norm_zero] using ht
    obtain ⟨n,hn⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
    exact (not_lt_of_ge (hb n).2.2) (hn n le_rfl)
  · intro ha
    let : Nontrivial (centralSequenceAlgebra J hJ hright ξ hξ) := by
      refine ⟨⟨0,1,?_⟩⟩
      intro h
      have he := congrArg (fun z : centralSequenceAlgebra J hJ hright ξ hξ => z.val 0) h
      exact zero_ne_one (he : (0 : Algebra M) = 1)
    apply (vectorBicentralizerMember_iff_unitary J hJ hright ξ hξ a).mpr
    intro u η
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ,hδ,hb⟩ := ha η ε hε
    have hx : Tendsto (fun n => ‖centralVectorDefect J ξ (u.val.val n).val‖)
        atTop (𝓝 0) := u.val.property
    filter_upwards [hx.eventually (gt_mem_nhds hδ)] with n hn
    have hbound : ‖u.val.val n‖ ≤ 1 := by
      calc
        _ ≤ ‖u.val.val‖ := u.val.val.norm_coe_le_norm n
        _ = ‖u.val‖ := rfl
        _ = 1 := CStarRing.norm_coe_unitary u
    simpa only [dist_zero_right] using hb (u.val.val n) hbound hn

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionCentralSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vectors continuous for projection centrality -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem projectionVectorDefect_eq (J : H ≃ₗᵢ⋆[ℂ] H) (p : AlgebraProjection M) (x : H) :
    projectionVectorDefect J p x=centralVectorDefect J x p.val.val := by
  rw [centralVectorDefect_apply]
  have hs : star p.val.val=p.val.val := congrArg Subtype.val p.property.isSelfAdjoint.star_eq
  rw [hs]
  rfl

theorem reference_mem_projectionCentralSpace (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) :
    ξ ∈ projectionCentralSpace (M := M) J ξ :=
  fun ε hε => ⟨ε,hε,fun _ h => h⟩

theorem projectionVectorDefect_conjugate (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (p : AlgebraProjection M) (x : H) :
    projectionVectorDefect J p (J x) = -J (projectionVectorDefect J p x) := by
  change p.val.val (J x)-J (p.val.val (J (J x))) =
    -J (p.val.val x-J (p.val.val (J x)))
  rw [hJ,map_sub,hJ]
  abel

theorem conjugate_mem_projectionCentralSpace (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (ξ : H) {η : H}
    (hη : η ∈ projectionCentralSpace (M := M) J ξ) :
    J η ∈ projectionCentralSpace (M := M) J ξ := by
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := hη ε hε
  refine ⟨δ,hδ,fun p hp => ?_⟩
  rw [projectionVectorDefect_conjugate J hJ,norm_neg,J.norm_map]
  exact hd p hp

variable [Nontrivial H]

theorem bicentralizer_vector_mem_projectionCentralSpace
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ=ξ) (a : Algebra M) (ha : vectorBicentralizerMember J ξ a) :
    a.val ξ ∈ projectionCentralSpace (M := M) J ξ := by
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := (vectorBicentralizerMember_iff_local J hJ hright ξ hξ a).mp ha
    ξ (ε/2) (half_pos hε)
  refine ⟨min δ (ε/(2*(‖a‖+1))),lt_min hδ (by positivity),?_⟩
  intro p hp
  have href : ‖centralVectorDefect J ξ p.val.val‖<δ := by
    rw [← projectionVectorDefect_eq]
    exact hp.trans_le (min_le_left _ _)
  have hc := hd p.val (p.property.norm_le _) href
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) a.val a.property
  have he : projectionVectorDefect J p (a.val ξ)=
      a.val (projectionVectorDefect J p ξ)-(a*p.val-p.val*a).val ξ := by
    change p.val.val (a.val ξ)-conjugationOperator J p.val.val (a.val ξ)=
      a.val (p.val.val ξ-conjugationOperator J p.val.val ξ)-
        (a.val (p.val.val ξ)-p.val.val (a.val ξ))
    have hh := congrArg (fun T : H →L[ℂ] H => T ξ) hcomm
    change a.val (conjugationOperator J p.val.val ξ)=conjugationOperator J p.val.val (a.val ξ) at hh
    rw [map_sub,hh]
    abel
  rw [he]
  apply (norm_sub_le _ _).trans_lt
  have hs : ‖a.val (projectionVectorDefect J p ξ)‖<ε/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*(‖a‖+1))).mp
      (hp.trans_le (min_le_right _ _))
    have hb := a.val.le_opNorm (projectionVectorDefect J p ξ)
    change ‖a.val (projectionVectorDefect J p ξ)‖≤‖a‖*‖projectionVectorDefect J p ξ‖ at hb
    nlinarith [norm_nonneg (projectionVectorDefect J p ξ)]
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionCentralScalar
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Projection centrality forces scalar vectors -/

namespace KadisonKastler

open Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
theorem conjugation_stable_submodule_scalar
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1) (V : Submodule ℂ H) (hξV : ξ∈V)
    (hJV : ∀ x∈V, J x∈V)
    (hzero : ∀ x∈V, J x=x → inner ℂ ξ x=0 → x=0) :
    ∀ η∈V, ∃ z : ℂ, η=z • ξ := by
  intro η hη
  let z := inner ℂ ξ η
  let v := η-z • ξ
  have hv : v∈V := V.sub_mem hη (V.smul_mem z hξV)
  have horth : inner ℂ ξ v=0 := by
    simp [v,z,inner_self_eq_norm_sq_to_K,huξ]
  have hjorth : inner ℂ ξ (J v)=0 := by
    have he := conjugateIsometry_inner J ξ v
    rw [hξ,horth,star_zero] at he
    exact he
  have hr : v+J v=0 := hzero _ (V.add_mem hv (hJV v hv))
    (by rw [map_add,hJ,add_comm]) (by rw [inner_add_right,horth,hjorth,add_zero])
  have hi : Complex.I • (v-J v)=0 := hzero _ (V.smul_mem _ (V.sub_mem hv (hJV v hv)))
    (by
      rw [J.map_smulₛₗ,map_sub,hJ]
      simp only [Complex.conj_I]
      module)
    (by rw [inner_smul_right,inner_sub_right,horth,hjorth,sub_self,mul_zero])
  have hs : v-J v=0 := (smul_eq_zero.mp hi).resolve_left Complex.I_ne_zero
  have hv0 : v=0 := by
    have hvj := sub_eq_zero.mp hs
    rw [← hvj] at hr
    have hs2 : (2:ℂ) • v=0 := by simpa only [two_smul] using hr
    exact (smul_eq_zero.mp hs2).resolve_left (by norm_num)
  refine ⟨z,?_⟩
  exact sub_eq_zero.mp hv0

variable [TopologicalSpace.SeparableSpace H]

attribute [local instance] OAI.KadisonKastler.projectionScalarRealInner
theorem projectionCentral_symmetric_orthogonal_eq_zero
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (η : H) (hc : η∈projectionCentralSpace (M := M) J ξ)
    (hη : J η=η) (horth : inner ℂ ξ η=0) : η=0 := by
  by_contra hne
  let v := normalize η
  have hv : v∈projectionCentralSpace (M := M) J ξ := by
    change ((‖η‖⁻¹ : ℝ) : ℂ) • η ∈ projectionCentralSpace (M := M) J ξ
    exact (projectionCentralSpace J ξ).smul_mem _ hc
  have hjv : J v=v := by
    change J (((‖η‖⁻¹ : ℝ) : ℂ) • η)=((‖η‖⁻¹ : ℝ) : ℂ) • η
    rw [J.map_smulₛₗ,Complex.conj_ofReal,hη]
  have hov : inner ℂ ξ v=0 := by
    change inner ℂ ξ (((‖η‖⁻¹ : ℝ) : ℂ) • η)=0
    rw [inner_smul_right,horth,mul_zero]
  obtain ⟨δ,hδ,hd⟩ := hv (1/4096) (by norm_num)
  obtain ⟨p,hpξ,hpη⟩ := exists_uniform_projection_gap J hJ hright hleft ξ hξ huξ hsep hpos
    hIII hremote v hjv (norm_normalize hne) hov (δ^2) (sq_pos_of_pos hδ)
  have hp : ‖projectionVectorDefect J p ξ‖<δ := by
    rw [projectionVectorDefect_eq]
    nlinarith [norm_nonneg (centralVectorDefect J ξ p.val.val)]
  have hvp := hd p hp
  rw [projectionVectorDefect_eq] at hvp
  nlinarith [norm_nonneg (centralVectorDefect J v p.val.val)]

theorem projectionCentralSpace_scalar
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (η : H) (hη : η∈projectionCentralSpace (M := M) J ξ) :
    ∃ z : ℂ, η=z • ξ :=
  conjugation_stable_submodule_scalar J hJ ξ hξ huξ (projectionCentralSpace J ξ)
    (reference_mem_projectionCentralSpace J ξ)
    (fun _ hx => conjugate_mem_projectionCentralSpace J hJ ξ hx)
    (fun x hx hj ho => projectionCentral_symmetric_orthogonal_eq_zero J hJ hright hleft
      ξ hξ huξ hsep hpos hIII hremote x hx hj ho) η hη

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularCoisometryBicentralizer
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar bicentralizers from the constructed modular coisometries

Only the fixed reference state is used. No state homogeneity, absorption
classification, or scalar-bicentralizer premise enters this implication.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.coisometryBicentralizerRealInner
theorem vector_bicentralizer_scalar_of_modular_coisometries
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (a : Algebra M) (ha : vectorBicentralizerMember J ξ a) :
    ∃ z : ℂ, a=z • 1 := by
  obtain ⟨z,hz⟩ := projectionCentralSpace_scalar J hJ hright hleft ξ hξ huξ hsep hpos
    hIII hremote (a.val ξ) (bicentralizer_vector_mem_projectionCentralSpace J hJ hright ξ hξ a ha)
  refine ⟨z,hsep ?_⟩
  change a.val ξ=(z • (1 : Algebra M)).val ξ
  simpa only [SetLike.val_smul,OneMemClass.coe_one,smul_apply,one_apply_eq_self] using hz

theorem state_bicentralizer_scalar_of_modular_coisometries_oai
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (a : Algebra M) (ha : stateBicentralizerMember ξ a) :
    ∃ z : ℂ, a=z • 1 := by
  apply vector_bicentralizer_scalar_of_modular_coisometries J hJ hright hleft ξ hξ huξ hsep
    hpos hIII hremote a
  intro x hx
  exact ha x (hx.state_commutator hJ hright hξ)

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.state_bicentralizer_scalar_of_modular_coisometries_oai.{u_1} := @OAI.KadisonKastler.state_bicentralizer_scalar_of_modular_coisometries_oai.{u_1}
