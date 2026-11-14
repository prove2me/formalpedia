-- Prove2me | solution 1 for OAI.KadisonKastler.exists_projection_gap_of_finite_pinching
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T14:31:46.557292+00:00
-- url     : https://prove2.me/submissions/7556aa61-1fc7-4b61-9cd4-e98d6c080280

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
import Definitions.Def_Q260K044
import Theorems.Thm_OAI_KadisonKastler_exists_partition_projection_gap
import Theorems.Thm_OAI_KadisonKastler_projectionFamilyPinching_insert

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularIsometryCorner
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Isometric coordinates in a two-sided modular corner

An algebra isometry induces an isometry on the Hilbert space by `v J v J`.
Projection sandwiches intertwine both left and right actions, preserving
the commutator norms used in projection refinement.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hJ in
theorem modularQuadratic_one : modularQuadratic (M := M) J 1=1 := by
  change (1 : H →L[ℂ] H)*conjugationOperator J 1=1
  rw [conjugationOperator_one J hJ,one_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFamilyCorner
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The remaining corner inside a family pinching

The quadratic remainder projection is contained in the simultaneous
commutation projection, including for infinite projection families.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem projectionFamily_left_annihilate (S : Set (AlgebraProjection M))
    (p : AlgebraProjection M) (hp : p∈S) : p.val.val*(projectionFamilyRemainder S).val.val=0 := by
  ext x
  exact (mem_projectionFamilyRemainderSpace S _).mp
    (Submodule.starProjection_apply_mem (projectionFamilyRemainderSpace S).toSubmodule x) p hp

theorem projectionFamily_right_annihilate (S : Set (AlgebraProjection M))
    (p : AlgebraProjection M) (hp : p∈S) : (projectionFamilyRemainder S).val.val*p.val.val=0 := by
  have he := congrArg star (projectionFamily_left_annihilate S p hp)
  have hs : star p.val.val=p.val.val := congrArg Subtype.val p.property.isSelfAdjoint.star_eq
  have hq : star (projectionFamilyRemainder S).val.val=(projectionFamilyRemainder S).val.val :=
    congrArg Subtype.val (projectionFamilyRemainder S).property.isSelfAdjoint.star_eq
  simpa only [star_mul,star_zero,hs,hq] using he

theorem projectionFamilyCommutationSpace_conjugate
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (S : Set (AlgebraProjection M)) {x : H}
    (hx : x ∈ projectionFamilyCommutationSpace J S) :
    J x ∈ projectionFamilyCommutationSpace J S := by
  rw [mem_projectionFamilyCommutationSpace] at hx ⊢
  intro p hp
  have he := congrArg J (hx p hp)
  change J (p.val.val x)=J (J (p.val.val (J x))) at he
  rw [hJ] at he
  change p.val.val (J x)=J (p.val.val (J (J x)))
  rw [hJ]
  exact he.symm

theorem projectionFamily_remainder_central
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (S : Set (AlgebraProjection M)) {x : H}
    (hx : x ∈ projectionFamilyCommutationSpace J S) :
    (projectionFamilyRemainder S).val.val x=
      conjugationOperator J (projectionFamilyRemainder S).val.val x := by
  let q := projectionFamilyRemainder S
  have haux (y : H) (hy : y ∈ projectionFamilyCommutationSpace J S) :
      conjugationOperator J q.val.val (q.val.val y)=q.val.val y := by
    have hmem : J (q.val.val y) ∈ projectionFamilyRemainderSpace S := by
      rw [mem_projectionFamilyRemainderSpace]
      intro p hp
      have hc := congrArg (fun T : H →L[ℂ] H => T y)
        (VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) q.val.val q.val.property)
      change q.val.val (conjugationOperator J p.val.val y)=
        conjugationOperator J p.val.val (q.val.val y) at hc
      have hyp := (mem_projectionFamilyCommutationSpace J S y).mp hy p hp
      have hz := congrArg (fun T : H →L[ℂ] H => T y) (projectionFamily_right_annihilate S p hp)
      change q.val.val (p.val.val y)=0 at hz
      calc
        p.val.val (J (q.val.val y)) = J (conjugationOperator J p.val.val (q.val.val y)) := by
          change _=J (J (p.val.val (J (q.val.val y))))
          rw [hJ]
        _ = J (q.val.val (conjugationOperator J p.val.val y)) := by rw [← hc]
        _ = 0 := by rw [← hyp,hz,map_zero]
    have hf : q.val.val (J (q.val.val y))=J (q.val.val y) :=
      Submodule.starProjection_eq_self_iff.mpr hmem
    change J (q.val.val (J (q.val.val y)))=q.val.val y
    rw [hf,hJ]
  have ha := haux x hx
  have hb := congrArg J (haux (J x) (projectionFamilyCommutationSpace_conjugate J hJ S hx))
  change J (J (q.val.val (J (q.val.val (J x)))))=J (q.val.val (J x)) at hb
  rw [hJ] at hb
  have hc := congrArg (fun T : H →L[ℂ] H => T x)
    (VonNeumannAlgebra.mem_commutant_iff.mp (hright q.val) q.val.val q.val.property)
  exact ha.symm.trans (hc.symm.trans hb)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFamilyInsert
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The remaining corner after one additional projection -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem mem_projectionFamilyRemainderSpace_insert (S : Set (AlgebraProjection M))
    (p : AlgebraProjection M) (x : H) :
    x ∈ projectionFamilyRemainderSpace (insert p S) ↔
      x ∈ projectionFamilyRemainderSpace S ∧ p.val.val x=0 := by
  simp only [mem_projectionFamilyRemainderSpace,Set.mem_insert_iff,forall_eq_or_imp]
  exact and_comm

theorem projectionFamilyRemainder_insert (S : Set (AlgebraProjection M))
    (p : AlgebraProjection M) (hpq : p≤projectionFamilyRemainder S) :
    (projectionFamilyRemainder (insert p S)).val=(projectionFamilyRemainder S).val-p.val := by
  let q := projectionFamilyRemainder S
  let r := AlgebraProjection.remainder p q hpq
  let q' := projectionFamilyRemainder (insert p S)
  have hrq : q.val.val*r.val.val=r.val.val :=
    congrArg Subtype.val (AlgebraProjection.remainder_le p q hpq)
  have hpr : p.val.val*r.val.val=0 :=
    congrArg Subtype.val (AlgebraProjection.remainder_orthogonal p q hpq)
  have hqr : q'.val.val*r.val.val=r.val.val := by
    ext x
    change (projectionFamilyRemainderSpace (insert p S)).toSubmodule.starProjection
      (r.val.val x)=r.val.val x
    apply Submodule.starProjection_eq_self_iff.mpr
    change r.val.val x ∈ projectionFamilyRemainderSpace (insert p S)
    rw [mem_projectionFamilyRemainderSpace_insert]
    constructor
    · have he := congrArg (fun T : H →L[ℂ] H => T x) hrq
      change q.val.val (r.val.val x)=r.val.val x at he
      rw [← he]
      exact Submodule.starProjection_apply_mem (projectionFamilyRemainderSpace S).toSubmodule _
    · exact congrArg (fun T : H →L[ℂ] H => T x) hpr
  have hrq' : r.val.val*q'.val.val=q'.val.val := by
    ext x
    have hx := (mem_projectionFamilyRemainderSpace_insert S p _).mp
      (Submodule.starProjection_apply_mem (projectionFamilyRemainderSpace (insert p S)).toSubmodule x)
    have he : q.val.val (q'.val.val x)=q'.val.val x :=
      Submodule.starProjection_eq_self_iff.mpr hx.1
    have hz : p.val.val (q'.val.val x)=0 := hx.2
    change q.val.val (q'.val.val x)-p.val.val (q'.val.val x)=q'.val.val x
    rw [he,hz,sub_zero]
  have hrq'' : r.val.val*q'.val.val=r.val.val := by
    have he := congrArg star hqr
    have hsr : star r.val.val=r.val.val := congrArg Subtype.val r.property.isSelfAdjoint.star_eq
    have hsq : star q'.val.val=q'.val.val := congrArg Subtype.val q'.property.isSelfAdjoint.star_eq
    simpa only [star_mul,hsr,hsq] using he
  exact Subtype.ext (hrq'.symm.trans hrq'')

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionFamilyMaximal
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Maximal admissible orthogonal projection families

Chain unions retain the two quantitative inequalities by strong convergence
of the constructed kernel projections.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem projectionFamilyRemainder_empty :
    (projectionFamilyRemainder (∅ : Set (AlgebraProjection M))).val=1 := by
  apply Subtype.ext
  ext x
  apply Submodule.starProjection_eq_self_iff.mpr
  change x ∈ projectionFamilyRemainderSpace (∅ : Set (AlgebraProjection M))
  rw [mem_projectionFamilyRemainderSpace]
  simp

theorem projectionFamilyPinching_empty (J : H ≃ₗᵢ⋆[ℂ] H) :
    projectionFamilyPinching J (∅ : Set (AlgebraProjection M))=1 := by
  ext x
  apply Submodule.starProjection_eq_self_iff.mpr
  change x ∈ projectionFamilyCommutationSpace J (∅ : Set (AlgebraProjection M))
  rw [mem_projectionFamilyCommutationSpace]
  simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteProjectionPartition
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Completing a finite orthogonal family to a partition of one -/

namespace KadisonKastler

open Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem projection_le_familyRemainder (S : Set (AlgebraProjection M))
    (p : AlgebraProjection M) (hp : ∀ q∈S, q.val*p.val=0) :
    p≤projectionFamilyRemainder S := by
  apply Subtype.ext
  ext x
  change (projectionFamilyRemainderSpace S).toSubmodule.starProjection (p.val.val x)=p.val.val x
  apply Submodule.starProjection_eq_self_iff.mpr
  change p.val.val x ∈ projectionFamilyRemainderSpace S
  rw [mem_projectionFamilyRemainderSpace]
  intro q hq
  exact congrArg (fun a : Algebra M => a.val x) (hp q hq)

theorem finite_family_partition_identities
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (F : Finset (AlgebraProjection M))
    (hF : (F : Set (AlgebraProjection M)).Pairwise (fun p q => p.val*q.val=0)) :
    (∑ p∈F, p.val)+(projectionFamilyRemainder (F : Set (AlgebraProjection M))).val=1 ∧
    projectionFamilyPinching J (F : Set (AlgebraProjection M))=
      (∑ p∈F, modularQuadratic J p.val)+
        modularQuadratic J (projectionFamilyRemainder (F : Set (AlgebraProjection M))).val := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.coe_empty,Finset.sum_empty,zero_add]
    rw [projectionFamilyRemainder_empty,projectionFamilyPinching_empty J,
      modularQuadratic_one J hJ]
    exact ⟨rfl,rfl⟩
  | @insert p F hp ih =>
    have hsub : (F : Set (AlgebraProjection M))⊆(↑(insert p F) : Set (AlgebraProjection M)) := by
      intro q hq
      exact Finset.mem_insert_of_mem hq
    obtain ⟨hs,hr⟩ := ih (hF.mono hsub)
    have hpq : p≤projectionFamilyRemainder (F : Set (AlgebraProjection M)) := by
      apply projection_le_familyRemainder
      intro q hq
      exact hF (hsub hq) (Finset.mem_insert_self p F) (by
        intro he
        subst q
        exact hp hq)
    have hrem := projectionFamilyRemainder_insert (F : Set (AlgebraProjection M)) p hpq
    have hpin := projectionFamilyPinching_insert J hJ hright (F : Set (AlgebraProjection M)) p hpq
    rw [Finset.coe_insert,Finset.sum_insert hp,Finset.sum_insert hp]
    constructor
    · rw [hrem]
      rw [← hs]
      abel
    · rw [hpin,projectionFamilySelectedPart,refinedCornerProjection,hr,hrem]
      abel

theorem finitePartitionProjection_sum
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (F : Finset (AlgebraProjection M))
    (hF : (F : Set (AlgebraProjection M)).Pairwise (fun p q => p.val*q.val=0)) :
    (∑ i, (finitePartitionProjection F i).val)=1 ∧
    (∑ i, modularQuadratic J (finitePartitionProjection F i).val)=
      projectionFamilyPinching J (F : Set (AlgebraProjection M)) := by
  classical
  obtain ⟨hs,hr⟩ := finite_family_partition_identities J hJ hright F hF
  simp only [Fintype.sum_option,finitePartitionProjection]
  rw [Finset.sum_coe_sort F (fun p => p.val),
    Finset.sum_coe_sort F (fun p => modularQuadratic J p.val)]
  exact ⟨(add_comm _ _).trans hs,(add_comm _ _).trans hr.symm⟩

theorem finitePartitionProjection_orthogonal (F : Finset (AlgebraProjection M))
    (hF : (F : Set (AlgebraProjection M)).Pairwise (fun p q => p.val*q.val=0)) :
    Pairwise (fun i j : Option F => (finitePartitionProjection F i).val*
      (finitePartitionProjection F j).val=0) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some p =>
      exact Subtype.ext (projectionFamily_right_annihilate _ p.val p.property)
  | some p =>
    cases j with
    | none => exact Subtype.ext (projectionFamily_left_annihilate _ p.val p.property)
    | some q =>
      exact hF p.property q.property (by
        intro he
        exact hij (congrArg (fun r : F => some r) (Subtype.ext he)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UniformProjectionGap
attribute [-instance] _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform projection witnesses from modular coisometries -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_projection_gap_of_finite_pinching_oai
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (T : Set (AlgebraProjection M)) (hT : T.Finite)
    (horth : T.Pairwise (fun p q => p.val*q.val=0)) (ξ η : H) :
    ∃ p : AlgebraProjection M,
      ‖centralVectorDefect J ξ p.val.val‖^2 ≤ ‖(1-projectionFamilyPinching J T) ξ‖^2 ∧
      (1/4:ℝ)*‖(1-projectionFamilyPinching J T) η‖^2 ≤
        ‖centralVectorDefect J η p.val.val‖^2 := by
  classical
  let F := hT.toFinset
  have he : (F : Set (AlgebraProjection M))=T := hT.coe_toFinset
  have hF : (F : Set (AlgebraProjection M)).Pairwise (fun p q => p.val*q.val=0) := he ▸ horth
  obtain ⟨hs,hr⟩ := finitePartitionProjection_sum J hJ hright F hF
  have hc : ∀ i x, (finitePartitionProjection F i).val.val (projectionFamilyPinching J T x)=
      conjugationOperator J (finitePartitionProjection F i).val.val (projectionFamilyPinching J T x) := by
    intro i x
    have hx : projectionFamilyPinching J T x ∈ projectionFamilyCommutationSpace J T :=
      Submodule.starProjection_apply_mem _ _
    cases i with
    | none =>
      change (projectionFamilyRemainder (F : Set (AlgebraProjection M))).val.val
        (projectionFamilyPinching J T x)=conjugationOperator J
          (projectionFamilyRemainder (F : Set (AlgebraProjection M))).val.val
          (projectionFamilyPinching J T x)
      rw [he]
      exact projectionFamily_remainder_central J hJ hright T hx
    | some p =>
      exact (mem_projectionFamilyCommutationSpace J T _).mp hx p.val (he ▸ p.property)
  rw [he] at hr
  exact exists_partition_projection_gap J hJ (finitePartitionProjection F)
    (finitePartitionProjection_orthogonal F hF) hs _ hr hc ξ η

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_projection_gap_of_finite_pinching_oai.{u_1} := @OAI.KadisonKastler.exists_projection_gap_of_finite_pinching_oai.{u_1}
