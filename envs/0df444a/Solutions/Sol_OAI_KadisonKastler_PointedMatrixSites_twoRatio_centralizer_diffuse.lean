-- Prove2me | solution 1 for OAI.KadisonKastler.PointedMatrixSites.twoRatio_centralizer_diffuse
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T14:28:11.993123+00:00
-- url     : https://prove2.me/submissions/a02782a1-0ae1-419d-8fc8-e6434879b9c0

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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_OAIQ075A032
import Definitions.Def_Q260K044

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MinimalProjectionEquivalence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Minimal projections, equivalence and automorphisms in a factor -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem partialIsometry_target_ne_zero (v : PartialIsometry M)
    (h : v.support.val ≠ 0) : v.target.val ≠ 0 := by
  intro hz
  have hv : v.val = 0 := by
    have hh := v.target_mul
    rw [hz, zero_mul] at hh
    exact hh.symm
  apply h
  rw [← v.initial, hv, star_zero, zero_mul]

theorem minimalProjection_partialIsometry_target (v : PartialIsometry M)
    (hp : IsMinimalProjectionIn M v.support) : IsMinimalProjectionIn M v.target := by
  refine ⟨partialIsometry_target_ne_zero v hp.1, ?_⟩
  intro q hq
  have hqright : q.val * v.target.val = q.val := projection_mul_of_le hq
  have hvstar : v.support.val * star v.val = star v.val := by
    simpa only [star_mul, v.support.property.isSelfAdjoint.star_eq, star_star] using
      congrArg star v.mul_support
  let a : Algebra M := star v.val * q.val * v.val
  have has : IsSelfAdjoint a := by
    change star (star v.val * q.val * v.val) = star v.val * q.val * v.val
    simp only [star_mul, star_star, q.property.isSelfAdjoint.star_eq, mul_assoc]
  have hai : a * a = a := by
    change (star v.val * q.val * v.val) * (star v.val * q.val * v.val) = _
    calc
      _ = star v.val * (q.val * v.target.val) * q.val * v.val := by
        change _ = star v.val * (q.val * (v.val * star v.val)) * q.val * v.val
        simp only [mul_assoc]
      _ = a := by rw [hqright]; simp only [a, mul_assoc, q.property.isIdempotentElem.eq]
  let r : AlgebraProjection M := ⟨a, ⟨hai, has⟩⟩
  have hr : r ≤ v.support := by
    change v.support.val * (star v.val * q.val * v.val) = star v.val * q.val * v.val
    simp only [← mul_assoc, hvstar]
  have hrecover : v.val * r.val * star v.val = q.val := by
    change v.val * (star v.val * q.val * v.val) * star v.val = q.val
    calc
      _ = v.target.val * q.val * v.target.val := by
        change _ = (v.val * star v.val) * q.val * (v.val * star v.val)
        simp only [mul_assoc]
      _ = q.val := by rw [show v.target.val * q.val = q.val from hq, hqright]
  rcases hp.2 r hr with hz | he
  · left
    rw [hz, mul_zero, zero_mul] at hrecover
    exact hrecover.symm
  · right
    apply Subtype.ext
    rw [he, v.mul_support] at hrecover
    exact hrecover.symm

private theorem factor_scalar_algebra (hM : ScalarCenter M) :
    ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M) := by
  intro c hc
  obtain ⟨z, hz⟩ := hM c.val c.property
    (fun a ha => congrArg Subtype.val (hc ⟨a, ha⟩))
  exact ⟨z, Subtype.ext hz⟩

theorem factor_exists_minimal_below (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hp : IsMinimalProjectionIn M p)
    (q : AlgebraProjection M) (hq : q.val ≠ 0) :
    ∃ r : AlgebraProjection M, r ≤ q ∧ IsMinimalProjectionIn M r := by
  obtain ⟨v, hvs, hvt, hv0⟩ :=
    traceFree_exists_nonzero_partialIsometry_between_projections
      (factor_scalar_algebra hM) p q hp.1 hq
  have hvp : v.support = p := (hp.2 v.support hvs).resolve_left hv0
  exact ⟨v.target, hvt, minimalProjection_partialIsometry_target v (hvp ▸ hp)⟩

theorem factor_minimal_projections_equivalent (hM : ScalarCenter M)
    (p q : AlgebraProjection M) (hp : IsMinimalProjectionIn M p)
    (hq : IsMinimalProjectionIn M q) : p.Equivalent q := by
  obtain ⟨v, hvs, hvt, hv0⟩ :=
    traceFree_exists_nonzero_partialIsometry_between_projections
      (factor_scalar_algebra hM) p q hp.1 hq.1
  exact ⟨v, (hp.2 v.support hvs).resolve_left hv0,
    (hq.2 v.target hvt).resolve_left (partialIsometry_target_ne_zero v hv0)⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductStateCentralizer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The centralizer of an infinite product state is irreducible

The proof uses only dense local vectors and state-preserving local swaps
which move a local observable to an independent set of sites. These are
the finite-site properties of the two-ratio tensor product in section 6.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_productVectorState_le (Ω : H) (hΩ : ‖Ω‖ = 1) (T : H →L[ℂ] H) :
    ‖productVectorState Ω T‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖Ω‖ * ‖T Ω‖ := norm_inner_le_norm _ _
    _ ≤ ‖Ω‖ * (‖T‖ * ‖Ω‖) := mul_le_mul_of_nonneg_left (T.le_opNorm Ω) (norm_nonneg Ω)
    _ = ‖T‖ := by rw [hΩ]; ring

/-- State centralization and commutation with `x` allow a local observable
to be moved by the swap while leaving its pairing with `x` unchanged. -/
theorem productVectorState_swap (D : VonNeumannAlgebra H) (Ω : H)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ D)
    (hcentral : ProductStateCentralizes D Ω u)
    (a x : H →L[ℂ] H) (ha : a ∈ D) (hx : x ∈ D)
    (hcomm : (u : H →L[ℂ] H) * x = x * u) :
    productVectorState Ω (unitaryConj u a * x) = productVectorState Ω (a * x) := by
  have hxu : star (u : H →L[ℂ] H) * x * u = x := by
    calc
      _ = star (u : H →L[ℂ] H) * (x * u) := mul_assoc _ _ _
      _ = star (u : H →L[ℂ] H) * (u * x) := by rw [← hcomm]
      _ = x := by rw [← mul_assoc, Unitary.star_mul_self_of_mem u.property, one_mul]
  calc
    _ = productVectorState Ω ((u : H →L[ℂ] H) * (a * star (u : H →L[ℂ] H) * x)) := by
      simp only [unitaryConj, mul_assoc]
    _ = productVectorState Ω ((a * star (u : H →L[ℂ] H) * x) * u) :=
      hcentral _ (D.mul_mem (D.mul_mem ha (D.toStarSubalgebra.star_mem' hu)) hx)
    _ = productVectorState Ω (a * x) := by rw [mul_assoc a, mul_assoc a, hxu]

omit [CompleteSpace H] in
/-- A vector-functional error only sees the vector error in the right factor. -/
theorem productVectorState_mul_error (Ω : H) (hΩ : ‖Ω‖ = 1)
    (a x y : H →L[ℂ] H) :
    ‖productVectorState Ω (a * x) - productVectorState Ω (a * y)‖ ≤
      ‖a‖ * ‖(x - y) Ω‖ := by
  calc
    _ = ‖inner ℂ Ω (a ((x - y) Ω))‖ := by
      simp only [productVectorState, mul_apply_eq_comp, sub_apply, map_sub, inner_sub_right]
    _ ≤ ‖Ω‖ * ‖a ((x - y) Ω)‖ := norm_inner_le_norm _ _
    _ ≤ ‖Ω‖ * (‖a‖ * ‖(x - y) Ω‖) :=
      mul_le_mul_of_nonneg_left (a.le_opNorm _) (norm_nonneg Ω)
    _ = ‖a‖ * ‖(x - y) Ω‖ := by rw [hΩ, one_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductStateIrreducible
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Local independent swaps force scalar relative commutant -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace LocalProductSwaps

variable {D : VonNeumannAlgebra H} {Ω : H} (L : LocalProductSwaps D Ω)

/-- Factorization of the vector state against every local observable. -/
theorem local_factorization (hΩ : ‖Ω‖ = 1) (x : H →L[ℂ] H) (hx : x ∈ D)
    (hcomm : ∀ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ D →
      ProductStateCentralizes D Ω u → (u : H →L[ℂ] H) * x = x * u)
    (k : ℕ) (a : L.localAlgebra k) :
    productVectorState Ω ((a : H →L[ℂ] H) * x) =
      productVectorState Ω a * productVectorState Ω x := by
  apply eq_of_sub_eq_zero
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  simp only [zero_add]
  let δ := ε / (2 * ‖(a : H →L[ℂ] H)‖ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ := Metric.mem_closure_iff.mp (L.dense (x Ω)) δ hδ
  have herr : ‖(x - (p.2 : H →L[ℂ] H)) Ω‖ < δ := by
    simpa only [dist_eq_norm, sub_apply, norm_sub_rev] using hp
  obtain ⟨u, hu, hc, hi⟩ := L.independent_swap k a p.1
  let b : H →L[ℂ] H := p.2
  let c : H →L[ℂ] H := unitaryConj u a
  have hs : productVectorState Ω (c * x) = productVectorState Ω (a * x) :=
    productVectorState_swap D Ω u hu hc a x (L.local_le k a.property) hx (hcomm u hu hc)
  have hi' : productVectorState Ω (c * b) =
      productVectorState Ω a * productVectorState Ω b := hi p.2
  have he : productVectorState Ω (a * x) -
      productVectorState Ω a * productVectorState Ω x =
      (productVectorState Ω (c * x) - productVectorState Ω (c * b)) +
        productVectorState Ω a * (productVectorState Ω b - productVectorState Ω x) := by
    rw [hs, hi']
    ring
  have hv : ‖productVectorState Ω b - productVectorState Ω x‖ ≤ ‖(x - b) Ω‖ := by
    calc
      _ = ‖inner ℂ Ω ((b - x) Ω)‖ := by
        simp only [productVectorState, sub_apply, inner_sub_right]
      _ ≤ ‖Ω‖ * ‖(b - x) Ω‖ := norm_inner_le_norm _ _
      _ = ‖(x - b) Ω‖ := by rw [hΩ, one_mul, sub_apply, norm_sub_rev, ← sub_apply]
  apply le_of_lt
  calc
    _ = ‖(productVectorState Ω (c * x) - productVectorState Ω (c * b)) +
        productVectorState Ω a * (productVectorState Ω b - productVectorState Ω x)‖ :=
      congrArg norm he
    _ ≤ ‖productVectorState Ω (c * x) - productVectorState Ω (c * b)‖ +
        ‖productVectorState Ω a * (productVectorState Ω b - productVectorState Ω x)‖ :=
      norm_add_le _ _
    _ ≤ ‖c‖ * ‖(x - b) Ω‖ + ‖(a : H →L[ℂ] H)‖ * ‖(x - b) Ω‖ := by
      apply add_le_add (productVectorState_mul_error Ω hΩ c x b)
      rw [norm_mul]
      exact mul_le_mul (norm_productVectorState_le Ω hΩ a) hv (norm_nonneg _) (norm_nonneg _)
    _ = 2 * ‖(a : H →L[ℂ] H)‖ * ‖(x - b) Ω‖ := by
      dsimp [c]
      rw [norm_unitaryConj]
      ring
    _ ≤ (2 * ‖(a : H →L[ℂ] H)‖ + 1) * ‖(x - b) Ω‖ := by
      nlinarith [norm_nonneg ((x - b) Ω)]
    _ < (2 * ‖(a : H →L[ℂ] H)‖ + 1) * δ :=
      mul_lt_mul_of_pos_left herr (by positivity)
    _ = ε := mul_div_cancel₀ _ (by positivity)

include L in
/-- The relative commutant of the full vector-state centralizer is scalar.
The argument uses only finite-site independence, dense local vectors, and
separation by the product vector. -/
theorem scalar_of_commutes (hΩ : ‖Ω‖ = 1)
    (hsep : Function.Injective (algebraVectorMap D Ω))
    (x : H →L[ℂ] H) (hx : x ∈ D)
    (hcomm : ∀ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ D →
      ProductStateCentralizes D Ω u → (u : H →L[ℂ] H) * x = x * u) :
    x = productVectorState Ω x • (1 : H →L[ℂ] H) := by
  have hv : x Ω = productVectorState Ω x • Ω := by
    apply DenseRange.eq_of_inner_right ℂ L.dense
    rintro ⟨k, a⟩
    have hf := L.local_factorization hΩ x hx hcomm k (star a)
    calc
      inner ℂ ((a : H →L[ℂ] H) Ω) (x Ω) =
          productVectorState Ω ((star (a : H →L[ℂ] H)) * x) := by
        rw [← ContinuousLinearMap.adjoint_inner_right]
        rfl
      _ = productVectorState Ω (star (a : H →L[ℂ] H)) * productVectorState Ω x := hf
      _ = inner ℂ ((a : H →L[ℂ] H) Ω) (productVectorState Ω x • Ω) := by
        rw [inner_smul_right]
        change inner ℂ Ω ((a : H →L[ℂ] H).adjoint Ω) * productVectorState Ω x = _
        rw [ContinuousLinearMap.adjoint_inner_right]
        ring
  have he : (⟨x, hx⟩ : Algebra D) =
      ⟨productVectorState Ω x • (1 : H →L[ℂ] H),
        D.toStarSubalgebra.smul_mem D.one_mem _⟩ := by
    apply hsep
    simpa only [algebraVectorMap, LinearMap.coe_mk, AddHom.coe_mk, smul_apply,
      one_apply_eq_self] using hv
  exact congrArg Subtype.val he

end LocalProductSwaps

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductMatrixStages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Deriving the product-state argument from finite matrix data

A remote copy of a finite tensor block has identical matrix moments.
Every other finite block embeds in the product of these two blocks and
a finite complement. These are finite tensor-product statements; no
centralizer irreducibility or crossed-product conclusion is assumed.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ProductMatrixStages

variable (P : ProductMatrixStages (H := H))

/-- The finite-product construction implies the irreducibility of its
state centralizer. -/
theorem state_centralizer_irreducible (x : H →L[ℂ] H) (hx : x ∈ P.algebra)
    (hc : ∀ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ P.algebra →
      ProductStateCentralizes P.algebra P.vector u → (u : H →L[ℂ] H) * x = x * u) :
    x = productVectorState P.vector x • (1 : H →L[ℂ] H) :=
  P.localSwaps.scalar_of_commutes P.unit_vector P.separating x hx hc

end ProductMatrixStages

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateCentralizerVonNeumann
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # The exact vector-state centralizer as a von Neumann algebra

Strong approximation preserves its defining matrix-coefficient identities.
The reference vector restricts to a faithful trace. For the fixed product
construction, finite-site swaps make this centralizer a factor.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem ProductMatrixStages.stateCentralizer_scalarCenter (P : ProductMatrixStages (H := H)) :
    ScalarCenter (stateCentralizerVonNeumann (M := P.algebra) P.vector) := by
  intro a ha hc
  refine ⟨productVectorState P.vector a,?_⟩
  apply P.state_centralizer_irreducible a ha.1
  intro u hu huc
  exact hc u.val ⟨hu,huc⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductCentralizerSmallProjections
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Small projections in the fixed product-state centralizer

The all-zero diagonal in a finite block of lambda sites is in the exact
state centralizer. Its trace is `(1 + lambda)⁻ⁿ`, hence tends to zero.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

theorem centralizerBlockZero_trace (l : List TwoRatioSite) (hl : l.Nodup) :
    (stateCentralizerTrace Ω S.unit_vector S.separating).trace
      (S.centralizerBlockZero l hl).val =
      matrixSiteBlockWeight twoRatioSiteParameter l (matrixSiteBlockZero l)
        (matrixSiteBlockZero l) := S.blockEntry_moment l hl _ _

theorem lambda_block_zero_weight (l : List ℕ) :
    matrixSiteBlockWeight twoRatioSiteParameter (l.map Sum.inl)
      (matrixSiteBlockZero _) (matrixSiteBlockZero _) =
      ((((1+fixedProductLambda)⁻¹ : ℝ)^l.length : ℝ) : ℂ) := by
  induction l with
  | nil => change (1 : ℂ) = ((1 : ℝ) : ℂ); exact_mod_cast rfl
  | cons i l ih =>
    change (((1+fixedProductLambda)⁻¹ : ℝ) : ℂ) *
      matrixSiteBlockWeight twoRatioSiteParameter (l.map Sum.inl)
        (matrixSiteBlockZero _) (matrixSiteBlockZero _) =
      ((((1+fixedProductLambda)⁻¹ : ℝ)^(l.length+1) : ℝ) : ℂ)
    rw [ih,pow_succ,Complex.ofReal_mul]
    exact mul_comm _ _

/-- Nonzero exact centralizer projections with arbitrarily small faithful trace. -/
theorem exists_small_centralizer_projection (ε : ℝ) (hε : 0 < ε) :
    ∃ p : AlgebraProjection (stateCentralizerVonNeumann (M := M) Ω),
      p.val ≠ 0 ∧
      ((stateCentralizerTrace Ω S.unit_vector S.separating).trace p.val).re < ε := by
  classical
  have hr : 0 < (1+fixedProductLambda)⁻¹ :=
    inv_pos.mpr (by linarith [fixedProductLambda_pos])
  have hr1 : (1+fixedProductLambda)⁻¹ < 1 := by
    rw [inv_lt_one₀ (by linarith [fixedProductLambda_pos])]
    linarith [fixedProductLambda_pos]
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1
  have he : ∀ᶠ n : ℕ in atTop, ((1+fixedProductLambda)⁻¹ : ℝ)^n < ε :=
    ht (Iio_mem_nhds hε)
  obtain ⟨n,hn⟩ := he.exists
  let l : List TwoRatioSite := (List.range n).map Sum.inl
  have hl : l.Nodup := List.nodup_range.map Sum.inl_injective
  let p := S.centralizerBlockZero l hl
  have hp : (stateCentralizerTrace Ω S.unit_vector S.separating).trace p.val =
      ((((1+fixedProductLambda)⁻¹ : ℝ)^n : ℝ) : ℂ) := by
    rw [S.centralizerBlockZero_trace]
    simpa only [l,List.length_range] using lambda_block_zero_weight (List.range n)
  refine ⟨p,?_,?_⟩
  · intro hz
    have hh := hp
    rw [hz] at hh
    change inner ℂ Ω ((0 : H →L[ℂ] H) Ω) = _ at hh
    simp only [zero_apply,inner_zero_right] at hh
    have hnz : ((((1+fixedProductLambda)⁻¹ : ℝ)^n : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (pow_pos hr n)
    exact hnz hh.symm
  · rw [hp,Complex.ofReal_re]
    exact hn

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductCentralizerDiffuse
attribute [-instance] _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Diffuseness of the fixed product-state centralizer

Scalar center and small nonzero projections exclude minimal projections.
This supplies the trace cuts used to assemble state-scaling isometries.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem algebraProjection_trace_mono (τ : TracialRepresentation M)
    {p q : AlgebraProjection M} (h : p ≤ q) :
    (τ.trace p.val).re ≤ (τ.trace q.val).re := by
  have he := projection_trace_sq τ (q.val-p.val)
    (p.property.sub_of_mul_eq_right q.property h)
  rw [τ.trace_sub,Complex.sub_re] at he
  nlinarith [sq_nonneg (τ.norm₂ (q.val-p.val))]

theorem factor_no_minimal_of_small_projections (τ : TracialRepresentation M)
    (hM : ScalarCenter M)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ q : AlgebraProjection M,
      q.val ≠ 0 ∧ (τ.trace q.val).re < ε)
    (p : AlgebraProjection M) : ¬ IsMinimalProjectionIn M p := by
  intro hp
  obtain ⟨q,hq,hqt⟩ := hsmall _ (projection_trace_pos τ p.val p.property hp.1)
  obtain ⟨r,hrq,hr⟩ := factor_exists_minimal_below hM p hp q hq
  obtain ⟨v,hvp,hvr⟩ := factor_minimal_projections_equivalent hM p r hp hr
  have ht : τ.trace p.val=τ.trace r.val := by
    rw [← hvp,← hvr]
    exact v.trace_support_eq_target τ
  have hle := algebraProjection_trace_mono τ hrq
  rw [← ht] at hle
  exact (not_lt_of_ge hle) hqt

theorem diffuse_of_no_minimal
    (h : ∀ p : AlgebraProjection M, ¬ IsMinimalProjectionIn M p)
    (p : Algebra M) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q := by
  classical
  by_contra hn
  apply h ⟨p,hp⟩
  refine ⟨hp0,?_⟩
  intro q hq
  by_cases hq0 : q.val=0
  · exact Or.inl hq0
  · right
    by_contra hqp
    apply hn
    exact ⟨q.val,q.property,hq0,(fun he => hqp (Subtype.ext he)),hq,
      projection_mul_of_le hq⟩

namespace PointedMatrixSites

variable {Ω : H} (S : PointedMatrixSites M Ω twoRatioSiteParameter)

include S

theorem twoRatio_centralizer_scalarCenter :
    ScalarCenter (stateCentralizerVonNeumann (M := M) Ω) := by
  have h := S.twoRatioStages.stateCentralizer_scalarCenter
  change ScalarCenter (stateCentralizerVonNeumann (M := S.twoRatioStages.algebra) Ω) at h
  simpa only [S.twoRatioStages_algebra] using h

theorem twoRatio_centralizer_diffuse_oai
    (p : Algebra (stateCentralizerVonNeumann (M := M) Ω))
    (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : Algebra (stateCentralizerVonNeumann (M := M) Ω),
      IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q :=
  diffuse_of_no_minimal
    (factor_no_minimal_of_small_projections
      (stateCentralizerTrace Ω S.unit_vector S.separating)
      S.twoRatio_centralizer_scalarCenter S.exists_small_centralizer_projection) p hp hp0

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.PointedMatrixSites.twoRatio_centralizer_diffuse_oai.{u_1} := @OAI.KadisonKastler.PointedMatrixSites.twoRatio_centralizer_diffuse_oai.{u_1}
