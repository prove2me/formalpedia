-- Prove2me | solution 1 for OAI.KadisonKastler.typeIII_of_factorialCore
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:59:59.953193+00:00
-- url     : https://prove2.me/submissions/6e80f7c0-8dc0-4626-a593-10219af1197b

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
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
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
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
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
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
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K065
import Definitions.Def_Q260K066
import Definitions.Def_Q260K034
import Theorems.Thm_OAI_KadisonKastler_exists_countable_source_partition
import Theorems.Thm_OAI_KadisonKastler_projectionSemifinite_of_finite_projection
import Theorems.Thm_OAI_KadisonKastler_regularCore_not_factor_of_II1
import Theorems.Thm_OAI_KadisonKastler_regularCore_not_factor_of_typeI
import Theorems.Thm_OAI_KadisonKastler_regularCore_not_factor_of_typeIIInfinity

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InfiniteFactorProperInfiniteness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # An infinite factor is properly infinite

A proper isometry supplies an infinite orthogonal sequence of equivalent
wandering projections.  A maximal orthogonal family of partial isometries
with sources under the first wandering projection covers the identity by
factoriality.  Separability makes this family countable, so its ranges can
be mapped into the even and odd wandering projections separately.

No trace, dimension function, or published projection comparison is used.
-/

namespace KadisonKastler

open Generator.Tracial
open scoped BigOperators Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

private theorem le_projectionComplement {p q : AlgebraProjection M}
    (h : q.val * p.val = 0) : p ≤ projectionComplement q := by
  change (1 - q.val) * p.val = p.val
  rw [sub_mul, one_mul, h, sub_zero]

private theorem mul_eq_zero_of_le_complement {p q : AlgebraProjection M}
    (h : p ≤ projectionComplement q) : q.val * p.val = 0 := by
  change (1 - q.val) * p.val = p.val at h
  rw [sub_mul, one_mul] at h
  exact sub_eq_self.mp h

private theorem wanderingProjection_mul_p0 (w : Algebra M) (hw : star w * w = 1) :
    (wanderingProjection_p0 w hw).val * w = 0 := by
  change (1 - w * star w) * w = 0
  rw [sub_mul, one_mul, mul_assoc, hw, mul_one, sub_self]

private theorem wanderingProjection_mul_pow_p0 (w : Algebra M) (hw : star w * w = 1)
    {n : ℕ} (hn : 0 < n) : (wanderingProjection_p0 w hw).val * w ^ n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ', ← mul_assoc, wanderingProjection_mul_p0, zero_mul]

private theorem wandering_cross_p0 (w : Algebra M) (hw : star w * w = 1)
    {i j : ℕ} (hij : i < j) :
    star (wanderingPartialIsometry_p0 w hw i).val *
      (wanderingPartialIsometry_p0 w hw j).val = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hij)
  have hk : 0 < k := by omega
  change star (w ^ i * (wanderingProjection_p0 w hw).val) *
    (w ^ (i + k) * (wanderingProjection_p0 w hw).val) = 0
  rw [star_mul, (wanderingProjection_p0 w hw).property.isSelfAdjoint.star_eq, pow_add]
  calc
    _ = ((wanderingProjection_p0 w hw).val * (star (w ^ i) * w ^ i)) *
        w ^ k * (wanderingProjection_p0 w hw).val := by simp only [mul_assoc]
    _ = 0 := by
      rw [star_pow_mul_pow_p0 w hw, mul_one, wanderingProjection_mul_pow_p0 w hw hk,
        zero_mul]

private theorem wandering_targets_orthogonal_p0 (w : Algebra M) (hw : star w * w = 1) :
    Pairwise (fun i j => (wanderingPartialIsometry_p0 w hw i).target.val *
      (wanderingPartialIsometry_p0 w hw j).target.val = 0) := by
  intro i j hij
  have hforward {i j : ℕ} (hlt : i < j) :
      (wanderingPartialIsometry_p0 w hw i).target.val *
        (wanderingPartialIsometry_p0 w hw j).target.val = 0 := by
    change ((wanderingPartialIsometry_p0 w hw i).val *
      star (wanderingPartialIsometry_p0 w hw i).val) *
      ((wanderingPartialIsometry_p0 w hw j).val *
        star (wanderingPartialIsometry_p0 w hw j).val) = 0
    calc
      _ = (wanderingPartialIsometry_p0 w hw i).val *
          (star (wanderingPartialIsometry_p0 w hw i).val *
            (wanderingPartialIsometry_p0 w hw j).val) *
          star (wanderingPartialIsometry_p0 w hw j).val := by simp only [mul_assoc]
      _ = 0 := by rw [wandering_cross_p0 w hw hlt, mul_zero, zero_mul]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hforward hlt
  · exact PartialIsometry.orthogonal_reverse _ _ (hforward hgt)

private theorem orthogonal_targets_of_sums
    (a b : ℕ → PartialIsometry M) (v w : PartialIsometry M)
    (hv : ∀ p : AlgebraProjection M, v.target ≤ p ↔ ∀ i, (a i).target ≤ p)
    (hw : ∀ p : AlgebraProjection M, w.target ≤ p ↔ ∀ i, (b i).target ≤ p)
    (h : ∀ i j, (a i).target.val * (b j).target.val = 0) :
    v.target.val * w.target.val = 0 := by
  have ha (i : ℕ) : (a i).target.val * w.target.val = 0 := by
    have hh : w.target ≤ projectionComplement (a i).target :=
      (hw _).mpr (fun j => le_projectionComplement (h i j))
    exact mul_eq_zero_of_le_complement hh
  have hh : v.target ≤ projectionComplement w.target := (hv _).mpr (fun i =>
    le_projectionComplement (PartialIsometry.orthogonal_reverse _ _ (ha i)))
  exact PartialIsometry.orthogonal_reverse _ _ (mul_eq_zero_of_le_complement hh)

/-- A proper isometry in a separably acting factor yields two isometries
with orthogonal ranges. -/
theorem properlyInfiniteIdentity_of_proper_isometry [Nontrivial H]
    [TopologicalSpace.SeparableSpace H] (hM : ScalarCenter M)
    (w : Algebra M) (hw : star w * w = 1) (hproper : w * star w ≠ 1) :
    ProperlyInfiniteIdentity M := by
  have hf : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M) := by
    intro c hc
    obtain ⟨z, hz⟩ := hM c.val c.property (fun a ha =>
      congrArg Subtype.val (hc ⟨a, ha⟩))
    exact ⟨z, Subtype.ext hz⟩
  let p := wanderingProjection_p0 w hw
  have hp : p.val ≠ 0 := sub_ne_zero.mpr hproper.symm
  obtain ⟨a, hap, hao, hatotal⟩ := exists_countable_source_partition hf p hp
  let slot := wanderingPartialIsometry_p0 w hw
  let b (k n : ℕ) : PartialIsometry M :=
    (slot (2 * n + k)).compose (a n).adjoint (by
      rw [PartialIsometry.adjoint_target]
      exact hap n)
  have hbs (k n : ℕ) : (b k n).support = (a n).target := rfl
  have hbt (k n : ℕ) : (b k n).target ≤ (slot (2 * n + k)).target :=
    PartialIsometry.compose_target_le _ _ _
  have hbo (k : ℕ) : Pairwise (fun i j =>
      (b k i).target.val * (b k j).target.val = 0) := by
    intro i j hij
    exact projection_orthogonal_of_le (wandering_targets_orthogonal_p0 w hw
      (by omega : 2 * i + k ≠ 2 * j + k)) (hbt k i) (hbt k j)
  have hbi (k : ℕ) : Pairwise (fun i j =>
      (b k i).support.val * (b k j).support.val = 0) := by
    simpa only [hbs] using hao
  obtain ⟨v, _, hvs, hvt⟩ := PartialIsometry.traceFree_orthogonal_sum (b 0)
    (fun i j hij => hbi 0 hij) (fun i j hij => hbo 0 hij)
  obtain ⟨u, _, hus, hut⟩ := PartialIsometry.traceFree_orthogonal_sum (b 1)
    (fun i j hij => hbi 1 hij) (fun i j hij => hbo 1 hij)
  have hv1 : v.support.val = 1 := (hatotal _ (fun n => by
    simpa only [hbs] using (hvs v.support).mp le_rfl n)).symm
  have hu1 : u.support.val = 1 := (hatotal _ (fun n => by
    simpa only [hbs] using (hus u.support).mp le_rfl n)).symm
  have hcross : v.target.val * u.target.val = 0 := by
    apply orthogonal_targets_of_sums (b 0) (b 1) v u hvt hut
    intro i j
    exact projection_orthogonal_of_le (wandering_targets_orthogonal_p0 w hw
      (by omega : 2 * i + 0 ≠ 2 * j + 1)) (hbt 0 i) (hbt 1 j)
  have hstar : star v.val * v.target.val = star v.val := by
    simpa only [star_mul, v.target.property.isSelfAdjoint.star_eq] using
      congrArg star v.target_mul
  refine ⟨_root_.one_ne_zero, v.val, u.val, v.initial.trans hv1, u.initial.trans hu1, ?_⟩
  calc
    star v.val * u.val = (star v.val * v.target.val) * (u.target.val * u.val) := by
      rw [hstar, u.target_mul]
    _ = star v.val * (v.target.val * u.target.val) * u.val := by
      simp only [mul_assoc]
    _ = 0 := by rw [hcross, mul_zero, zero_mul]

/-- The formerly published infinite-factor projection input follows from
concrete partial-isometry comparison and separability. -/
theorem publishedInfiniteFactorProperlyInfinite :
    PublishedInfiniteFactorProperlyInfinite.{u} := by
  intro H _ _ _ _ _ M hM hInfinite
  simp only [FiniteProjectionIn, one_mul] at hInfinite
  push Not at hInfinite
  obtain ⟨w, hw, _, hproper⟩ := hInfinite
  exact properlyInfiniteIdentity_of_proper_isometry hM w hw hproper

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIFactorStability
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- A nonzero finite factor without minimal projections is a II₁ factor.
Finiteness is only assumed for its identity
projection; the required isometry condition follows directly. -/
theorem isII1Factor_of_finite_of_not_typeI {M : VonNeumannAlgebra H}
    (hM : ScalarCenter M) (hnonzero : (0 : H →L[ℂ] H) ≠ 1)
    (hfinite : FiniteProjectionIn M 1) (htype : ¬ IsTypeIFactor M) :
    Generator.IsII1Factor M.toStarSubalgebra := by
  refine {
    nonzero := hnonzero
    weaklyClosed := Generator.Tracial.vonNeumann_wotClosed M
    factor := ?_
    finite := fun v hv => hfinite v hv (one_mul v)
    diffuse := (isTypeIFactor_or_projectionDiffuse hM).resolve_left htype }
  intro x hx
  obtain ⟨z, hz⟩ := hM x.val x.property (fun y hy =>
    congrArg Subtype.val (hx ⟨y, hy⟩))
  refine ⟨z, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one]
  apply Subtype.ext
  exact hz

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FactorialCoreSourceType
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A factorial modular core forces the source factor to be type III -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem typeIII_of_factorialCore_oai (hM : ScalarCenter M) (Ω : H)
    (hs : Function.Injective (algebraVectorMap M Ω))
    (hc : DenseRange (algebraVectorMap M Ω))
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hn : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hm : IsModularStateGroup M Ω U)
    (hf : ScalarCenter (regularCoreAlgebra U hU M)) : TypeIIIFactor M := by
  have ht : ¬ IsTypeIFactor M := fun h => regularCore_not_factor_of_typeI h Ω hs hc U hU hn hm hf
  have hfinite : ¬ FiniteProjectionIn M 1 := by
    intro h
    exact regularCore_not_factor_of_II1
      (isII1Factor_of_finite_of_not_typeI hM zero_ne_one h ht) Ω hs hc U hU hn hm hf
  have hproper := publishedInfiniteFactorProperlyInfinite H M hM hfinite
  refine ⟨_root_.one_ne_zero, hM, ?_⟩
  intro p hp hpfinite
  by_contra hp0
  have hII : TypeIIInfinityFactor M := {
    factor := hM
    properlyInfinite := hproper
    semifinite := projectionSemifinite_of_finite_projection hM ⟨p, hp⟩ hp0 hpfinite
    diffuse := (isTypeIFactor_or_projectionDiffuse hM).resolve_left ht }
  exact regularCore_not_factor_of_typeIIInfinity hII Ω hs hc U hU hn hm hf

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.typeIII_of_factorialCore_oai.{u} := @OAI.KadisonKastler.typeIII_of_factorialCore_oai.{u}
