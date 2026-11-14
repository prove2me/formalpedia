-- Prove2me | solution 1 for OAI.KadisonKastler.TypeIIIFactor.exists_countable_amplification_unitary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:59:49.297276+00:00
-- url     : https://prove2.me/submissions/1673f39b-6585-4bd0-9602-7bec318704c9

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
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
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
import Mathlib.Analysis.Complex.Norm
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
import Mathlib.Analysis.Normed.Module.RCLike.Real
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
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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
import Mathlib.Data.Fintype.Fin
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
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
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
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
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K066
import Definitions.Def_Q260K034
import Theorems.Thm_OAI_Generator_Tracial_AlgebraProjection_equivalent_of_le_of_subequivalent
import Theorems.Thm_OAI_KadisonKastler_TypeIIIFactor_commutant_properlyInfinite
import Theorems.Thm_OAI_KadisonKastler_exists_countable_source_partition_of_full

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProperInfiniteProjectionCopies
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.mem_projectionFamilyRemainderSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable copies of a full projection

A maximal orthogonal family with sources under a full projection gives a
countable partition of the identity.  Two orthogonal isometries provide
room for countably many copies of the full projection.  The partition
embeds into their sum, and concrete projection Schroeder--Bernstein moves
that sum onto the identity.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped BigOperators Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- Orthogonal projection sums are strong sums in the original representation. -/
theorem exists_orthogonal_projection_sum (p : ℕ → AlgebraProjection M)
    (ho : Pairwise (fun i j => (p i).val * (p j).val = 0)) :
    ∃ q : AlgebraProjection M, (∀ i, p i ≤ q) ∧
      (∀ r : AlgebraProjection M, (∀ i, p i ≤ r) → q ≤ r) ∧
      ∀ x : H, HasSum (fun i => ((p i).val : H →L[ℂ] H) x)
        ((q.val : H →L[ℂ] H) x) := by
  let a := finiteProjectionSum p ho
  have ha : Monotone a := by
    intro s t hst
    apply (AlgebraProjection.finsetSum_le_iff p s _ _).mpr
    intro i hi
    exact (AlgebraProjection.finsetSum_le_iff p t _ _).mp le_rfl i (hst hi)
  obtain ⟨q, hq⟩ := AlgebraProjection.exists_isLUB_monotone a ha
  refine ⟨q, ?_, ?_, ?_⟩
  · intro i
    have hi : p i ≤ a {i} :=
      (AlgebraProjection.finsetSum_le_iff p {i} _ _).mp le_rfl i (by simp)
    exact hi.trans (hq.1 ⟨{i}, rfl⟩)
  · intro r hr
    apply hq.2
    rintro _ ⟨s, rfl⟩
    exact (AlgebraProjection.finsetSum_le_iff p s _ r).mpr (fun i _ => hr i)
  · intro x
    have hv := AlgebraProjection.vectorValue_tendsto_monotone a ha q hq x
    have hs (s : Finset ℕ) :
        ‖(q.val : H →L[ℂ] H) x - ((a s).val : H →L[ℂ] H) x‖ ^ 2 =
          AlgebraProjection.vectorValue x q - AlgebraProjection.vectorValue x (a s) := by
      have hh := AlgebraProjection.vectorValue_remainder x (a s) q (hq.1 ⟨s, rfl⟩)
      rw [AlgebraProjection.vectorValue_eq_norm_sq] at hh
      exact hh
    have hc : Tendsto (fun _ : Finset ℕ => AlgebraProjection.vectorValue x q)
        atTop (𝓝 (AlgebraProjection.vectorValue x q)) := tendsto_const_nhds
    have hh := hc.sub hv
    rw [sub_self] at hh
    have hsquare := hh.congr (fun s => (hs s).symm)
    have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    have hnorm : Tendsto (fun s : Finset ℕ =>
        ‖((a s).val : H →L[ℂ] H) x - (q.val : H →L[ℂ] H) x‖) atTop (𝓝 0) := by
      simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
        Real.sqrt_zero, norm_sub_rev, Function.comp_def] using hn
    have ht := tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
    have ha_apply (s : Finset ℕ) :
        ((a s).val : H →L[ℂ] H) x = ∑ i ∈ s, ((p i).val : H →L[ℂ] H) x := by
      change (M.toStarSubalgebra.subtype (∑ i ∈ s, (p i).val)) x = _
      rw [map_sum]
      simp only [sum_apply]
      rfl
    simpa only [HasSum, SummationFilter.unconditional, ha_apply] using ht

private theorem copySlot_cross (u v : Algebra M) (hu : star u * u = 1)
    (hv : star v * v = 1) (huv : star u * v = 0) (p : AlgebraProjection M)
    {i j : ℕ} (hij : i < j) :
    star (copySlot u v hu hv p i).val * (copySlot u v hu hv p j).val = 0 := by
  have hvu : star v * u = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star huv
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hij)
  have hk : 0 < k := by omega
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  change star (u ^ i * v * p.val) * (u ^ (i + (l + 1)) * v * p.val) = 0
  rw [star_mul, star_mul, p.property.isSelfAdjoint.star_eq, pow_add]
  calc
    _ = p.val * star v * (star (u ^ i) * u ^ i) * u ^ (l + 1) * v * p.val := by
      simp only [mul_assoc]
    _ = 0 := by
      rw [isometry_power u hu, mul_one, pow_succ']
      calc
        _ = p.val * (star v * u) * u ^ l * v * p.val := by simp only [mul_assoc]
        _ = 0 := by rw [hvu, mul_zero, zero_mul, zero_mul, zero_mul]

private theorem copySlot_orthogonal (u v : Algebra M) (hu : star u * u = 1)
    (hv : star v * v = 1) (huv : star u * v = 0) (p : AlgebraProjection M) :
    Pairwise (fun i j => (copySlot u v hu hv p i).target.val *
      (copySlot u v hu hv p j).target.val = 0) := by
  have hh {i j : ℕ} (hij : i < j) :
      (copySlot u v hu hv p i).target.val * (copySlot u v hu hv p j).target.val = 0 := by
    change ((copySlot u v hu hv p i).val * star (copySlot u v hu hv p i).val) *
      ((copySlot u v hu hv p j).val * star (copySlot u v hu hv p j).val) = 0
    calc
      _ = (copySlot u v hu hv p i).val *
          (star (copySlot u v hu hv p i).val * (copySlot u v hu hv p j).val) *
          star (copySlot u v hu hv p j).val := by simp only [mul_assoc]
      _ = 0 := by rw [copySlot_cross u v hu hv huv p hij, mul_zero, zero_mul]
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hh h
  · exact PartialIsometry.orthogonal_reverse _ _ (hh h)

/-- Countably many copies of a full projection fill a properly infinite,
separably acting algebra. All the witnesses lie in the original algebra. -/
theorem exists_countable_projection_copies [TopologicalSpace.SeparableSpace H]
    (hM : ProperlyInfiniteIdentity M) (p : AlgebraProjection M)
    (hp : (centralSupport p).val = 1) : Nonempty (CountableProjectionCopies M p) := by
  obtain ⟨u, v, hu, hv, huv⟩ := hM.isometries
  let slot := copySlot u v hu hv p
  have ho : Pairwise (fun i j => (slot i).target.val * (slot j).target.val = 0) :=
    copySlot_orthogonal u v hu hv huv p
  obtain ⟨q, hq, _, hsum⟩ := exists_orthogonal_projection_sum (fun i => (slot i).target) ho
  obtain ⟨a, ha, hao, hatotal⟩ := exists_countable_source_partition_of_full p hp
  let b (n : ℕ) : PartialIsometry M := (slot n).compose (a n).adjoint (by
    rw [PartialIsometry.adjoint_target]
    exact ha n)
  have hbs (n : ℕ) : (b n).support = (a n).target := rfl
  have hbt (n : ℕ) : (b n).target ≤ (slot n).target :=
    PartialIsometry.compose_target_le _ _ _
  obtain ⟨B, _, hBs, hBt⟩ := PartialIsometry.traceFree_orthogonal_sum b
    (by intro i j hij; rw [hbs, hbs]; exact hao hij)
    (by intro i j hij; exact projection_orthogonal_of_le (ho hij) (hbt i) (hbt j))
  let oneP : AlgebraProjection M := ⟨1, IsStarProjection.one _⟩
  have hB1 : B.support = oneP := Subtype.ext (hatotal _ (fun n => by
    simpa only [hbs] using (hBs B.support).mp le_rfl n)).symm
  have hBq : B.target ≤ q := (hBt _).mpr (fun n => (hbt n).trans (hq n))
  have hq1 : q ≤ oneP := by change 1 * q.val = q.val; exact one_mul _
  obtain ⟨c, hcq, hc1⟩ := AlgebraProjection.equivalent_of_le_of_subequivalent hq1
    (show oneP.Subequivalent q from ⟨B, hB1, hBq⟩)
  let z (n : ℕ) := c.compose (slot n) (by rw [hcq]; exact hq n)
  have hzi (n : ℕ) : star (z n).val * (z n).val = p.val := (z n).initial
  have hzf (n : ℕ) : (z n).target.val = c.val * (slot n).target.val * star c.val :=
    PartialIsometry.compose_target c (slot n) _
  refine ⟨{ projection := fun n => (z n).target
            witness := fun n => (z n).val
            initial := hzi
            final := fun _ => rfl
            orthogonal := ?_
            total := ?_ }⟩
  · intro i j hij
    rw [hzf, hzf]
    calc
      _ = c.val * (slot i).target.val * (star c.val * c.val) *
          (slot j).target.val * star c.val := by simp only [mul_assoc]
      _ = 0 := by
        rw [c.initial, hcq]
        calc
          _ = c.val * ((slot i).target.val * q.val) * (slot j).target.val *
              star c.val := by simp only [mul_assoc]
          _ = c.val * ((slot i).target.val * (slot j).target.val) * star c.val := by
            rw [projection_mul_of_le (hq i)]
            simp only [mul_assoc]
          _ = 0 := by rw [ho hij, mul_zero, zero_mul]
  · intro x
    have hs := (c.val : H →L[ℂ] H).hasSum (hsum ((star c.val : H →L[ℂ] H) x))
    have hcx : (c.val : H →L[ℂ] H) ((q.val : H →L[ℂ] H)
        ((star c.val : H →L[ℂ] H) x)) = x := by
      have hmul : c.val * q.val = c.val := by rw [← hcq]; exact c.mul_support
      have hfinal : c.val * star c.val = 1 := congrArg Subtype.val hc1
      calc
        _ = (((c.val * q.val) * star c.val : Algebra M) : H →L[ℂ] H) x := rfl
        _ = x := by rw [hmul, hfinal]; rfl
    rw [hcx] at hs
    apply hs.congr_fun
    intro n
    rw [hzf]
    rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FullCopyHilbertSum
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.countableHilbertSum_separable _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.countableOperatorEntry_apply _root_.OAI.KadisonKastler.countableOperatorEntry_diagonal_mul _root_.OAI.KadisonKastler.countableOperatorEntry_mul_diagonal _root_.OAI.KadisonKastler.countableTensorAlgebraic_tmul _root_.OAI.KadisonKastler.countableTensorEquiv_symm_single _root_.OAI.KadisonKastler.countableTensorEquiv_tmul _root_.OAI.KadisonKastler.countableTensorIsometry_tmul _root_.OAI.KadisonKastler.countableTensorVector_apply _root_.OAI.KadisonKastler.countableTensorVector_single _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tomitaPolarCoordinates_root _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Full projection copies identify the countable Hilbert amplification -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

namespace CountableProjectionCopies

variable (C : CountableProjectionCopies M (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))

theorem fullCopyUnitary_single (i : ℕ) (x : H) :
    C.fullCopyUnitary (lp.single 2 i x)=(C.witness i).val x :=
  C.fullCopyHilbertSum.linearIsometryEquiv_symm_apply_single x

theorem fullCopyUnitary_intertwines (a : H →L[ℂ] H)
    (ha : ∀ i, Commute a (C.witness i).val) (x : CountableHilbertSum H) :
    C.fullCopyUnitary (l2Diagonal a x)=a (C.fullCopyUnitary x) := by
  have hs := lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x
  have h1 := (C.fullCopyUnitary.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (l2Diagonal a)).hasSum hs
  have h2 := (a.comp C.fullCopyUnitary.toContinuousLinearEquiv.toContinuousLinearMap).hasSum hs
  have he (i : ℕ) :
      C.fullCopyUnitary (l2Diagonal a (lp.single 2 i (x i)))=
        a (C.fullCopyUnitary (lp.single 2 i (x i))) := by
    have hl : l2Diagonal a (lp.single 2 i (x i))=lp.single 2 i (a (x i)) := by
      ext j
      by_cases hji : j=i
      · subst j
        simp
      · simp [lp.single_apply,hji]
    rw [hl,fullCopyUnitary_single,fullCopyUnitary_single]
    exact congrArg (fun T : H →L[ℂ] H => T (x i)) (ha i).symm
  change HasSum (fun i => C.fullCopyUnitary (l2Diagonal a (lp.single 2 i (x i)))) _ at h1
  change HasSum (fun i => a (C.fullCopyUnitary (lp.single 2 i (x i)))) _ at h2
  simp_rw [he] at h1
  exact h1.unique h2

end CountableProjectionCopies

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIICountableAmplification
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable amplification is spatially absorbed by a type III representation -/

namespace KadisonKastler

open Generator.Tracial
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem TypeIIIFactor.exists_countable_amplification_unitary_oai (hM : TypeIIIFactor M) :
    ∃ U : CountableHilbertSum H ≃ₗᵢ[ℂ] H,
      ∀ (a : Algebra M) (x : CountableHilbertSum H), U (l2Diagonal a.val x)=a.val (U x) := by
  let p : AlgebraProjection M.commutant := ⟨1,IsStarProjection.one _⟩
  have hp : (centralSupport p).val=1 := by
    have he := le_centralSupport p
    change (centralSupport p).val*1=1 at he
    simpa only [mul_one] using he
  obtain ⟨C⟩ := exists_countable_projection_copies hM.commutant_properlyInfinite p hp
  refine ⟨C.fullCopyUnitary,?_⟩
  intro a x
  exact C.fullCopyUnitary_intertwines a.val (fun i =>
    VonNeumannAlgebra.mem_commutant_iff.mp (C.witness i).property a.val a.property) x

end
end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.TypeIIIFactor.exists_countable_amplification_unitary_oai.{u_1} := @OAI.KadisonKastler.TypeIIIFactor.exists_countable_amplification_unitary_oai.{u_1}
