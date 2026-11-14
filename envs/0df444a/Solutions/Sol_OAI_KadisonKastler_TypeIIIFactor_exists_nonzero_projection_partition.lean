-- Prove2me | solution 1 for OAI.KadisonKastler.TypeIIIFactor.exists_nonzero_projection_partition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:07:34.557364+00:00
-- url     : https://prove2.me/submissions/7fd392cd-d424-4ad8-8580-ecf4bbd5d261

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
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
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K066

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIIMatrixCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable matrix corners in type III factors

The absence of nonzero finite projections gives a proper isometry. Its
wandering projections are nonzero and orthogonal. A projection supremum
completes them to a partition of one; the published comparison theorem
then joins the pieces by partial isometries.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped BigOperators Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem TypeIIIFactor.exists_proper_isometry (hM : TypeIIIFactor M) :
    ∃ w : Algebra M, star w * w = 1 ∧ w * star w ≠ 1 := by
  have hn : ¬ FiniteProjectionIn M (1 : Algebra M) := by
    intro hf
    have hz := hM.purelyInfinite 1 (IsStarProjection.one (Algebra M)) hf
    exact hM.nonzero (congrArg Subtype.val hz)
  simp only [FiniteProjectionIn, one_mul] at hn
  push Not at hn
  obtain ⟨w, hw, _, hproper⟩ := hn
  exact ⟨w, hw, hproper⟩

private theorem wanderingProjection_mul_p1 (w : Algebra M) (hw : star w * w = 1) :
    (wanderingProjection_p1 w hw).val * w = 0 := by
  change (1 - w * star w) * w = 0
  rw [sub_mul, one_mul, mul_assoc, hw, mul_one, sub_self]

private theorem wanderingProjection_mul_pow_p1 (w : Algebra M) (hw : star w * w = 1)
    {n : ℕ} (hn : 0 < n) : (wanderingProjection_p1 w hw).val * w ^ n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ', ← mul_assoc, wanderingProjection_mul_p1, zero_mul]

private theorem wandering_cross_p1 (w : Algebra M) (hw : star w * w = 1)
    {i j : ℕ} (hij : i < j) :
    star (wanderingPartialIsometry_p1 w hw i).val *
      (wanderingPartialIsometry_p1 w hw j).val = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hij)
  have hk : 0 < k := by omega
  change star (w ^ i * (wanderingProjection_p1 w hw).val) *
    (w ^ (i + k) * (wanderingProjection_p1 w hw).val) = 0
  rw [star_mul, (wanderingProjection_p1 w hw).property.isSelfAdjoint.star_eq, pow_add]
  calc
    _ = ((wanderingProjection_p1 w hw).val * (star (w ^ i) * w ^ i)) *
        w ^ k * (wanderingProjection_p1 w hw).val := by simp only [mul_assoc]
    _ = 0 := by
      rw [star_pow_mul_pow_p1 w hw, mul_one, wanderingProjection_mul_pow_p1 w hw hk,
        zero_mul]

private theorem wandering_targets_orthogonal_p1 (w : Algebra M) (hw : star w * w = 1) :
    Pairwise (fun i j => (wanderingPartialIsometry_p1 w hw i).target.val *
      (wanderingPartialIsometry_p1 w hw j).target.val = 0) := by
  intro i j hij
  have hforward {i j : ℕ} (hlt : i < j) :
      (wanderingPartialIsometry_p1 w hw i).target.val *
        (wanderingPartialIsometry_p1 w hw j).target.val = 0 := by
    change ((wanderingPartialIsometry_p1 w hw i).val *
      star (wanderingPartialIsometry_p1 w hw i).val) *
      ((wanderingPartialIsometry_p1 w hw j).val *
        star (wanderingPartialIsometry_p1 w hw j).val) = 0
    calc
      _ = (wanderingPartialIsometry_p1 w hw i).val *
          (star (wanderingPartialIsometry_p1 w hw i).val *
            (wanderingPartialIsometry_p1 w hw j).val) *
          star (wanderingPartialIsometry_p1 w hw j).val := by simp only [mul_assoc]
      _ = 0 := by rw [wandering_cross_p1 w hw hlt, mul_zero, zero_mul]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hforward hlt
  · exact PartialIsometry.orthogonal_reverse _ _ (hforward hgt)

/-- Every nonzero type III factor has a countably infinite orthogonal
family of nonzero projections, constructed from one proper isometry. -/
theorem TypeIIIFactor.exists_orthogonal_nonzero_projections (hM : TypeIIIFactor M) :
    ∃ p : ℕ → AlgebraProjection M,
      (∀ n, (p n).val ≠ 0) ∧ Pairwise (fun i j => (p i).val * (p j).val = 0) := by
  obtain ⟨w, hw, hproper⟩ := hM.exists_proper_isometry
  have hp : (wanderingProjection_p1 w hw).val ≠ 0 := by
    change 1 - w * star w ≠ 0
    exact sub_ne_zero.mpr hproper.symm
  refine ⟨fun n => (wanderingPartialIsometry_p1 w hw n).target, ?_,
    wandering_targets_orthogonal_p1 w hw⟩
  intro n hz
  have hv : (wanderingPartialIsometry_p1 w hw n).val = 0 :=
    (CStarRing.mul_star_self_eq_zero_iff _).mp hz
  have hi := (wanderingPartialIsometry_p1 w hw n).initial
  rw [hv, star_zero, zero_mul] at hi
  exact hp hi.symm

private theorem orthogonalProjectionNet_mono (p : ℕ → AlgebraProjection M)
    (ho : Pairwise (fun i j => (p i).val * (p j).val = 0)) :
    Monotone (orthogonalProjectionNet p ho) := by
  intro s t hst
  apply (AlgebraProjection.finsetSum_le_iff p s _ _).mpr
  intro i hi
  exact (AlgebraProjection.finsetSum_le_iff p t _ _).mp le_rfl i (hst hi)

private theorem exists_orthogonalProjection_sum (p : ℕ → AlgebraProjection M)
    (ho : Pairwise (fun i j => (p i).val * (p j).val = 0)) :
    ∃ q : AlgebraProjection M, (∀ i, p i ≤ q) ∧
      ∀ x : H, HasSum (fun i => ((p i).val : H →L[ℂ] H) x)
        ((q.val : H →L[ℂ] H) x) := by
  let a := orthogonalProjectionNet p ho
  have ha : Monotone a := orthogonalProjectionNet_mono p ho
  obtain ⟨q, hq⟩ := AlgebraProjection.exists_isLUB_monotone a ha
  refine ⟨q, ?_, ?_⟩
  · intro i
    have hi : p i ≤ a {i} :=
      (AlgebraProjection.finsetSum_le_iff p {i} _ _).mp le_rfl i (by simp)
    exact hi.trans (hq.1 ⟨{i}, rfl⟩)
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

/-- An infinite nonzero orthogonal family can be completed to a nonzero
strong partition of one by adding its residual projection to its first term. -/
theorem exists_nonzero_projection_partition_of_orthogonal
    (p : ℕ → AlgebraProjection M) (hp : ∀ i, (p i).val ≠ 0)
    (ho : Pairwise (fun i j => (p i).val * (p j).val = 0)) :
    ∃ d : ℕ → AlgebraProjection M, (∀ i, (d i).val ≠ 0) ∧
      Pairwise (fun i j => (d i).val * (d j).val = 0) ∧
      ∀ x : H, HasSum (fun i => ((d i).val : H →L[ℂ] H) x) x := by
  classical
  obtain ⟨q, hpq, hsum⟩ := exists_orthogonalProjection_sum p ho
  let r : AlgebraProjection M := ⟨1 - q.val, q.property.one_sub⟩
  have hpr (i : ℕ) : (p i).val * r.val = 0 := by
    change (p i).val * (1 - q.val) = 0
    rw [mul_sub, mul_one, projection_mul_of_le (hpq i), sub_self]
  have hrp (i : ℕ) : r.val * (p i).val = 0 :=
    PartialIsometry.orthogonal_reverse _ _ (hpr i)
  let d (i : ℕ) : AlgebraProjection M :=
    if i = 0 then orthogonalSum (p 0) r (hpr 0) else p i
  have hd (i : ℕ) : (d i).val = (p i).val + if i = 0 then r.val else 0 := by
    by_cases hi : i = 0
    · subst i; simp [d, orthogonalSum]
    · simp only [d, ite_eq_right hi, add_zero]
  refine ⟨d, ?_, ?_, ?_⟩
  · intro i hz
    by_cases hi : i = 0
    · subst i
      have hle := le_orthogonalSum_left (p 0) r (hpr 0)
      change (d 0).val * (p 0).val = (p 0).val at hle
      rw [hz, zero_mul] at hle
      exact hp 0 hle.symm
    · exact hp i (by simpa only [d, ite_eq_right hi] using hz)
  · intro i j hij
    rw [hd, hd]
    by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := Ne.symm hij
      simp only [ite_true, if_true, ite_eq_right hj, add_zero, add_mul, ho hij, hrp]
    · by_cases hj : j = 0
      · subst j
        simp only [ite_true, if_true, ite_eq_right hi, add_zero, mul_add, ho hij, hpr]
      · simpa only [ite_eq_right hi, ite_eq_right hj, add_zero] using ho hij
  · intro x
    have hs := (hsum x).add (hasSum_ite_eq (0 : ℕ) ((r.val : H →L[ℂ] H) x))
    have ht : (q.val : H →L[ℂ] H) x + (r.val : H →L[ℂ] H) x = x := by
      change (q.val : H →L[ℂ] H) x + ((1 : H →L[ℂ] H) - q.val) x = x
      simp only [sub_apply, one_apply_eq_self]
      abel
    rw [ht] at hs
    apply hs.congr_fun
    intro i
    rw [hd]
    by_cases hi : i = 0 <;> simp [hi]

/-- The projection partition required for countable matrix units is
constructed without any trace or extra projection-comparison assumption. -/
theorem TypeIIIFactor.exists_nonzero_projection_partition_oai (hM : TypeIIIFactor M) :
    ∃ d : ℕ → AlgebraProjection M, (∀ i, (d i).val ≠ 0) ∧
      Pairwise (fun i j => (d i).val * (d j).val = 0) ∧
      ∀ x : H, HasSum (fun i => ((d i).val : H →L[ℂ] H) x) x := by
  obtain ⟨p, hp, ho⟩ := hM.exists_orthogonal_nonzero_projections
  exact exists_nonzero_projection_partition_of_orthogonal p hp ho

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.TypeIIIFactor.exists_nonzero_projection_partition_oai.{u} := @OAI.KadisonKastler.TypeIIIFactor.exists_nonzero_projection_partition_oai.{u}
