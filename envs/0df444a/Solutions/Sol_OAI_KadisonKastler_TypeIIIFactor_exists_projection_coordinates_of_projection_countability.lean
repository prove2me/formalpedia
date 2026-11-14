-- Prove2me | solution 1 for OAI.KadisonKastler.TypeIIIFactor.exists_projection_coordinates_of_projection_countability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:57:45.28308+00:00
-- url     : https://prove2.me/submissions/f3422770-4b91-47d7-ad35-b46554996a2f

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
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
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
import Definitions.Def_Q260K020
import Definitions.Def_Q260K061
import Theorems.Thm_OAI_Generator_Tracial_AlgebraProjection_equivalent_of_le_of_subequivalent

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InfiniteFactorProperInfiniteness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

private theorem exists_maximal_sourceFamily (p : AlgebraProjection M) :
    ∃ s : Set (PartialIsometry M), Maximal (sourceFamily p) s := by
  apply zorn_subset
  intro c hc hchain
  refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
  constructor
  · intro v hv
    obtain ⟨s, hs, hvs⟩ := Set.mem_sUnion.mp hv
    exact (hc hs).1 v hvs
  · intro v hv w hw hvw
    obtain ⟨s, hs, hvs⟩ := Set.mem_sUnion.mp hv
    obtain ⟨t, ht, hwt⟩ := Set.mem_sUnion.mp hw
    rcases hchain.total hs ht with hst | hts
    · exact (hc ht).2 (hst hvs) hwt hvw
    · exact (hc hs).2 hvs (hts hwt) hvw

private theorem target_ne_zero_of_support_ne_zero (v : PartialIsometry M)
    (hv : v.support.val ≠ 0) : v.target.val ≠ 0 := by
  intro hz
  have he := v.target_mul
  rw [hz, zero_mul] at he
  have hi := v.initial
  rw [← he, star_zero, zero_mul] at hi
  exact hv hi.symm

/-- Every nonzero projection in a countably decomposable factor supplies a
countable partition of the identity by ranges of partial isometries whose
initial projections lie under the supplied projection. -/
theorem exists_countable_source_partition_of_projection_countability
    (hFamilies : HasCountableProjectionFamilies M)
    (hfactor : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M))
    (p : AlgebraProjection M) (hp : p.val ≠ 0) :
    ∃ a : ℕ → PartialIsometry M,
      (∀ n, (a n).support ≤ p) ∧
      Pairwise (fun i j => (a i).target.val * (a j).target.val = 0) ∧
      (∀ q : AlgebraProjection M, (∀ n, (a n).target ≤ q) →
        (1 : Algebra M) = q.val) := by
  classical
  obtain ⟨s, hs, hmax⟩ := exists_maximal_sourceFamily p
  have hcount : Countable s := hFamilies s
    (fun v : s => v.val.target)
    (fun v => target_ne_zero_of_support_ne_zero v.val ((hs.1 v.val v.property).2))
    (fun v w hvw => hs.2 v.property w.property (fun he => hvw (Subtype.ext he)))
  let : Encodable s := @Encodable.ofCountable s hcount
  let a (n : ℕ) : PartialIsometry M :=
    (Encodable.decode₂ s n).elim PartialIsometry.zero (fun v => v.val)
  have ha (v : s) : a (Encodable.encode v) = v.val := by
    simp only [a, Encodable.decode₂_encode, Option.elim_some]
  have has (n : ℕ) : a n = PartialIsometry.zero ∨ a n ∈ s := by
    unfold a
    cases h : Encodable.decode₂ s n with
    | none => exact Or.inl rfl
    | some v => exact Or.inr v.property
  have hap (n : ℕ) : (a n).support ≤ p := by
    rcases has n with h | h
    · rw [h]
      change p.val * 0 = 0
      exact mul_zero _
    · exact (hs.1 _ h).1
  have hao : Pairwise (fun i j => (a i).target.val * (a j).target.val = 0) := by
    intro i j hij
    unfold a
    cases hi : Encodable.decode₂ s i with
    | none => simp [PartialIsometry.zero, PartialIsometry.target]
    | some v =>
      cases hj : Encodable.decode₂ s j with
      | none => simp [PartialIsometry.zero, PartialIsometry.target]
      | some w =>
        apply hs.2 v.property w.property
        intro hvw
        have hvwe : v = w := Subtype.ext hvw
        have hvi := Encodable.decode₂_eq_some.mp hi
        have hwj := Encodable.decode₂_eq_some.mp hj
        exact hij (hvi.symm.trans (congrArg Encodable.encode hvwe |>.trans hwj))
  refine ⟨a, hap, hao, ?_⟩
  intro q hq
  by_contra hne
  let r := projectionComplement q
  have hr : r.val ≠ 0 := by
    change 1 - q.val ≠ 0
    exact sub_ne_zero.mpr hne
  obtain ⟨v, hvp, hvr, hv0⟩ :=
    traceFree_exists_nonzero_partialIsometry_between_projections hfactor p r hp hr
  have hsq (w : PartialIsometry M) (hw : w ∈ s) : w.target ≤ q := by
    simpa only [ha ⟨w, hw⟩] using hq (Encodable.encode (⟨w, hw⟩ : s))
  have hov (w : PartialIsometry M) (hw : w ∈ s) :
      v.target.val * w.target.val = 0 := by
    have hrq : r.val * q.val = 0 := by
      change (1 - q.val) * q.val = 0
      rw [sub_mul, one_mul, q.property.isIdempotentElem.eq, sub_self]
    exact projection_orthogonal_of_le hrq hvr (hsq w hw)
  have hnew : sourceFamily p (insert v s) := by
    constructor
    · intro w hw
      rcases Set.mem_insert_iff.mp hw with rfl | hw
      · exact ⟨hvp, hv0⟩
      · exact hs.1 w hw
    · intro w hw z hz hwz
      rcases Set.mem_insert_iff.mp hw with hw | hw
      · subst w
        rcases Set.mem_insert_iff.mp hz with hz | hz
        · subst z
          exact (hwz rfl).elim
        · exact hov z hz
      · rcases Set.mem_insert_iff.mp hz with hz | hz
        · subst z
          exact PartialIsometry.orthogonal_reverse _ _ (hov w hw)
        · exact hs.2 hw hz hwz
  have hvs : v ∈ s := hmax hnew (Set.subset_insert v s) (Set.mem_insert v s)
  have hz : v.target.val * v.target.val = 0 := hov v hvs
  rw [v.target.property.isIdempotentElem.eq] at hz
  exact target_ne_zero_of_support_ne_zero v hv0 hz

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionSchroederBernstein
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Schroeder--Bernstein for concrete projection equivalence

The proof constructs the unilateral shift on the iterated defect of a
partial isometry, then adds the identity on its orthogonal complement.
The construction uses the existing strong sums of partial isometries;
no finiteness or trace assumption occurs.
-/

namespace Generator.Tracial

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

namespace PartialIsometry

private theorem defect_mul (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) :
    (AlgebraProjection.remainder p v.support hp).val * v.val = 0 := by
  change (v.support.val - p.val) * v.val = 0
  rw [sub_mul, (v.target_le_iff_mul _).mp (ht.trans hp),
    (v.target_le_iff_mul _).mp ht, sub_self]

private theorem defect_mul_pow (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) {n : ℕ} (hn : 0 < n) :
    (AlgebraProjection.remainder p v.support hp).val * v.val ^ n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ', ← mul_assoc, defect_mul v p ht hp, zero_mul]

private theorem defectOrbit_target_le (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) (n : ℕ) :
    (defectOrbit v p ht hp n).target ≤ v.support := by
  apply ((defectOrbit v p ht hp n).target_le_iff_mul _).mpr
  change v.support.val * (v.val ^ n * (AlgebraProjection.remainder p v.support hp).val) =
    v.val ^ n * (AlgebraProjection.remainder p v.support hp).val
  cases n with
  | zero =>
    simp only [pow_zero, one_mul]
    exact AlgebraProjection.remainder_le p v.support hp
  | succ n =>
    rw [pow_succ']
    calc
      _ = ((v.support.val * v.val) * v.val ^ n) *
          (AlgebraProjection.remainder p v.support hp).val := by simp only [mul_assoc]
      _ = _ := by rw [(v.target_le_iff_mul _).mp (ht.trans hp)]

private theorem defectOrbit_cross (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) {i j : ℕ} (hij : i < j) :
    star (defectOrbit v p ht hp i).val * (defectOrbit v p ht hp j).val = 0 := by
  let d := AlgebraProjection.remainder p v.support hp
  have hd : d ≤ v.support := AlgebraProjection.remainder_le _ _ hp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hij)
  have hk : 0 < k := by omega
  change star (v.val ^ i * d.val) * (v.val ^ (i + k) * d.val) = 0
  rw [star_mul, d.property.isSelfAdjoint.star_eq, pow_add]
  calc
    _ = (d.val * (star (v.val ^ i) * v.val ^ i)) * v.val ^ k * d.val := by
      simp only [mul_assoc]
    _ = d.val * v.val ^ k * d.val := by
      by_cases hi : i = 0
      · subst i
        simp only [pow_zero, star_one, mul_one]
      · rw [power_initial v (ht.trans hp) (Nat.pos_of_ne_zero hi),
          projection_mul_of_le hd]
    _ = 0 := by rw [defect_mul_pow v p ht hp hk, zero_mul]

private theorem defectOrbit_orthogonal (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) :
    Pairwise (fun i j => (defectOrbit v p ht hp i).target.val *
      (defectOrbit v p ht hp j).target.val = 0) := by
  have hforward {i j : ℕ} (hij : i < j) :
      (defectOrbit v p ht hp i).target.val *
        (defectOrbit v p ht hp j).target.val = 0 := by
    change ((defectOrbit v p ht hp i).val * star (defectOrbit v p ht hp i).val) *
      ((defectOrbit v p ht hp j).val * star (defectOrbit v p ht hp j).val) = 0
    calc
      _ = (defectOrbit v p ht hp i).val *
          (star (defectOrbit v p ht hp i).val * (defectOrbit v p ht hp j).val) *
          star (defectOrbit v p ht hp j).val := by simp only [mul_assoc]
      _ = 0 := by rw [defectOrbit_cross v p ht hp hij, mul_zero, zero_mul]
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hforward h
  · exact orthogonal_reverse _ _ (hforward h)

/-- A partial isometry whose range lies in its source has orthogonal copies
of its defect, all lying under the original source projection. -/
theorem defect_copies (v : PartialIsometry M) (h : v.target ≤ v.support) :
    ∃ a : ℕ → PartialIsometry M,
      (∀ n, (a n).support = AlgebraProjection.remainder v.target v.support h) ∧
      (∀ n, (a n).target ≤ v.support) ∧
      Pairwise (fun i j => (a i).target.val * (a j).target.val = 0) :=
  ⟨defectOrbit v v.target le_rfl h, fun _ => rfl,
    defectOrbit_target_le v v.target le_rfl h, defectOrbit_orthogonal v v.target le_rfl h⟩

end PartialIsometry

end

end Generator.Tracial

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIIProjectionComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nonzero projections in separably acting type III factors

A nonfinite projection contains a proper isometry and hence countably
many orthogonal copies of a nonzero defect.  Factoriality supplies a
countable source partition under this defect.  It embeds the identity
into the original projection; concrete Schroeder--Bernstein gives the
required equivalence.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- A nonfinite projection in a separably acting factor is equivalent to
its identity.  The type III hypothesis is needed only to supply nonfiniteness. -/
theorem projection_equivalent_one_of_not_finite_of_projection_countability
    (hFamilies : HasCountableProjectionFamilies M) (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hInfinite : ¬ FiniteProjectionIn M p.val) :
    p.Equivalent (⟨1, IsStarProjection.one _⟩ : AlgebraProjection M) := by
  have hf : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M) := by
    intro c hc
    obtain ⟨z, hz⟩ := hM c.val c.property (fun a ha =>
      congrArg Subtype.val (hc ⟨a, ha⟩))
    exact ⟨z, Subtype.ext hz⟩
  simp only [FiniteProjectionIn] at hInfinite
  push Not at hInfinite
  obtain ⟨w, hw, hpw, hproper⟩ := hInfinite
  let v : PartialIsometry M := ⟨p, w, hw⟩
  have hvp : v.target ≤ v.support := (v.target_le_iff_mul p).mpr hpw
  let d := AlgebraProjection.remainder v.target v.support hvp
  have hd : d.val ≠ 0 := by
    change p.val - w * star w ≠ 0
    exact sub_ne_zero.mpr hproper.symm
  obtain ⟨slot, hs, ht, ho⟩ := v.defect_copies hvp
  obtain ⟨a, ha, hao, hatotal⟩ :=
    exists_countable_source_partition_of_projection_countability hFamilies hf d hd
  let b (n : ℕ) := (slot n).compose (a n).adjoint (by
    rw [PartialIsometry.adjoint_target, hs]
    exact ha n)
  have hbs (n : ℕ) : (b n).support = (a n).target := rfl
  have hbt (n : ℕ) : (b n).target ≤ p :=
    ((slot n).compose_target_le _ _).trans (ht n)
  obtain ⟨B, _, hBs, hBt⟩ := PartialIsometry.traceFree_orthogonal_sum b
    (by intro i j hij; rw [hbs, hbs]; exact hao hij)
    (by
      intro i j hij
      exact projection_orthogonal_of_le (ho hij)
        ((slot i).compose_target_le _ _) ((slot j).compose_target_le _ _))
  let oneP : AlgebraProjection M := ⟨1, IsStarProjection.one _⟩
  have hB1 : B.support = oneP := Subtype.ext (hatotal _ (fun n => by
    simpa only [hbs] using (hBs B.support).mp le_rfl n)).symm
  have hBp : B.target ≤ p := (hBt _).mpr hbt
  have hp1 : p ≤ oneP := by change 1 * p.val = p.val; exact one_mul _
  exact AlgebraProjection.equivalent_of_le_of_subequivalent hp1 ⟨B, hB1, hBp⟩

/-- Every nonzero projection in the concrete type III factor is the range
of an isometry in the same algebra. -/
theorem TypeIIIFactor.exists_isometry_onto_projection_of_projection_countability
    (hM : TypeIIIFactor M) (hFamilies : HasCountableProjectionFamilies M)
    (p : Algebra M) (hp : IsStarProjection p) (hne : p ≠ 0) :
    ∃ v : Algebra M, star v * v = 1 ∧ v * star v = p := by
  have hInfinite : ¬ FiniteProjectionIn M p := fun h => hne (hM.purelyInfinite p hp h)
  have he := projection_equivalent_one_of_not_finite_of_projection_countability
    hFamilies hM.factor ⟨p, hp⟩ hInfinite
  obtain ⟨v, hv, ht⟩ := AlgebraProjection.equivalent_symm he
  refine ⟨v.val, ?_, ?_⟩
  · exact v.initial.trans (congrArg Subtype.val hv)
  · exact congrArg Subtype.val ht

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIIProjectionCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Two-by-two coordinates for a nontrivial type III projection -/

namespace KadisonKastler

noncomputable section

open Generator.Tracial

variable {A : Type*} [CStarAlgebra A]

theorem isometry_cross_eq_zero (v w : A) (hv : star v * v = 1)
    (hw : star w * w = 1) (horth : (v * star v) * (w * star w) = 0) :
    star v * w = 0 := by
  calc
    star v * w = (star v * v) * (star v * w) * (star w * w) := by rw [hv, hw]; simp
    _ = star v * ((v * star v) * (w * star w)) * w := by noncomm_ring
    _ = 0 := by rw [horth, mul_zero, zero_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {N : VonNeumannAlgebra H}

theorem TypeIIIFactor.exists_projection_coordinates_of_projection_countability_oai
    (hN : TypeIIIFactor N) (hFamilies : HasCountableProjectionFamilies N)
    (p : AlgebraProjection N) (hp : p.val ≠ 0) (hq : p.val ≠ 1) :
    ∃ S : CuntzFamily (Fin 2) H, (∀ i, S.entry i ∈ N) ∧
      S.entry 0 * star (S.entry 0) = p.val.val ∧
      S.entry 1 * star (S.entry 1) = 1 - p.val.val := by
  obtain ⟨v, hv, hvp⟩ :=
    hN.exists_isometry_onto_projection_of_projection_countability hFamilies p.val p.property hp
  have hq0 : 1 - p.val ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  obtain ⟨w, hw, hwq⟩ := hN.exists_isometry_onto_projection_of_projection_countability
    hFamilies (1 - p.val) p.property.one_sub hq0
  have hvw : star v * w = 0 := isometry_cross_eq_zero v w hv hw (by
    rw [hvp, hwq]; exact p.property.mul_one_sub_self)
  have hwv : star w * v = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hvw
  let e : Fin 2 → Algebra N := ![v, w]
  have he (i j : Fin 2) : star (e i) * e j = if i = j then 1 else 0 := by
    fin_cases i <;> fin_cases j <;> simp [e, hv, hw, hvw, hwv]
  let S : CuntzFamily (Fin 2) H := {
    entry i := (e i).val
    orthogonal i j := by
      have hh := congrArg Subtype.val (he i j)
      split_ifs with hij
      · simpa only [ite_eq_left hij, MulMemClass.coe_mul, StarMemClass.coe_star,
          OneMemClass.coe_one] using hh
      · simpa only [ite_eq_right hij, MulMemClass.coe_mul, StarMemClass.coe_star,
          ZeroMemClass.coe_zero] using hh
    total := by
      have hh : v * star v + w * star w = 1 := by rw [hvp, hwq]; abel
      simpa only [Fin.sum_univ_two, e, Matrix.cons_val_zero, Matrix.cons_val_one,
        AddMemClass.coe_add, MulMemClass.coe_mul, StarMemClass.coe_star, OneMemClass.coe_one]
        using congrArg Subtype.val hh }
  refine ⟨S, fun i => (e i).property, ?_, ?_⟩
  · exact congrArg Subtype.val hvp
  · exact congrArg Subtype.val hwq

end

end KadisonKastler

end OAI
end

theorem solution.{u_2} : type_of% @OAI.KadisonKastler.TypeIIIFactor.exists_projection_coordinates_of_projection_countability_oai.{u_2} := @OAI.KadisonKastler.TypeIIIFactor.exists_projection_coordinates_of_projection_countability_oai.{u_2}
