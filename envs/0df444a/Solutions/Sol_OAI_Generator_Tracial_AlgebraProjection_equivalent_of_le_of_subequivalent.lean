-- Prove2me | solution 1 for OAI.Generator.Tracial.AlgebraProjection.equivalent_of_le_of_subequivalent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:59:53.761221+00:00
-- url     : https://prove2.me/submissions/a587bf99-084b-4f5f-99d8-335985a8435b

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Definitions.Def_Q260K009
import Definitions.Def_Q260K015

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionSchroederBernstein
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

private theorem defectOrbit_zero (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) :
    (defectOrbit v p ht hp 0).target = AlgebraProjection.remainder p v.support hp := by
  apply Subtype.ext
  change (v.val ^ 0 * _) * star (v.val ^ 0 * _) = _
  simp only [pow_zero, one_mul,
    (AlgebraProjection.remainder p v.support hp).property.isSelfAdjoint.star_eq,
    (AlgebraProjection.remainder p v.support hp).property.isIdempotentElem.eq]

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

/-- A projection between the initial and final projections of a partial
isometry is equivalent to the initial projection. This is the shift form
of projection Schroeder--Bernstein. -/
theorem equivalent_intermediate (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) : v.support.Equivalent p := by
  let a := defectOrbit v p ht hp
  let d := AlgebraProjection.remainder p v.support hp
  have ho : Pairwise (fun i j => (a i).target.val * (a j).target.val = 0) :=
    defectOrbit_orthogonal v p ht hp
  let b (i : ℕ) := rangeLink (a i) (a (i + 1)) rfl
  have hbs (i : ℕ) : (b i).support = (a i).target := rfl
  have hbt (i : ℕ) : (b i).target = (a (i + 1)).target := rangeLink_target _ _ _
  obtain ⟨s, _, hs, hs'⟩ := traceFree_orthogonal_sum b
    (by intro i j hij; rw [hbs, hbs]; exact ho hij)
    (by intro i j hij; rw [hbt, hbt]; exact ho (by omega))
  have hsle : s.support ≤ v.support := (hs _).mpr (fun i => by
    rw [hbs]
    exact defectOrbit_target_le v p ht hp i)
  have hst : s.target ≤ s.support := (hs' _).mpr (fun i => by
    rw [hbt, ← hbs (i + 1)]
    exact (hs s.support).mp le_rfl (i + 1))
  have hd0 : (a 0).target = d := defectOrbit_zero v p ht hp
  have hds : d ≤ s.support := by
    rw [← hd0, ← hbs 0]
    exact (hs s.support).mp le_rfl 0
  let c : AlgebraProjection M := ⟨1 - d.val, d.property.one_sub⟩
  have hsc : s.target ≤ c := (hs' c).mpr (fun i => by
    rw [hbt]
    change (1 - d.val) * (a (i + 1)).target.val = (a (i + 1)).target.val
    rw [sub_mul, one_mul, ← hd0, ho (by omega), sub_zero])
  have hdo : d.val * s.target.val = 0 := by
    change (1 - d.val) * s.target.val = s.target.val at hsc
    rw [sub_mul, one_mul] at hsc
    exact sub_eq_self.mp hsc
  have hsplit : s.support = orthogonalSum d s.target hdo := by
    apply le_antisymm
    · apply (hs _).mpr
      intro i
      rw [hbs]
      cases i with
      | zero => rw [hd0]; exact le_orthogonalSum_left _ _ hdo
      | succ i =>
        rw [← hbt i]
        exact ((hs' s.target).mp le_rfl i).trans
          (le_orthogonalSum_right _ _ hdo)
    · exact orthogonalSum_le hdo hds hst
  let e := AlgebraProjection.remainder s.support v.support hsle
  have hse : s.support.val * e.val = 0 :=
    AlgebraProjection.remainder_orthogonal _ _ hsle
  have hte : s.target.val * e.val = 0 :=
    projection_orthogonal_of_le hse hst le_rfl
  let z := s.patch (onProjection e) hse (by
    rw [onProjection_target]
    exact hte)
  refine ⟨z, ?_, ?_⟩
  · apply Subtype.ext
    change s.support.val + e.val = v.support.val
    change s.support.val + (v.support.val - s.support.val) = v.support.val
    abel
  · apply Subtype.ext
    have hz := s.patch_target (onProjection e) hse (by
      rw [onProjection_target]
      exact hte)
    have he := congrArg (fun q : AlgebraProjection M => s.target.val + q.val)
      (onProjection_target e)
    have hz' : z.target.val = s.target.val + e.val := hz.trans he
    refine hz'.trans ?_
    change s.target.val + (v.support.val - s.support.val) = p.val
    rw [hsplit]
    change s.target.val + (v.support.val - (d.val + s.target.val)) = p.val
    change s.target.val + (v.support.val - ((v.support.val - p.val) + s.target.val)) = p.val
    abel

end PartialIsometry

namespace AlgebraProjection

/-- Comparable projections satisfy Schroeder--Bernstein without any finite
trace or finite-isometry assumption. -/
theorem equivalent_of_le_of_subequivalent_oai {p q : AlgebraProjection M}
    (hpq : p ≤ q) (hqp : q.Subequivalent p) : p.Equivalent q := by
  obtain ⟨v, hv, ht⟩ := hqp
  exact equivalent_symm (by
    rw [← hv] at hpq ⊢
    exact v.equivalent_intermediate p ht hpq)

end AlgebraProjection

end

end Generator.Tracial

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.AlgebraProjection.equivalent_of_le_of_subequivalent_oai.{u_1} := @OAI.Generator.Tracial.AlgebraProjection.equivalent_of_le_of_subequivalent_oai.{u_1}
