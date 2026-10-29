-- Prove2me | solution 1 for MIPStarRE.QPBT.CombinedPointsWitness.ordered_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:21:09.186985+00:00
-- url     : https://prove2.me/submissions/29480e74-8384-47fb-89b4-2d1044b55d0d

-- Generated proof for MIPStarRE.QPBT.CombinedPointsWitness.ordered_dist_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_conjTranspose
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_mul
import Theorems.Thm_MIPStarRE_QPBT_extendedQ_spec
import Theorems.Thm_MIPStarRE_QPBT_projective_refinement_ordered_dist_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.CombinedPointsWitness
end MIPStarRE.QPBT.CombinedPointsWitness
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Combining/Points/PlacementSupport.lean. -/
/-!
# Placement calculus on the expanded state

This module records the algebra of the four register placements used by the
combining argument: a placement is a unital `*`-homomorphism, placements on
opposite register pairs commute, and the crosswise exchange of the two EPR
pairs of the expanded state carries the placement `AA'` to `AB''` and `BA''`
to `BB'` while fixing the expanded state.  The last fact transfers every
state-dependent distance between the two bipartition schemes of
`def:symmetric-equivalents` without assuming a symmetric strategy.

## References

The placements are those of `def:symmetric-equivalents`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.  The
placement module proves EPR-exchange invariance for the involution
`(A' B'')(A'' B')`, which fixes `A` and `B`, in
`ProjectiveSetting.reindexState_eprCrossSwap_psiHat`; its use for
`lem:qld-4-10` is analyzed in
`docs/paper-gaps/qpbt_linearity-theorem-quotation.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## Placements as reindexed tensor factors -/













/-! ## The placement is a unital `*`-homomorphism -/





















/-- A placed projective measurement is projective. -/
theorem placedMeasurement_isProjective (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (p : _root_.MIPStarRE.QPBT.Placement) {α : Type*} [Fintype α]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p.side))
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (S.placedMeasurement p M) := by
  intro a
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · change S.place p (M.effect a) * S.place p (M.effect a) =
      S.place p (M.effect a)
    rw [← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_mul, (hM a).isIdempotentElem.eq]
  · change star (S.place p (M.effect a)) = S.place p (M.effect a)
    rw [Matrix.star_eq_conjTranspose, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.place_conjTranspose,
      (hM a).isSelfAdjoint.isHermitian.eq]

end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

























































































/-- Formalization-only auxiliary lemma for Proposition 4.29: state-dependent
operator-family distance is symmetric. -/
theorem opFamilyDistSq_symm {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ B A ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, map_sub, LinearMap.sub_apply]
  rw [norm_sub_rev]

end MIPStarRE.QPBT.DistanceCalculus

/-!
# Ordered products selected by a global projective measurement

The point comparison of a projective measurement can be refined to its original
outcomes and composed with the two combined-point ordered-product estimates.
All bounds are on the actual expanded state and retain the complete outcome sum.

## References

`eq:qld-g-42` and `eq:qld-g-43`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1283-1300`.
These are auxiliary estimates for issue Dengnifer/MIPStarRE-QPBT-bak#513, not the global-pair
constructor.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus





open MIPStarRE.QPBT.CombinedPointsWitness

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ : ℝ}
    {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε} (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ)
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopposite : p1.IsOpposite p2)
    (R : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ (S.ExpandedLocalSpace p1.side))
    (hR : _root_.MIPStarRE.QPBT.Measurement.IsProjective R) (ev : _root_.MIPStarRE.QPBT.ExtendedPointQuestion P → Γ → _root_.MIPStarRE.QPBT.PauliScalar P)
    (eta : ℝ)
    (hpoint : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P))
      (fun x a => S.place p1 ((R.postprocess (ev x)).effect a))
      (fun x a => S.place p2
        ((points.extendedQ p2.side x.1.1 x.1.2 x.2.1 x.2.2).effect a)) S.psiHat ≤ eta) :
    (_root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P))
      (fun _ g => S.place p1 (R.effect g))
      (fun x g => S.place p1 (R.effect g) * S.place p2
        (∑ ab ∈ Finset.univ.filter (fun ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P =>
            x.2.1 * ab.1 + x.2.2 * ab.2 = ev x g),
          (S.pointMeasExp p2.side .X x.1.1).effect ab.1 *
            (S.pointMeasExp p2.side .Z x.1.2).effect ab.2)) S.psiHat ≤
        4 * eta + 8 * δQ) ∧
    (_root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P))
      (fun _ g => S.place p1 (R.effect g))
      (fun x g => S.place p1 (R.effect g) * S.place p2
        (∑ ab ∈ Finset.univ.filter (fun ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P =>
            x.2.1 * ab.1 + x.2.2 * ab.2 = ev x g),
          (S.pointMeasExp p2.side .Z x.1.2).effect ab.2 *
            (S.pointMeasExp p2.side .X x.1.1).effect ab.1)) S.psiHat ≤
        4 * eta + 8 * δQ) := by
  classical
  let A (x : _root_.MIPStarRE.QPBT.ExtendedPointQuestion P) := S.placedMeasurement p1
    (points.extendedQ p1.side x.1.1 x.1.2 x.2.1 x.2.2)
  let B (x : _root_.MIPStarRE.QPBT.ExtendedPointQuestion P) := S.placedMeasurement p2
    (points.extendedQ p2.side x.1.1 x.1.2 x.2.1 x.2.2)
  have hpoint' : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P))
      (fun x a => ((S.placedMeasurement p1 R).postprocess (ev x)).effect a)
      (fun x a => (B x).effect a) S.psiHat ≤ eta := by
    simpa only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, _root_.MIPStarRE.QPBT.ProjectiveSetting.placedMeasurement_effect,
      _root_.MIPStarRE.QPBT.ProjectiveSetting.place_finsetSum, B] using hpoint
  have hself : _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P))
      (fun x a => (B x).effect a) (fun x a => (A x).effect a) S.psiHat ≤ δQ := by
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_symm]
    exact (_root_.MIPStarRE.QPBT.extendedQ_spec points).2.1 p1 p2 hopposite
  have hbound := _root_.MIPStarRE.QPBT.projective_refinement_ordered_dist_le
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P)) (S.placedMeasurement p1 R)
    (S.placedMeasurement_isProjective p1 R hR) ev A B
  constructor
  · have h := hbound _ S.psiHat eta δQ δQ hpoint' hself
      ((_root_.MIPStarRE.QPBT.extendedQ_spec points).2.2.1 p1 p2 hopposite)
    simpa only [_root_.MIPStarRE.QPBT.ProjectiveSetting.placedMeasurement_effect,
      show 4 * eta + 4 * δQ + 4 * δQ = 4 * eta + 8 * δQ by ring] using h
  · have h := hbound _ S.psiHat eta δQ δQ hpoint' hself
      ((_root_.MIPStarRE.QPBT.extendedQ_spec points).2.2.2 p1 p2 hopposite)
    simpa only [_root_.MIPStarRE.QPBT.ProjectiveSetting.placedMeasurement_effect,
      show 4 * eta + 4 * δQ + 4 * δQ = 4 * eta + 8 * δQ by ring] using h
