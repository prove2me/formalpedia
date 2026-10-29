-- Prove2me | solution 1 for MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_distance_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:02:02.004354+00:00
-- url     : https://prove2.me/submissions/88693f0d-5e72-46ab-83fc-66a192b743e7

-- Generated proof for MIPStarRE.QPBT.CombinedPointsWitness.marginal_X_distance_le.
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
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_comm
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_conjTranspose
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_mul
import Theorems.Thm_MIPStarRE_QPBT_norm_marginal_sub_sq_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
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

/-!
# Marginal distances for combined point witnesses

This module applies the generic marginal contraction estimate to the combined
point measurements of `lem:qld-4-10`. The X marginal uses the ordered
Z-then-X consistency relation, while the Z marginal uses the ordered
X-then-Z relation; no commutation of point effects on one player is assumed.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:914-930`:
the two marginal displays inside the proof of `lem:qld-xz-lines`, namely
`eq:qld-qxz-close-to-point` at lines 914--917 with its supporting calculation
at lines 918--927, and the symmetric `eq:qld-qxz-close-to-point-2` at lines
928--930.  The line-measurement-to-point consistency bounds at lines 931--935
are a separate later step of that proof and are not formalized here.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

set_option maxHeartbeats 800000 in

theorem solution
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ)
    (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopp : p1.IsOpposite p2) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
        ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))
      (fun xz a => ∑ b, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
      (fun xz a => S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a))
      S.psiHat ≤ 4 * δQ := by
  classical
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (points.consistent_ZX p1 p2 hopp)
    (by norm_num : (0 : ℝ) ≤ 4))
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
  intro xz
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  simpa only [_root_.MIPStarRE.QPBT.ProjectiveSetting.placedMeasurement_effect, _root_.MIPStarRE.QPBT.ProjectiveSetting.place_mul] using
    _root_.MIPStarRE.QPBT.norm_marginal_sub_sq_le
    (fun b => S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
    (fun b => S.placedMeasurement_isProjective p1 _ (points.projective _ _ _) (a, b))
    (fun hbc => _root_.MIPStarRE.QPBT.DistanceCalculus.projective_effect_mul_effect_eq_zero
      (S.placedMeasurement p1 (points.Q p1.side xz.1 xz.2))
      (S.placedMeasurement_isProjective p1 _ (points.projective _ _ _))
      (fun hpair => hbc (congrArg Prod.snd hpair)))
    (S.placedMeasurement p2 (S.pointMeasExp p2.side .Z xz.2))
    (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
    (fun b => S.place_comm p1 p2 hopp _ _)
    (S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a)) S.psiHat
