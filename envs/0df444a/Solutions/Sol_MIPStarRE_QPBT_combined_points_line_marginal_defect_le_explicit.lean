-- Prove2me | solution 1 for MIPStarRE.QPBT.combined_points_line_marginal_defect_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:17:59.671183+00:00
-- url     : https://prove2.me/submissions/acf103c4-0e65-47c9-80ce-f59b46ff506a

-- Generated proof for MIPStarRE.QPBT.combined_points_line_marginal_defect_le_explicit.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_conjTranspose
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_mul
import Theorems.Thm_MIPStarRE_QPBT_combined_points_line_marginal_distance_le_explicit
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_le_opFamilyDistSq_of_projective

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Combining/Lines/PointComparison.lean. -/
/-!
# Point and line marginal comparisons

Projection contraction and the original line-point law give the two marginal
comparisons used by the X-Z-X line construction.
The joint-point marginal estimates are imported through `Points` from
`Points.WitnessMarginals`, which retains the same statements and proofs.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions remain
as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section



























/-- Completing a joint answer and then taking its X marginal agrees with
completing the X marginal. This is a formalization-only postprocessing
identity for `eq:pasting-q1`; it is not an extra marginal hypothesis. -/
theorem CombinedPointsWitness.completed_fst_effect
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (x z : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (answer : Option (_root_.MIPStarRE.QPBT.PauliScalar P)) :
    (((points.Q side x z).postprocess (fun pair => (some pair.1, some pair.2))).postprocess
      Prod.fst).effect answer =
      (((points.Q side x z).postprocess Prod.fst).postprocess some).effect answer := by
  classical
  exact congrArg (fun meas => meas.effect answer)
    ((_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp (points.Q side x z)
      (fun pair => (some pair.1, some pair.2)) Prod.fst).trans
      (_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp (points.Q side x z) Prod.fst some).symm)

/-- Completing a joint answer and then taking its Z marginal agrees with
completing the Z marginal. Source: `eq:pasting-q1`, with the existing
completed evaluation convention. -/
theorem CombinedPointsWitness.completed_snd_effect
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (x z : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (answer : Option (_root_.MIPStarRE.QPBT.PauliScalar P)) :
    (((points.Q side x z).postprocess (fun pair => (some pair.1, some pair.2))).postprocess
      Prod.snd).effect answer =
      (((points.Q side x z).postprocess Prod.snd).postprocess some).effect answer := by
  classical
  exact congrArg (fun meas => meas.effect answer)
    ((_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp (points.Q side x z)
      (fun pair => (some pair.1, some pair.2)) Prod.snd).trans
      (_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp (points.Q side x z) Prod.snd some).symm)











end

end MIPStarRE.QPBT

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
# Point and line marginal comparisons

Projection contraction and the original line-point law give the two marginal
comparisons used by the X-Z-X line construction.
The joint-point marginal estimates are imported through `Points` from
`Points.WitnessMarginals`, which retains the same statements and proofs.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-963`,
blueprint `lem:qld-xz-lines`. The source and completed-answer distinctions remain
as documented in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

theorem solution
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε δQ : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ)
    (p1 p2 : _root_.MIPStarRE.QPBT.Placement) (hopp : p1.IsOpposite p2) :
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
          (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            ((((points.Q p1.side sample.1.2 sample.2.2).postprocess
              (fun pair => (some pair.1, some pair.2))).postprocess Prod.fst).effect answer))
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side .X sample.1.1 sample.1.2).effect answer))
          S.psiHat ≤ 8 * δQ + 2080 * (ε + _root_.MIPStarRE.QPBT.deltaLine ε) ∧
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
          (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams))
          (fun sample answer => S.place p1
            ((((points.Q p1.side sample.1.2 sample.2.2).postprocess
              (fun pair => (some pair.1, some pair.2))).postprocess Prod.snd).effect answer))
          (fun sample answer => S.place p2
            ((S.lineEvalMeasExp p2.side .Z sample.2.1 sample.2.2).effect answer))
          S.psiHat ≤ 8 * δQ + 2080 * (ε + _root_.MIPStarRE.QPBT.deltaLine ε) := by
  classical
  simp_rw [points.completed_fst_effect, points.completed_snd_effect]
  have hcompare (coordinate : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P → _root_.MIPStarRE.QPBT.PauliScalar P)
      (sampleLine : (_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) ×
        (_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) →
        _root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) (W : _root_.MIPStarRE.QPBT.PauliKind) :=
    _root_.MIPStarRE.QPBT.consistencyDefect_le_opFamilyDistSq_of_projective
      (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams) (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams))
      (fun sample => S.placedMeasurement p1
        (((points.Q p1.side sample.1.2 sample.2.2).postprocess coordinate).postprocess some))
      (fun sample => S.placedMeasurement p2
        (S.lineEvalMeasExp p2.side W (sampleLine sample).1 (sampleLine sample).2)) S.psiHat
      (fun sample => S.placedMeasurement_isProjective p1 _
        (_root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective _
          (_root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective _ (points.projective _ _ _) _) _))
      (fun sample => S.placedMeasurement_isProjective p2 _
        (_root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective _ (S.lineMeasExp_isProjective _ _ _) _))
  exact ⟨(hcompare Prod.fst Prod.fst .X).trans
      (_root_.MIPStarRE.QPBT.combined_points_line_marginal_distance_le_explicit P ε δQ S points p1 p2 hopp).1,
    (hcompare Prod.snd Prod.snd .Z).trans
      (_root_.MIPStarRE.QPBT.combined_points_line_marginal_distance_le_explicit P ε δQ S points p1 p2 hopp).2⟩
