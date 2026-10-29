-- Prove2me | solution 1 for MIPStarRE.QPBT.SubLineWitness.one_sub_avgOver_xPointOverlap_le_at
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:27:30.954178+00:00
-- url     : https://prove2.me/submissions/7a2d6f1c-6eda-4305-8c13-bcc188ea879b

-- Generated proof for MIPStarRE.QPBT.SubLineWitness.one_sub_avgOver_xPointOverlap_le_at.
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
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_SubLineXDeficit
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Combining_ZEvalDeficit
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_CombinedLinesWitness_one_sub_X_overlap_restricted_le_at
import Theorems.Thm_MIPStarRE_QPBT_SubLineWitness_exists_avgOver_X_eq_mixture
import Theorems.Thm_MIPStarRE_QPBT_regroup_line_answer_sum_at

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Combining/SubLineXDeficit.lean. -/
/-!
# X-point subline averages

This directly indexed auxiliary construction follows the first consistency
route for combined lines. The question carrier, completed answer alphabet,
and corrected error convention retain their existing meanings.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

noncomputable section

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ δP : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
  {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ}



/-! ## The mixture form of a one-point sub-line average -/



/-- At a pair of line-point pairs, the `X`-point overlap is the overlap of the
evaluated pair-line measurement with the completed `X`-point measurement; the
`Z`-point of the second pair only labels the evaluation classes. -/
theorem xPointOverlap_eq_at (lines : _root_.MIPStarRE.QPBT.CombinedLinesWitness S points δP)
    (first second : _root_.MIPStarRE.QPBT.Placement)
    (w : _root_.MIPStarRE.QPBT.LinePointPairSample P) :
    _root_.MIPStarRE.QPBT.xPointOverlapAt lines first second ((w.1.1, w.2.1), w.1.2) =
      ∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
          (S.place first
            (((lines.T first.side w.1.1 w.2.1).postprocess fun fs =>
              (_root_.MIPStarRE.QPBT.evalOpt w.1.1 w.1.2 fs.1, _root_.MIPStarRE.QPBT.evalOpt w.2.1 w.2.2 fs.2)).effect o) *
            S.place second ((S.pointMeasExpOption second.side .X w.1.2).effect o.1)) :=
  (_root_.MIPStarRE.QPBT.regroup_line_answer_sum_at lines first second w.1.1 w.2.1 w.1.2 w.2.2
    (fun o1 _ => (S.pointMeasExpOption second.side .X w.1.2).effect o1)).symm




end

end MIPStarRE.QPBT

/-!
# X-point subline averages

This directly indexed auxiliary construction follows the first consistency
route for combined lines. The question carrier, completed answer alphabet,
and corrected error convention retain their existing meanings.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder



variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ δP : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
  {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ}



/-! ## The mixture form of a one-point sub-line average -/

theorem solution
    (sublines : _root_.MIPStarRE.QPBT.SubLineWitness P) (lines : _root_.MIPStarRE.QPBT.CombinedLinesWitness S points δP)
    (first second : _root_.MIPStarRE.QPBT.Placement) (hopposite : first.IsOpposite second) :
    1 - _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D (fun sample =>
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
        (fun t => _root_.MIPStarRE.QPBT.xPointOverlapAt lines first second (sample.2, _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
          (sample.1.base + t • sample.1.direction))))) ≤
      2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ) := by
  obtain ⟨components, hcomp, hmix⟩ :=
    _root_.MIPStarRE.QPBT.SubLineWitness.exists_avgOver_X_eq_mixture P sublines (_root_.MIPStarRE.QPBT.xPointOverlapAt lines first second)
  rw [hmix]
  have hsplit : _root_.LIDT.MIPStarRE.LDT.avgOver components (fun c => 1 -
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.restrictedLinePointDist P c.1 c.2.1)
        (_root_.MIPStarRE.QPBT.restrictedLinePointDist P c.1 c.2.2))
        (fun w => _root_.MIPStarRE.QPBT.xPointOverlapAt lines first second ((w.1.1, w.2.1), w.1.2))) =
      1 - _root_.LIDT.MIPStarRE.LDT.avgOver components (fun c =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.restrictedLinePointDist P c.1 c.2.1)
          (_root_.MIPStarRE.QPBT.restrictedLinePointDist P c.1 c.2.2))
          (fun w => _root_.MIPStarRE.QPBT.xPointOverlapAt lines first second ((w.1.1, w.2.1), w.1.2))) := by
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability components hcomp]
  rw [← hsplit]
  calc
    _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver components (fun _ =>
        2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ)) := by
      refine _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun c => ?_
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun w => _root_.MIPStarRE.QPBT.xPointOverlap_eq_at lines first second w]
      exact lines.one_sub_X_overlap_restricted_le_at first second hopposite c.1 c.1 c.2.1 c.2.2
    _ = _ := _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability components hcomp _
