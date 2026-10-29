-- Prove2me | solution 1 for MIPStarRE.QPBT.SubLineWitness.avgOver_extendedPointOverlap_ge
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:34:37.546905+00:00
-- url     : https://prove2.me/submissions/252c98ca-4da4-45f0-b8c0-3f22abb9223a

-- Generated proof for MIPStarRE.QPBT.SubLineWitness.avgOver_extendedPointOverlap_ge.
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
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLines_Measurement
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLines_Overlap
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_SubLineWitness_avgOver_conditionalLaw
import Theorems.Thm_MIPStarRE_QPBT_SubLineWitness_extendedPointOverlap_ge
import Theorems.Thm_MIPStarRE_QPBT_avgOver_directLinePointDist_resample_parameter

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Consistency of the extended-line measurements

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

theorem solution {params : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {error pointError lineError : ℝ} {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error}
    {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting pointError}
    (sublines : _root_.MIPStarRE.QPBT.SubLineWitness params) (lines : _root_.MIPStarRE.QPBT.CombinedLinesWitness setting points lineError)
    (first second : _root_.MIPStarRE.QPBT.Placement) (hopposite : first.IsOpposite second) :
    _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D (_root_.MIPStarRE.QPBT.pairedSublineOverlap setting points lines first second) ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.directLinePointDist params.extendedDirectLd)
        (_root_.MIPStarRE.QPBT.extendedPointOverlap setting points lines sublines first second) := by
  rw [_root_.MIPStarRE.QPBT.avgOver_directLinePointDist_resample_parameter, ← sublines.extended_marginal,
    ← sublines.avgOver_conditionalLaw]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
  intro line
  unfold _root_.MIPStarRE.QPBT.pairedSublineOverlap
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_comm]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
  intro parameter
  have hpoint : line.base + parameter • line.direction ∈ line.pointSet := ⟨parameter, rfl⟩
  refine le_trans ?_ (sublines.extendedPointOverlap_ge lines first second hopposite line _ hpoint)
  apply le_of_eq
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro sample
  rw [(Finset.mem_filter.mp sample.property).2]
