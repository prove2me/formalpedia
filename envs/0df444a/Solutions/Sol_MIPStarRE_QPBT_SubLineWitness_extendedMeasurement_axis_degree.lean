-- Prove2me | solution 1 for MIPStarRE.QPBT.SubLineWitness.extendedMeasurement_axis_degree
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:03:55.398644+00:00
-- url     : https://prove2.me/submissions/84340979-aa35-4cb0-ae7f-b67a89dcb9eb

-- Generated proof for MIPStarRE.QPBT.SubLineWitness.extendedMeasurement_axis_degree.
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
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLines_Measurement
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Restriction
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_SubLineWitness_affineData_axis
import Theorems.Thm_MIPStarRE_QPBT_combineLinePoly_axis_degree

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Combining/ExtendedLines/Measurement.lean. -/
/-!
# Conditional extended-line measurements

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













































/-- The actual polynomial combination preserves the source axis-degree support. -/
theorem SubLineWitness.combinedPolynomial_axis_degree {params : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (sublines : _root_.MIPStarRE.QPBT.SubLineWitness params) (sample : _root_.MIPStarRE.QPBT.SubLineTriple params)
    (hsample : sample ∈ sublines.D.support) (haxis : sample.1.kind = .axis)
    (polynomials : _root_.MIPStarRE.QPBT.DegPoly params.toLdParams (params.m * params.d) ×
      _root_.MIPStarRE.QPBT.DegPoly params.toLdParams (params.m * params.d))
    (hdegreeX : polynomials.1.FitsDegree params.d)
    (hdegreeZ : polynomials.2.FitsDegree params.d) :
    ∀ index, params.d < index.val →
      sublines.combinedPolynomial sample hsample polynomials index = 0 := by
  intro index hindex
  have hzero := _root_.MIPStarRE.QPBT.combineLinePoly_axis_degree params.hd (sublines.affineData sample hsample)
    polynomials.1 polynomials.2 hdegreeX hdegreeZ
    (sublines.affineData_axis sample hsample haxis) index hindex
  change (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv params).symm _ = 0
  erw [hzero]
  exact map_zero _




end

end MIPStarRE.QPBT

/-!
# Conditional extended-line measurements

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
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (line : _root_.MIPStarRE.QPBT.DirectLineDesc params.extendedDirectLd)
    (polynomial : _root_.MIPStarRE.QPBT.DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
    (haxis : line.kind = .axis) (hdegree : ¬ ∀ index, params.d < index.val → polynomial index = 0) :
    (sublines.extendedMeasurement lines side line).effect polynomial = 0 := by
  classical
  change _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution (sublines.conditionalLaw line) (fun sample =>
    ((lines.T side sample.val.2.1 sample.val.2.2).postprocess
      (sublines.combinedPolynomial sample.val
        (Finset.mem_filter.mp sample.property).1)).effect polynomial) = 0
  unfold _root_.LIDT.MIPStarRE.LDT.averageOperatorOverDistribution
  apply Finset.sum_eq_zero
  intro sample _
  have hsample := (Finset.mem_filter.mp sample.property).1
  have hsampleAxis : sample.val.1.kind = .axis := by
    rw [(Finset.mem_filter.mp sample.property).2]
    exact haxis
  have hsource := sublines.axis_closure sample.val hsample hsampleAxis
  suffices hzero : ((lines.T side sample.val.2.1 sample.val.2.2).postprocess
      (sublines.combinedPolynomial sample.val hsample)).effect polynomial = 0 by
    exact (congrArg (fun operator => (sublines.conditionalLaw line).weight sample • operator)
      hzero).trans (smul_zero _)
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  apply Finset.sum_eq_zero
  intro pair hpair
  by_cases hdegreeX : pair.1.FitsDegree params.d
  · by_cases hdegreeZ : pair.2.FitsDegree params.d
    · have hfit := sublines.combinedPolynomial_axis_degree sample.val hsample hsampleAxis
        pair hdegreeX hdegreeZ
      rw [(Finset.mem_filter.mp hpair).2] at hfit
      exact (hdegree hfit).elim
    · exact lines.axis_degree_Z side _ _ _ _ hsource.2 hdegreeZ
  · exact lines.axis_degree_X side _ _ _ _ hsource.1 hdegreeX
