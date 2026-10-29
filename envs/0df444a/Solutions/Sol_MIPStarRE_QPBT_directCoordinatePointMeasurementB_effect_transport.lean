-- Prove2me | solution 1 for MIPStarRE.QPBT.directCoordinatePointMeasurementB_effect_transport
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:15:21.80042+00:00
-- url     : https://prove2.me/submissions/59343144-098c-4ee8-a599-2ed3241374cd

-- Generated proof for MIPStarRE.QPBT.directCoordinatePointMeasurementB_effect_transport.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Consistency_State
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Questions
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Strategy
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# State conversion and direct point readout

This module contains the pure-state conversion and direct point-readout
portion of the low-degree consistency transport.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:393-458`
- `references/ldt-paper/test_definition.tex:180-202`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum



/-! ## Equality of the two consistency formulations -/

-- The following identities identify pure-state expectation with the
-- Euclidean quadratic form used in the consistency calculations below.  They
-- send a pure state to its Euclidean coordinate vector and identify the
-- quadratic form of that vector with evaluation in the associated density
-- state; they are stated for an arbitrary finite index type in
-- `MIPStarRE/QPBT/Games/DistanceTheorems/Support.lean`.




/-! ## Direct-strategy state and point readout -/

theorem solution
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k)
    (u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (a : _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    letI := D.toLDTFieldModel
    (((_root_.MIPStarRE.QPBT.directCoordinateProjStrat D S hS r).pointMeasurementB
      (_root_.MIPStarRE.QPBT.directPointEquiv D u)).outcome (_root_.MIPStarRE.QPBT.directScalarEquiv D a)) =
      ((S.B (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
        (fun answer => _root_.MIPStarRE.QPBT.directLdPointValuesOrZero D answer r)).effect a := by
  letI := D.toLDTFieldModel
  classical
  simp only [_root_.MIPStarRE.QPBT.directCoordinateProjStrat, _root_.MIPStarRE.QPBT.directCoordinatePointMeasurement,
    _root_.MIPStarRE.QPBT.directLdGame,
    _root_.LIDT.MIPStarRE.LDT.ProjMeas.postprocess, _root_.LIDT.MIPStarRE.LDT.SubMeas.postprocess_outcome,
    _root_.MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas_outcome,
    _root_.MIPStarRE.QPBT.directPointQuestionOf_directPointEquiv,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  congr 1
  ext answer
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  simpa only [_root_.MIPStarRE.QPBT.directPointAnswerReadout_eq] using
    (_root_.MIPStarRE.QPBT.directScalarEquiv D).injective.eq_iff
