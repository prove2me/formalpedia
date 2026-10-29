-- Prove2me | solution 1 for MIPStarRE.QPBT.directPolynomialPoint_consistencyDefect_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:36:27.556704+00:00
-- url     : https://prove2.me/submissions/40bc70e3-5f70-4e68-98b7-459e81c21f84

-- Generated proof for MIPStarRE.QPBT.directPolynomialPoint_consistencyDefect_eq.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Strategy
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_congr
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_uniform_question_outcome_equiv
import Theorems.Thm_MIPStarRE_QPBT_directCoordinatePointMeasurementB_effect_transport
import Theorems.Thm_MIPStarRE_QPBT_directLdtPointNonempty
import Theorems.Thm_MIPStarRE_QPBT_directPolynomialMeasurement_evaluation_effect

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Low-degree consistency defect transport

This module expresses the consistency conclusions of the low individual
degree theorem in the coordinates of the directly indexed game, without
changing their numerical bounds.  The point/polynomial and polynomial/point
conclusions are taken at a fixed tuple coordinate; the polynomial/polynomial
conclusion is global.

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



/-! ## The three LDT conclusions in direct coordinates -/

theorem solution
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D))
    (hS : S.IsProjective) (r : Fin D.k) :
    letI := D.toLDTFieldModel
    ∀ (G : _root_.LIDT.MIPStarRE.LDT.ProjMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA),
      _root_.MIPStarRE.QPBT.consistencyDefect
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
          (fun u a => _root_.MIPStarRE.QPBT.heteroKron
            ((_root_.MIPStarRE.QPBT.directPolynomialEvaluationMeasurement D G u).effect a) 1)
          (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1
            ((_root_.MIPStarRE.QPBT.directPointCoordinateMeasurementB D S r u).effect a)) S.ψ =
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point D.toLDTParameters))
          (_root_.MIPStarRE.QPBT.ldtPolynomialEvaluationLeft D G)
          (_root_.MIPStarRE.QPBT.ldtPointBPlaced D S hS r) S.ψ := by
  letI := D.toLDTFieldModel
  intro G
  calc
    _root_.MIPStarRE.QPBT.consistencyDefect
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron
          ((_root_.MIPStarRE.QPBT.directPolynomialEvaluationMeasurement D G u).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1
          ((_root_.MIPStarRE.QPBT.directPointCoordinateMeasurementB D S r u).effect a)) S.ψ =
      _root_.MIPStarRE.QPBT.consistencyDefect
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun u a => _root_.MIPStarRE.QPBT.ldtPolynomialEvaluationLeft D G
          (_root_.MIPStarRE.QPBT.directPointEquiv D u) (_root_.MIPStarRE.QPBT.directScalarEquiv D a))
        (fun u a => _root_.MIPStarRE.QPBT.ldtPointBPlaced D S hS r
          (_root_.MIPStarRE.QPBT.directPointEquiv D u) (_root_.MIPStarRE.QPBT.directScalarEquiv D a)) S.ψ := by
          apply _root_.MIPStarRE.QPBT.consistencyDefect_congr
          · intro u a
            unfold _root_.MIPStarRE.QPBT.ldtPolynomialEvaluationLeft
            congr 1
            exact _root_.MIPStarRE.QPBT.directPolynomialMeasurement_evaluation_effect D G u a
          · intro u a
            unfold _root_.MIPStarRE.QPBT.ldtPointBPlaced
            congr 1
            exact (_root_.MIPStarRE.QPBT.directCoordinatePointMeasurementB_effect_transport
              D S hS r u a).symm
    _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point D.toLDTParameters))
        (_root_.MIPStarRE.QPBT.ldtPolynomialEvaluationLeft D G)
        (_root_.MIPStarRE.QPBT.ldtPointBPlaced D S hS r) S.ψ :=
      _root_.MIPStarRE.QPBT.consistencyDefect_uniform_question_outcome_equiv
        (_root_.MIPStarRE.QPBT.directPointEquiv D) (_root_.MIPStarRE.QPBT.directScalarEquiv D)
        (_root_.MIPStarRE.QPBT.ldtPolynomialEvaluationLeft D G)
        (_root_.MIPStarRE.QPBT.ldtPointBPlaced D S hS r) S.ψ
