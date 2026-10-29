-- Prove2me | solution 1 for MIPStarRE.QPBT.directPolynomialPolynomial_consistencyDefect_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:32:14.436955+00:00
-- url     : https://prove2.me/submissions/190eeae5-3b5f-4201-bb1c-f82ed028afd6

-- Generated proof for MIPStarRE.QPBT.directPolynomialPolynomial_consistencyDefect_eq.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Consistency_Measurements
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Consistency_State
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_congr
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_outcome_equiv

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
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) :
    letI := D.toLDTFieldModel
    ∀ (GA : _root_.LIDT.MIPStarRE.LDT.ProjMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιA)
      (GB : _root_.LIDT.MIPStarRE.LDT.ProjMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial D.toLDTParameters) S.ιB),
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (fun _ g => _root_.MIPStarRE.QPBT.heteroKron ((_root_.MIPStarRE.QPBT.directPolynomialMeasurement D GA).effect g) 1)
          (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 ((_root_.MIPStarRE.QPBT.directPolynomialMeasurement D GB).effect g))
          S.ψ =
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (fun _ g => _root_.MIPStarRE.QPBT.ldtPolynomialLeftPlaced D GA g)
          (fun _ g => _root_.MIPStarRE.QPBT.ldtPolynomialRightPlaced D GB g) S.ψ := by
  letI := D.toLDTFieldModel
  intro GA GB
  calc
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun _ g => _root_.MIPStarRE.QPBT.heteroKron ((_root_.MIPStarRE.QPBT.directPolynomialMeasurement D GA).effect g) 1)
        (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 ((_root_.MIPStarRE.QPBT.directPolynomialMeasurement D GB).effect g))
        S.ψ =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun _ g => _root_.MIPStarRE.QPBT.ldtPolynomialLeftPlaced D GA (_root_.MIPStarRE.QPBT.directPolyEquivPolynomial D g))
        (fun _ g => _root_.MIPStarRE.QPBT.ldtPolynomialRightPlaced D GB (_root_.MIPStarRE.QPBT.directPolyEquivPolynomial D g))
        S.ψ := by
          apply _root_.MIPStarRE.QPBT.consistencyDefect_congr
          · intro _ g
            unfold _root_.MIPStarRE.QPBT.ldtPolynomialLeftPlaced
            rw [_root_.MIPStarRE.QPBT.directPolynomialMeasurement_effect]
          · intro _ g
            unfold _root_.MIPStarRE.QPBT.ldtPolynomialRightPlaced
            rw [_root_.MIPStarRE.QPBT.directPolynomialMeasurement_effect]
    _ = _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun _ g => _root_.MIPStarRE.QPBT.ldtPolynomialLeftPlaced D GA g)
        (fun _ g => _root_.MIPStarRE.QPBT.ldtPolynomialRightPlaced D GB g) S.ψ :=
      _root_.MIPStarRE.QPBT.consistencyDefect_outcome_equiv (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (_root_.MIPStarRE.QPBT.directPolyEquivPolynomial D)
        (fun _ g => _root_.MIPStarRE.QPBT.ldtPolynomialLeftPlaced D GA g)
        (fun _ g => _root_.MIPStarRE.QPBT.ldtPolynomialRightPlaced D GB g) S.ψ
