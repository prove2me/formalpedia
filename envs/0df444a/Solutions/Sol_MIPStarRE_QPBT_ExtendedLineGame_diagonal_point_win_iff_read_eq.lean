-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.diagonal_point_win_iff_read_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:42:28.622811+00:00
-- url     : https://prove2.me/submissions/3425f079-991f-4b2d-ac8d-85f8c8be813d

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.diagonal_point_win_iff_read_eq.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_LinePointRejection
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_directEvalOpt_eq_some_iff

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame

/-!
# Line/point rejection for the extended direct game

This module identifies the axis-line/point, diagonal-line/point, and reversed
point/axis-line branch rejections of the strategy constructed from an
`ExtendedLinesWitness` with the corresponding completed line-point defects.
These are finite postprocessing and state-transport steps in the first
paragraph of the proof of `lem:qld-4-7`; they do not establish a passing-value
bound or construct the supplied witness.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issues #302, #305, #307, and #309.
-/

open scoped BigOperators MatrixOrder ComplexOrder

-- The six-register products use the same instance-search budget as StateTransport.
set_option synthInstance.maxSize 400

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

theorem solution
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)
    (coeffs : Fin P.extendedDirectLd.k →
      Fin (P.extendedDirectLd.m * P.extendedDirectLd.d + 1) →
        _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)
    (values : Fin P.extendedDirectLd.k → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.directLdWinPredicate P.extendedDirectLd
        (.dline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .dline sample)
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)
        (.dlinePolys coeffs) (.pointVals values) = true ↔
      _root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalGameRead sample (.dlinePolys coeffs) = _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead (.pointVals values) := by
  let line := _root_.MIPStarRE.QPBT.directDLineDescOf P.extendedDirectLd sample
  have hmem : sample.point ∈ line.pointSet := by
    simpa [line, _root_.MIPStarRE.QPBT.DirectLineDesc.pointSet, _root_.MIPStarRE.QPBT.directDLineDescOf,
      _root_.MIPStarRE.QPBT.DirectLineDesc.base, _root_.MIPStarRE.QPBT.DirectLineDesc.direction] using
      (_root_.MIPStarRE.QPBT.mem_linePoints_lineRepMap
        (_root_.MIPStarRE.QPBT.directPrefixProjection sample.index sample.direction) sample.point)
  constructor
  · intro hwin
    have heval : _root_.MIPStarRE.QPBT.DirectEvaluatesTo line (coeffs _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate) sample.point
        (values _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate) := by
      refine ⟨hmem, ?_⟩
      intro parameter hparameter
      have hcondition : _root_.MIPStarRE.QPBT.directDlinePointCondition P.extendedDirectLd
          (_root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .dline sample)
          (_root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample) coeffs values := by
        simpa [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer] using hwin
      exact hcondition parameter (by
        simpa [line, _root_.MIPStarRE.QPBT.directDLineDescOf, _root_.MIPStarRE.QPBT.directLdMap, _root_.MIPStarRE.QPBT.DirectLineDesc.base,
          _root_.MIPStarRE.QPBT.DirectLineDesc.direction] using hparameter) _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate
    have hopt : _root_.MIPStarRE.QPBT.directEvalOpt line sample.point (coeffs _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate) =
        some (values _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate) :=
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.directEvalOpt_eq_some_iff line sample.point (coeffs _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate)
        (values _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate)).2 heval
    simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalGameRead, _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead, line, hopt]
  · intro hread
    have hopt : _root_.MIPStarRE.QPBT.directEvalOpt line sample.point (coeffs _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate) =
        some (values _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate) := by
      cases h : _root_.MIPStarRE.QPBT.directEvalOpt line sample.point (coeffs _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate) with
      | none => simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalGameRead, _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead, line, h] at hread
      | some value =>
          have hvalue : value = values _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate := by
            apply (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P).injective
            simpa [_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalGameRead, _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead, line, h] using hread
          subst value
          rfl
    have heval := (_root_.MIPStarRE.QPBT.ExtendedLineGame.directEvalOpt_eq_some_iff line sample.point
      (coeffs _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate) (values _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate)).1 hopt
    simp only [_root_.MIPStarRE.QPBT.directLdWinPredicate, _root_.MIPStarRE.QPBT.validDirectLdAnswer, Bool.and_self,
      ↓reduceIte, decide_eq_true_eq]
    intro parameter hparameter index
    have hindex : index = _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate := by
      have hlt : index.val < 1 := index.isLt
      have hzero : (_root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate (P := P)).val = 0 := rfl
      apply Fin.ext
      rw [hzero]
      omega
    subst index
    exact heval.2 parameter (by
      simpa [line, _root_.MIPStarRE.QPBT.directDLineDescOf, _root_.MIPStarRE.QPBT.directLdMap, _root_.MIPStarRE.QPBT.DirectLineDesc.base,
        _root_.MIPStarRE.QPBT.DirectLineDesc.direction] using hparameter)
