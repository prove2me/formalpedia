-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:37:41.112882+00:00
-- url     : https://prove2.me/submissions/576d1daf-4efe-4394-8f19-1e323e1dae7e

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.outcomeWeight_eq_zero_of_invalid.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame

/- Source helpers from QPBT/Combining/ExtendedLineGame.lean. -/
/-!
# A direct-game strategy from supplied extended-line measurements

The input is an existing `ExtendedLinesWitness`, not an existence assertion
for that witness. Axis answers are restricted using its degree-support field;
diagonal answers are extended by zero coefficients. Point answers are the
scalar coarse-grainings of the supplied joint point measurements.

These are construction lemmas for the first paragraph of the proof of
`lem:qld-4-7`, not a proof of that lemma or of the existence of its input.
The remaining game-value estimates and the dependency on issue Dengnifer/MIPStarRE-QPBT-bak#119 are
recorded in `audits/2026-09-06_extended-line-game-244.md`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1402`
- Blueprint `lem:qld-4-7` and `rem:qld-4-7-divisibility`.
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame





























variable {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}



/-- All wrong-tag effects vanish: the measurement construction never uses the
game's wrong-format fallback answers. -/
theorem answerMeasurement_effect_eq_zero
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (question : _root_.MIPStarRE.QPBT.DirectLdQuestion params.extendedDirectLd)
    (answer : _root_.MIPStarRE.QPBT.DirectLdAnswer params.extendedDirectLd)
    (hanswer : _root_.MIPStarRE.QPBT.validDirectLdAnswer question.1 answer = false) :
    (_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines side question).effect answer = 0 := by
  classical
  rcases question with ⟨kind, question⟩
  cases kind <;> cases answer <;>
    simp_all [_root_.MIPStarRE.QPBT.validDirectLdAnswer, _root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement,
      _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess, _root_.LIDT.MIPStarRE.Quantum.Submeasurement.postprocess,
      _root_.MIPStarRE.QPBT.ExtendedLineGame.pointAnswer, _root_.MIPStarRE.QPBT.ExtendedLineGame.axisAnswer, _root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalAnswer]































end ExtendedLineGame

end

end MIPStarRE.QPBT

/-!
# A direct-game strategy from supplied extended-line measurements

The input is an existing `ExtendedLinesWitness`, not an existence assertion
for that witness. Axis answers are restricted using its degree-support field;
diagonal answers are extended by zero coefficients. Point answers are the
scalar coarse-grainings of the supplied joint point measurements.

These are construction lemmas for the first paragraph of the proof of
`lem:qld-4-7`, not a proof of that lemma or of the existence of its input.
The remaining game-value estimates and the dependency on issue Dengnifer/MIPStarRE-QPBT-bak#119 are
recorded in `audits/2026-09-06_extended-line-game-244.md`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1402`
- Blueprint `lem:qld-4-7` and `rem:qld-4-7-divisibility`.
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.ExtendedLineGame





























variable {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

theorem solution
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (questionA questionB : _root_.MIPStarRE.QPBT.DirectLdQuestion params.extendedDirectLd)
    (answerA answerB : _root_.MIPStarRE.QPBT.DirectLdAnswer params.extendedDirectLd)
    (hinvalid : _root_.MIPStarRE.QPBT.validDirectLdAnswer questionA.1 answerA = false ∨
      _root_.MIPStarRE.QPBT.validDirectLdAnswer questionB.1 answerB = false) :
    _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines) questionA questionB answerA answerB = 0 := by
  rcases hinvalid with hinvalid | hinvalid
  · have hzero := _root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement_effect_eq_zero lines .alice questionA answerA hinvalid
    change (inner ℂ (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) (_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron ((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .alice questionA).effect answerA)
        ((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .bob questionB).effect answerB)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting))).re = 0
    rw [hzero]
    simp [_root_.MIPStarRE.QPBT.heteroKron, _root_.MIPStarRE.QPBT.applyOperatorToState]
  · have hzero := _root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement_effect_eq_zero lines .bob questionB answerB hinvalid
    change (inner ℂ (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) (_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron ((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .alice questionA).effect answerA)
        ((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .bob questionB).effect answerB)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting))).re = 0
    rw [hzero]
    simp [_root_.MIPStarRE.QPBT.heteroKron, _root_.MIPStarRE.QPBT.applyOperatorToState]
