-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.directEvalOpt_eq_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:32:45.292974+00:00
-- url     : https://prove2.me/submissions/5def530b-eecb-4239-9120-b70010fb46cb

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.directEvalOpt_eq_some_iff.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
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

theorem solution {params : _root_.MIPStarRE.QPBT.DirectLdParams} {degree : ℕ}
    (line : _root_.MIPStarRE.QPBT.DirectLineDesc params) (point : Fin params.m → _root_.MIPStarRE.QPBT.DirectScalarQ params)
    (coeffs : _root_.MIPStarRE.QPBT.DirectDegPoly params degree) (answer : _root_.MIPStarRE.QPBT.DirectScalarQ params) :
    _root_.MIPStarRE.QPBT.directEvalOpt line point coeffs = some answer ↔
      _root_.MIPStarRE.QPBT.DirectEvaluatesTo line coeffs point answer := by
  classical
  unfold _root_.MIPStarRE.QPBT.directEvalOpt
  split_ifs with hexists
  · simp only [Option.some.injEq]
    constructor
    · intro heq
      simpa [heq] using Classical.choose_spec hexists
    · intro heval
      obtain ⟨parameter, hparameter⟩ := heval.1
      exact ((Classical.choose_spec hexists).2 parameter hparameter).symm.trans
        (heval.2 parameter hparameter)
  · simp only [false_iff]
    exact fun heval => hexists ⟨answer, heval⟩
