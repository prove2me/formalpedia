-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.diagonalGameRead_diagonalAnswer_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:42:28.462033+00:00
-- url     : https://prove2.me/submissions/30940c3f-4e71-4df6-9d96-816d3282e788

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.diagonalGameRead_diagonalAnswer_eq.
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
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_LinePointRejection
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Observables_Defs
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









/-- The extended-line degree fits the direct game's diagonal answer bound. -/
theorem diagonal_degree_le (params : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    params.m * params.d + 2 ≤
      params.extendedDirectLd.m * params.extendedDirectLd.d + 1 := by
  change params.m * params.d + 2 ≤ (2 * params.m + 2) * params.d + 1
  have hdegree := params.hd
  nlinarith



/-- Extending a diagonal answer by zeros preserves evaluation at every parameter. -/
theorem diagonalRead_eval (params : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (coeffs : _root_.MIPStarRE.QPBT.DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
    (parameter : _root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.evalCoefficient (_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalRead params coeffs) parameter =
      _root_.MIPStarRE.QPBT.evalCoefficient coeffs parameter := by
  symm
  apply Fintype.sum_of_injective (Fin.castLE (_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonal_degree_le params))
    (Fin.castLE_injective _) _ _ ?_ ?_
  · intro index hindex
    have hlarge : ¬index.val < params.m * params.d + 2 := by
      intro hsmall
      exact hindex ⟨⟨index.val, hsmall⟩, Fin.ext rfl⟩
    simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalRead, hlarge]
  · intro index
    simp [_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalRead, index.isLt]















variable {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}



































end ExtendedLineGame

end

end MIPStarRE.QPBT

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
    (coeffs : _root_.MIPStarRE.QPBT.DirectDegPoly P.extendedDirectLd (P.m * P.d + 1)) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalGameRead sample (_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalAnswer P coeffs) =
      (_root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directDLineDescOf P.extendedDirectLd sample) sample.point coeffs).map
        (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P) := by
  change (_root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directDLineDescOf P.extendedDirectLd sample) sample.point
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalRead P coeffs)).map (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P) = _
  have heval (parameter : _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
      _root_.MIPStarRE.QPBT.evalCoefficient (_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalRead P coeffs) parameter = _root_.MIPStarRE.QPBT.evalCoefficient coeffs parameter :=
    _root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalRead_eval P coeffs parameter
  apply congrArg (Option.map (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P))
  cases hfull : _root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directDLineDescOf P.extendedDirectLd sample)
      sample.point coeffs with
  | none =>
      cases hdiagonal : _root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directDLineDescOf P.extendedDirectLd sample)
          sample.point (_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalRead P coeffs) with
      | none => rfl
      | some answer =>
          have hspec := (_root_.MIPStarRE.QPBT.ExtendedLineGame.directEvalOpt_eq_some_iff _ _ _ _).1 hdiagonal
          have hfull' : _root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directDLineDescOf P.extendedDirectLd sample)
              sample.point coeffs = some answer := by
            apply (_root_.MIPStarRE.QPBT.ExtendedLineGame.directEvalOpt_eq_some_iff _ _ _ _).2
            exact ⟨hspec.1, fun parameter hparameter =>
              (heval parameter).symm.trans (hspec.2 parameter hparameter)⟩
          rw [hfull] at hfull'
          contradiction
  | some answer =>
      have hspec := (_root_.MIPStarRE.QPBT.ExtendedLineGame.directEvalOpt_eq_some_iff _ _ _ _).1 hfull
      have hdiagonal : _root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directDLineDescOf P.extendedDirectLd sample)
          sample.point (_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalRead P coeffs) = some answer := by
        apply (_root_.MIPStarRE.QPBT.ExtendedLineGame.directEvalOpt_eq_some_iff _ _ _ _).2
        exact ⟨hspec.1, fun parameter hparameter =>
          (heval parameter).trans (hspec.2 parameter hparameter)⟩
      rw [hdiagonal]
