-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.axis_parameter_evaluated_coefficient_defect_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:03:32.563906+00:00
-- url     : https://prove2.me/submissions/9ac35de6-9615-4d23-957e-99d55c68fca2

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.axis_parameter_evaluated_coefficient_defect_eq.
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_ParameterCompletion
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_ParameterEvaluatedLineBound
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_SameLineCoefficientBound
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_consistencyDefect_postprocess_eq_mismatch

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





















/-- Re-reading a canonical axis question preserves its line description. -/
theorem axis_description_canonical (params : _root_.MIPStarRE.QPBT.DirectLdParams) (sample : _root_.MIPStarRE.QPBT.DirectLdSpace params) :
    _root_.MIPStarRE.QPBT.directALineDescOf params (_root_.MIPStarRE.QPBT.directLdMap params .aline sample) =
      _root_.MIPStarRE.QPBT.directALineDescOf params sample := by
  simp [_root_.MIPStarRE.QPBT.directALineDescOf, _root_.MIPStarRE.QPBT.directLdMap, _root_.MIPStarRE.QPBT.lineRepMap_apply_self]







variable {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}



































end ExtendedLineGame

end

end MIPStarRE.QPBT

/-!
# Transport of the axis parameter-evaluation defect

The coefficient-evaluation defect for the same-axis branch equals the
parameter-evaluation defect of the supplied direct-game strategy. Both sample
the actual axis-line marginal and an independent uniform affine parameter.
Composing the strategy's answer map with coefficient extraction gives
`axisRead`. The degree-support field of the supplied line measurements also
identifies this truncated evaluation with the original coefficient evaluation.

These are formalization-only identities for the construction in the proof of
`lem:qld-4-7`; they neither construct the supplied witness nor prove the source
theorem.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#351.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : Real}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

theorem solution
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.axisParameterEvaluatedCoefficientDefect lines =
      _root_.MIPStarRE.QPBT.ExtendedLineGame.axisParameterEvaluationDefect lines := by
  classical
  let readAxis : _root_.MIPStarRE.QPBT.DirectLdAnswer P.extendedDirectLd →
      _root_.MIPStarRE.QPBT.DirectDegPoly P.extendedDirectLd P.d := fun answer =>
    match answer with
    | .alinePolys coefficients => coefficients ⟨0, by change 0 < 1; decide⟩
    | _ => 0
  let law := _root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd))
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
  have heffect (side : _root_.MIPStarRE.QPBT.PlayerSide) (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)
      (parameter value : _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
      ((((lines.Qline side (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample)).postprocess
          (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead P)).postprocess
            (fun coefficients => _root_.MIPStarRE.QPBT.evalCoefficient coefficients parameter)).effect value) =
        (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines side
          (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)).postprocess
            (fun answer => _root_.MIPStarRE.QPBT.evalCoefficient (readAxis answer) parameter)).effect value) := by
    unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement
    rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.axis_description_canonical]
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp,
      _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
    rfl
  have hmeasurement : _root_.MIPStarRE.QPBT.ExtendedLineGame.axisParameterEvaluatedCoefficientDefect lines =
      _root_.MIPStarRE.QPBT.consistencyDefect law
        (fun sample value => _root_.MIPStarRE.QPBT.heteroKron
          (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .alice
            (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample.1)).postprocess
              (fun answer => _root_.MIPStarRE.QPBT.evalCoefficient (readAxis answer) sample.2)).effect value) 1)
        (fun sample value => _root_.MIPStarRE.QPBT.heteroKron 1
          (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .bob
            (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample.1)).postprocess
              (fun answer => _root_.MIPStarRE.QPBT.evalCoefficient (readAxis answer) sample.2)).effect value))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) := by
    unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.axisParameterEvaluatedCoefficientDefect _root_.MIPStarRE.QPBT.consistencyDefect
    dsimp only [law]
    simp only [_root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod, _root_.MIPStarRE.QPBT.directALinePointDist,
      _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro sample
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro parameter
    apply Finset.sum_congr rfl
    intro valueA _
    apply Finset.sum_congr rfl
    intro valueB _
    rw [heffect .alice sample parameter valueA, heffect .bob sample parameter valueB]
  rw [hmeasurement]
  change _root_.MIPStarRE.QPBT.consistencyDefect law
      (fun sample value => _root_.MIPStarRE.QPBT.heteroKron
        ((((_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines).A
          (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample.1)).postprocess
            (fun answer => _root_.MIPStarRE.QPBT.evalCoefficient (readAxis answer) sample.2)).effect value) 1)
      (fun sample value => _root_.MIPStarRE.QPBT.heteroKron 1
        ((((_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines).B
          (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample.1)).postprocess
            (fun answer => _root_.MIPStarRE.QPBT.evalCoefficient (readAxis answer) sample.2)).effect value))
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines).ψ = _
  rw [_root_.MIPStarRE.QPBT.WinImplications.consistencyDefect_postprocess_eq_mismatch]
  unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.axisParameterEvaluationDefect
  simp only [law, _root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod, _root_.MIPStarRE.QPBT.directALinePointDist,
    _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
  rfl
