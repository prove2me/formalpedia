-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.reversed_axis_completed_defect_eq_read_defect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:08:28.276533+00:00
-- url     : https://prove2.me/submissions/92cda374-ce8d-467f-9665-fc5845d0278b

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.reversed_axis_completed_defect_eq_read_defect.
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
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_LinePointRejection
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_directEvalOpt_eq_some_iff
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_place_BB_prime_mul_AB_prime_prime_comm
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_stateQForm_pairState_eq_AB_prime_prime_BB_prime

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
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







/-- Restriction preserves evaluation when the discarded coefficients vanish. -/
theorem axisRead_eval (params : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (coeffs : _root_.MIPStarRE.QPBT.DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
    (hsupport : ∀ index, params.d < index.val → coeffs index = 0)
    (parameter : _root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd) :
      _root_.MIPStarRE.QPBT.evalCoefficient (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead params coeffs) parameter = _root_.MIPStarRE.QPBT.evalCoefficient coeffs parameter := by
  unfold _root_.MIPStarRE.QPBT.evalCoefficient _root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead
  refine Fintype.sum_of_injective (Fin.castLE (_root_.MIPStarRE.QPBT.ExtendedLineGame.axis_degree_le params))
    (Fin.castLE_injective _) _ (fun index => coeffs index * parameter ^ index.val)
    ?_ (fun _ => rfl)
  intro index hindex
  have hlarge : params.d < index.val := by
    by_contra hlarge
    exact hindex ⟨⟨index.val, by omega⟩, Fin.ext rfl⟩
  simp [hsupport index hlarge]













/-- Re-reading a canonical axis question preserves its line description. -/
theorem axis_description_canonical (params : _root_.MIPStarRE.QPBT.DirectLdParams) (sample : _root_.MIPStarRE.QPBT.DirectLdSpace params) :
    _root_.MIPStarRE.QPBT.directALineDescOf params (_root_.MIPStarRE.QPBT.directLdMap params .aline sample) =
      _root_.MIPStarRE.QPBT.directALineDescOf params sample := by
  simp [_root_.MIPStarRE.QPBT.directALineDescOf, _root_.MIPStarRE.QPBT.directLdMap, _root_.MIPStarRE.QPBT.lineRepMap_apply_self]







variable {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}







/-- Axis truncation preserves evaluation on every nonzero effect, directly by
the degree-support field of the supplied extended-line witness. -/
theorem axisRead_eval_of_effect_ne_zero
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (line : _root_.MIPStarRE.QPBT.DirectLineDesc params.extendedDirectLd) (hline : line.kind = .axis)
    (coeffs : _root_.MIPStarRE.QPBT.DirectDegPoly params.extendedDirectLd (params.m * params.d + 1))
    (heffect : (lines.Qline side line).effect coeffs ≠ 0)
    (parameter : _root_.MIPStarRE.QPBT.DirectScalarQ params.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.evalCoefficient (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead params coeffs) parameter = _root_.MIPStarRE.QPBT.evalCoefficient coeffs parameter := by
  apply _root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead_eval
  by_contra hsupport
  exact heffect (lines.axis_degree side line coeffs hline hsupport)



























end ExtendedLineGame

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective























































/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): the matrix-vector term in `consistencyDefect` is the state quadratic
form. -/
theorem consistency_term_eq_stateQForm {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm (M.mulVec ψ))).re =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  rfl



































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/DistanceTheorems/TensorSupport.lean. -/
/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective





/-- Formalization-only auxiliary lemma for Fact 4.26: products of left and right
placements evaluate as a Kronecker product. -/
theorem placed_product_stateQForm_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A 1 * _root_.MIPStarRE.QPBT.heteroKron 1 B) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A B) := by
  congr 1
  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor A B































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Combining/ExtendedLineGame/LinePointRejection.lean. -/
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
@[expose] public section
open scoped BigOperators MatrixOrder ComplexOrder

-- The six-register products use the same instance-search budget as StateTransport.
set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}









































private theorem axisGameRead_axisAnswer_eq_of_effect_ne_zero_bob
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)
    (coeffs : _root_.MIPStarRE.QPBT.DirectDegPoly P.extendedDirectLd (P.m * P.d + 1))
    (heffect : (lines.Qline .bob
      (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample)).effect coeffs ≠ 0) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisAnswer P coeffs) =
      (_root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
        (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P) := by
  change (_root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample) sample.point
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead P coeffs)).map (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P) = _
  have heval (parameter : _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
      _root_.MIPStarRE.QPBT.evalCoefficient (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead P coeffs) parameter = _root_.MIPStarRE.QPBT.evalCoefficient coeffs parameter :=
    _root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead_eval_of_effect_ne_zero lines .bob _ rfl coeffs heffect parameter
  apply congrArg (Option.map (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P))
  cases hfull : _root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample)
      sample.point coeffs with
  | none =>
      cases haxis : _root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample)
          sample.point (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead P coeffs) with
      | none => rfl
      | some answer =>
          have hspec := (_root_.MIPStarRE.QPBT.ExtendedLineGame.directEvalOpt_eq_some_iff _ _ _ _).1 haxis
          have hfull' : _root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample)
              sample.point coeffs = some answer := by
            apply (_root_.MIPStarRE.QPBT.ExtendedLineGame.directEvalOpt_eq_some_iff _ _ _ _).2
            exact ⟨hspec.1, fun parameter hparameter =>
              (heval parameter).symm.trans (hspec.2 parameter hparameter)⟩
          rw [hfull] at hfull'
          contradiction
  | some answer =>
      have hspec := (_root_.MIPStarRE.QPBT.ExtendedLineGame.directEvalOpt_eq_some_iff _ _ _ _).1 hfull
      have haxis : _root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample)
          sample.point (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead P coeffs) = some answer := by
        apply (_root_.MIPStarRE.QPBT.ExtendedLineGame.directEvalOpt_eq_some_iff _ _ _ _).2
        exact ⟨hspec.1, fun parameter hparameter =>
          (heval parameter).trans (hspec.2 parameter hparameter)⟩
      rw [haxis]

private theorem axis_read_effect_bob
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd) (answer : Option (_root_.MIPStarRE.QPBT.PauliScalar P)) :
    ((((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .bob
        (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)).postprocess
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample)).effect answer)) =
      (((lines.Qline .bob (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample)).postprocess
        (fun coeffs => (_root_.MIPStarRE.QPBT.directEvalOpt
          (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
            (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P))).effect answer) := by
  classical
  unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement
  rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.axis_description_canonical, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
  simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro coeffs _
  by_cases heffect : (lines.Qline .bob
      (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample)).effect coeffs = 0
  · simp [heffect]
  · rw [axisGameRead_axisAnswer_eq_of_effect_ne_zero_bob lines sample coeffs heffect]

/-- Alice's point readout is the corresponding postprocessed joint point effect.
Support for `lem:qld-4-7`, paper `14_analysis_of_the_pauli_basis_test.tex:1279-1288`. -/
theorem point_read_effect_alice
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd) (answer : Option (_root_.MIPStarRE.QPBT.PauliScalar P)) :
    ((((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .alice
        (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)).postprocess
      _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead).effect answer)) =
      (((points.Q .alice
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point))
        (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point))).postprocess fun values =>
          some (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point (_root_.MIPStarRE.QPBT.alphaVar P.m) * values.1 +
            _root_.MIPStarRE.QPBT.directPointToPauli P sample.point (_root_.MIPStarRE.QPBT.betaVar P.m) * values.2)).effect answer) := by
  classical
  unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement _root_.MIPStarRE.QPBT.CombinedPointsWitness.extendedQ
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
  rfl











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
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    _root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect lines .BB' .AB''
        (_root_.MIPStarRE.QPBT.directALinePointDist P.extendedDirectLd) =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd))
        (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron
          (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .alice
            (.point, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .point sample)).postprocess
              _root_.MIPStarRE.QPBT.ExtendedLineGame.pointGameRead).effect answer) 1)
        (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron 1
          (((_root_.MIPStarRE.QPBT.ExtendedLineGame.answerMeasurement lines .bob
            (.aline, _root_.MIPStarRE.QPBT.directLdMap P.extendedDirectLd .aline sample)).postprocess
              (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisGameRead sample)).effect answer))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) := by
  unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect _root_.MIPStarRE.QPBT.consistencyDefect
  rw [_root_.MIPStarRE.QPBT.directALinePointDist, _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro sample
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro answerA _
  apply Finset.sum_congr rfl
  intro answerB _
  by_cases hab : answerA = answerB
  · simp [hab]
  · have hba : answerB ≠ answerA := Ne.symm hab
    simp only [hab, hba, if_false, _root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm]
    let A : _root_.LIDT.MIPStarRE.Quantum.Op (setting.ExpandedLocalSpace .alice) :=
      ((points.Q .alice
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point))
        (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point))).postprocess fun values =>
          some (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point (_root_.MIPStarRE.QPBT.alphaVar P.m) * values.1 +
            _root_.MIPStarRE.QPBT.directPointToPauli P sample.point (_root_.MIPStarRE.QPBT.betaVar P.m) * values.2)).effect answerA
    let B : _root_.LIDT.MIPStarRE.Quantum.Op (setting.ExpandedLocalSpace .bob) :=
      ((lines.Qline .bob
        (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample)).postprocess fun coeffs =>
          (_root_.MIPStarRE.QPBT.directEvalOpt
            (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
              (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P)).effect answerB
    have hA : A.IsHermitian := by
      exact (Matrix.nonneg_iff_posSemidef.mp
        (((points.Q .alice
          (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point))
          (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point))).postprocess fun values =>
            some (_root_.MIPStarRE.QPBT.directPointToPauli P sample.point (_root_.MIPStarRE.QPBT.alphaVar P.m) * values.1 +
              _root_.MIPStarRE.QPBT.directPointToPauli P sample.point (_root_.MIPStarRE.QPBT.betaVar P.m) * values.2)).pos answerA)).isHermitian
    have hB : B.IsHermitian := by
      exact (Matrix.nonneg_iff_posSemidef.mp
        (((lines.Qline .bob
          (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample)).postprocess
            (fun coeffs => (_root_.MIPStarRE.QPBT.directEvalOpt
              (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
                (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P))).pos answerB)).isHermitian
    rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.point_read_effect_alice lines sample answerA, axis_read_effect_bob lines sample answerB,
      _root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq]
    change _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm setting.psiHat
        (setting.place .BB' B * setting.place .AB'' A) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) (_root_.MIPStarRE.QPBT.heteroKron A B)
    rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.place_BB_prime_mul_AB_prime_prime_comm]
    exact (_root_.MIPStarRE.QPBT.ExtendedLineGame.stateQForm_pairState_eq_AB_prime_prime_BB_prime setting A B hA hB).symm
