-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.aline_aline_rejection_le_axisParameterEvaluatedCoefficientDefect_add
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:08:28.034636+00:00
-- url     : https://prove2.me/submissions/ec492051-0de4-4514-8b9f-2d8cadae2188

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.aline_aline_rejection_le_axisParameterEvaluatedCoefficientDefect_add.
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_SameLineCoefficientBound
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_SameLineRejection
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_IsProbability_map
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_aline_aline_rejection_eq_axisCoefficientAnswerDefect
import Theorems.Thm_MIPStarRE_QPBT_SandwichProduct_consistencyDefect_codewords_le_evaluated_add
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_congr
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_postprocess_le
import Theorems.Thm_MIPStarRE_QPBT_directCoefficientCollision_avg_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame
namespace MIPStarRE.QPBT.SandwichProduct
end MIPStarRE.QPBT.SandwichProduct

/- Source helpers from QPBT/Combining/DirectLowDegree/CoefficientConsistency.lean. -/
/-!
# Consistency of direct coefficient measurements

This module lifts consistency of uniformly evaluated coefficient-vector POVMs
to consistency of their full coefficient outcomes.  The loss is the direct
univariate collision bound `degree / q`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:331-344`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1595-1603`
- Blueprint `lem:sandwich-codeword-defect`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-- The consistency defect of two coefficient-vector POVM families is at most
their consistency defect after evaluation at an independent uniform parameter,
plus `degree / q`.

This is a formalization-only specialization of
`SandwichProduct.consistencyDefect_codewords_le_evaluated_add`.  It applies to
arbitrary POVMs and retains all degrees, including `degree ≥ q`. -/
theorem consistencyDefect_directCoefficients_le_evaluated_add
    {X ιA ιB : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (degree : ℕ) (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X)
    (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.DirectDegPoly D degree) ιA)
    (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.DirectDegPoly D degree) ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB))
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) :
    _root_.MIPStarRE.QPBT.consistencyDefect μ
        (fun x coefficients => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect coefficients) 1)
        (fun x coefficients => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect coefficients)) ψ ≤
      _root_.MIPStarRE.QPBT.consistencyDefect
        (_root_.MIPStarRE.QPBT.Distribution.prod μ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D)))
        (fun xt value => _root_.MIPStarRE.QPBT.heteroKron
          (((A xt.1).postprocess
            (fun coefficients => _root_.MIPStarRE.QPBT.evalCoefficient coefficients xt.2)).effect value) 1)
        (fun xt value => _root_.MIPStarRE.QPBT.heteroKron 1
          (((B xt.1).postprocess
            (fun coefficients => _root_.MIPStarRE.QPBT.evalCoefficient coefficients xt.2)).effect value)) ψ +
        (degree : ℝ) / (D.q : ℝ) := by
  apply _root_.MIPStarRE.QPBT.SandwichProduct.consistencyDefect_codewords_le_evaluated_add
      μ A B ψ (fun coefficients t => _root_.MIPStarRE.QPBT.evalCoefficient coefficients t)
      ((degree : ℝ) / (D.q : ℝ)) hμ hψ
  · positivity
  · intro a b hne
    exact _root_.MIPStarRE.QPBT.directCoefficientCollision_avg_le D degree a b hne

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Geometry.lean. -/
/-!
# Geometry for the directly indexed low-degree game

This module defines the parameters, line carrier, and line-point distributions
for the directly indexed low-degree game.

## References

The line-point distributions originate in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`.
The directly indexed repair is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section





























/-! ## Finite direct-line carrier -/

































/-- The directly indexed axis-line/point law is probabilistic. -/
theorem directALinePointDist_isProbability (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    (_root_.MIPStarRE.QPBT.directALinePointDist D).IsProbability := by
  exact (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability (_root_.MIPStarRE.QPBT.DirectLdSpace D)).map _















end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/Sandwich/Support.lean. -/
/-! # Quantitative support for sandwiched measurements

This module develops the consistency and operator-distance estimates used
in the quantitative sandwich argument.

## References

Blueprint `lem:ld-sandwich` and `lem:ld-sandwich-measurement`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open DistanceCalculus

namespace SandwichProduct



















/-- Performing two outcome relabelings has the same effects as their
composition. This is the formalization-only identity
`lem:sandwich-postprocess-compose` used to align the coordinate marginals in
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:952-994`. It reads at a
single outcome the equality of the twice-relabeled measurement with the
measurement relabeled along the composite map. -/
theorem postprocess_postprocess_effect {α β γ ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (f : α → β) (g : β → γ) (c : γ) :
    ((M.postprocess f).postprocess g).effect c =
      (M.postprocess (fun a => g (f a))).effect c := by
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]













end SandwichProduct

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/ExtendedLineGame/SameLineCoefficientBound.lean. -/
/-!
# Coefficient bounds for same-line rejection

The exact axis-axis and diagonal-diagonal rejection identities are bounded by
evaluating the corresponding coefficient measurements at an independent
uniform affine parameter. The losses are the direct univariate collision terms
`d / q` and `md / q`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1595-1603`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#328.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : Real}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}





private theorem axisCoefficientAnswerDefect_le_raw
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) :
    @LE.le Real Real.instLE (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficientAnswerDefect lines)
      (_root_.MIPStarRE.QPBT.consistencyDefect ((_root_.MIPStarRE.QPBT.directALinePointDist P.extendedDirectLd).map Prod.fst)
        (fun line coefficients => _root_.MIPStarRE.QPBT.heteroKron
          (((lines.Qline .alice line).postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead P)).effect coefficients) 1)
        (fun line coefficients => _root_.MIPStarRE.QPBT.heteroKron 1
          (((lines.Qline .bob line).postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead P)).effect coefficients))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting)) := by
  let A := fun line => (lines.Qline .alice line).postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead P)
  let B := fun line => (lines.Qline .bob line).postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead P)
  let wrap : _root_.MIPStarRE.QPBT.DirectDegPoly P.extendedDirectLd P.d ->
      _root_.MIPStarRE.QPBT.DirectLdAnswer P.extendedDirectLd := fun coefficients =>
    @_root_.MIPStarRE.QPBT.DirectLdAnswer.alinePolys P.extendedDirectLd
      (fun _ index => coefficients index)
  have hwrap : (fun coefficients => wrap (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead P coefficients)) = _root_.MIPStarRE.QPBT.ExtendedLineGame.axisAnswer P := by
    funext coefficients
    dsimp [wrap, _root_.MIPStarRE.QPBT.ExtendedLineGame.axisAnswer]
  have h := _root_.MIPStarRE.QPBT.consistencyDefect_postprocess_le
    ((_root_.MIPStarRE.QPBT.directALinePointDist P.extendedDirectLd).map Prod.fst)
    A B (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) wrap
  have hEq : _root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficientAnswerDefect lines =
      _root_.MIPStarRE.QPBT.consistencyDefect ((_root_.MIPStarRE.QPBT.directALinePointDist P.extendedDirectLd).map Prod.fst)
        (fun line answer => _root_.MIPStarRE.QPBT.heteroKron (((A line).postprocess wrap).effect answer) 1)
        (fun line answer => _root_.MIPStarRE.QPBT.heteroKron 1 (((B line).postprocess wrap).effect answer))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) := by
    unfold _root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficientAnswerDefect
    apply _root_.MIPStarRE.QPBT.consistencyDefect_congr
    · intro line answer
      apply congrArg (fun effect => _root_.MIPStarRE.QPBT.heteroKron effect 1)
      rw [<- hwrap]
      simpa only [A] using
        (_root_.MIPStarRE.QPBT.SandwichProduct.postprocess_postprocess_effect
          (lines.Qline .alice line) (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead P) wrap answer).symm
    · intro line answer
      apply congrArg (fun effect => _root_.MIPStarRE.QPBT.heteroKron 1 effect)
      rw [<- hwrap]
      simpa only [B] using
        (_root_.MIPStarRE.QPBT.SandwichProduct.postprocess_postprocess_effect
          (lines.Qline .bob line) (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead P) wrap answer).symm
  rw [hEq]
  exact h







end ExtendedLineGame

end

end MIPStarRE.QPBT

/-!
# Coefficient bounds for same-line rejection

The exact axis-axis and diagonal-diagonal rejection identities are bounded by
evaluating the corresponding coefficient measurements at an independent
uniform affine parameter. The losses are the direct univariate collision terms
`d / q` and `md / q`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1595-1603`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#328.
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
    @LE.le Real Real.instLE
      (_root_.MIPStarRE.QPBT.directLdBranchRejectionProbability P.extendedDirectLd (_root_.MIPStarRE.QPBT.ExtendedLineGame.strategy lines)
        (.aline, .aline))
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisParameterEvaluatedCoefficientDefect lines +
        (P.d : Real) / (P.extendedDirectLd.q : Real)) := by
  rw [_root_.MIPStarRE.QPBT.ExtendedLineGame.aline_aline_rejection_eq_axisCoefficientAnswerDefect]
  calc
    _root_.MIPStarRE.QPBT.ExtendedLineGame.axisCoefficientAnswerDefect lines <=
        _root_.MIPStarRE.QPBT.consistencyDefect ((_root_.MIPStarRE.QPBT.directALinePointDist P.extendedDirectLd).map Prod.fst)
          (fun line coefficients => _root_.MIPStarRE.QPBT.heteroKron
            (((lines.Qline .alice line).postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead P)).effect coefficients) 1)
          (fun line coefficients => _root_.MIPStarRE.QPBT.heteroKron 1
            (((lines.Qline .bob line).postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead P)).effect coefficients))
          (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) := axisCoefficientAnswerDefect_le_raw lines
    _ <= _ := by
      have hProbability :
          ((_root_.MIPStarRE.QPBT.directALinePointDist P.extendedDirectLd).map Prod.fst).IsProbability :=
        (_root_.MIPStarRE.QPBT.directALinePointDist_isProbability P.extendedDirectLd).map _
      simpa [_root_.MIPStarRE.QPBT.ExtendedLineGame.axisParameterEvaluatedCoefficientDefect] using
        (_root_.MIPStarRE.QPBT.consistencyDefect_directCoefficients_le_evaluated_add
          P.extendedDirectLd P.d
          ((_root_.MIPStarRE.QPBT.directALinePointDist P.extendedDirectLd).map Prod.fst)
          (fun line => (lines.Qline .alice line).postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead P))
          (fun line => (lines.Qline .bob line).postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisRead P))
          (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting) hProbability (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState_norm setting))
