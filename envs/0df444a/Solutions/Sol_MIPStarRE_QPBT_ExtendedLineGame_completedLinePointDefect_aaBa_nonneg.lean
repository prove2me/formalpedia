-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect_aaBa_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:20:47.975984+00:00
-- url     : https://prove2.me/submissions/654c2c2a-78c2-45b1-8384-72579396bcea

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect_aaBa_nonneg.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_stateQForm_pairState_eq_AA_prime_BA_prime_prime

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





























/-- A positive semidefinite operator has nonnegative state quadratic form. This
is the formalization-only order fact `lem:distance-qform-nonnegative`, used for
the nonnegative overlap terms in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) {M : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hM : 0 ≤ M) :
    0 ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  calc
    0 = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ 0 := by simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
    _ ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hM ψ

























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

/-!
# Nonnegativity of combining-witness errors

This module derives nonnegativity of the error parameters supplied with the
combined point and extended line witnesses.  The point conclusion follows from
nonnegativity of state-dependent squared distance.  The line conclusion uses
the genuine bipartite POVMs underlying the completed line-point defect.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- Blueprint `lem:qld-4-10` and `lem:qld-4-13`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#335.
-/



open scoped BigOperators MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum





open MIPStarRE.QPBT.ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

theorem solution
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL)
    (mu : _root_.LIDT.MIPStarRE.LDT.Distribution
      (_root_.MIPStarRE.QPBT.DirectLineDesc P.extendedDirectLd ×
        (Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))) :
    0 ≤ _root_.MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect lines .AA' .BA'' mu := by
  let lineMeasurement :
      (_root_.MIPStarRE.QPBT.DirectLineDesc P.extendedDirectLd ×
        (Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)) →
        _root_.LIDT.MIPStarRE.Quantum.Measurement (Option (_root_.MIPStarRE.QPBT.PauliScalar P)) (setting.ExpandedLocalSpace .alice) :=
    fun sample =>
      (lines.Qline .alice sample.1).postprocess
        (fun coeffs => (_root_.MIPStarRE.QPBT.directEvalOpt sample.1 sample.2 coeffs).map
          (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P))
  let pointMeasurement :
      (_root_.MIPStarRE.QPBT.DirectLineDesc P.extendedDirectLd ×
        (Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)) →
        _root_.LIDT.MIPStarRE.Quantum.Measurement (Option (_root_.MIPStarRE.QPBT.PauliScalar P)) (setting.ExpandedLocalSpace .bob) :=
    fun sample =>
      (points.Q .bob
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P sample.2))
        (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P sample.2))).postprocess fun values =>
          some (_root_.MIPStarRE.QPBT.directPointToPauli P sample.2 (_root_.MIPStarRE.QPBT.alphaVar P.m) * values.1 +
            _root_.MIPStarRE.QPBT.directPointToPauli P sample.2 (_root_.MIPStarRE.QPBT.betaVar P.m) * values.2)
  change 0 ≤ _root_.MIPStarRE.QPBT.consistencyDefect mu
    (fun sample answer => setting.place .AA' ((lineMeasurement sample).effect answer))
    (fun sample answer => setting.place .BA'' ((pointMeasurement sample).effect answer))
    setting.psiHat
  unfold _root_.MIPStarRE.QPBT.consistencyDefect _root_.LIDT.MIPStarRE.LDT.avgOver
  refine Finset.sum_nonneg fun sample _ =>
    mul_nonneg (mu.nonnegative sample) ?_
  refine Finset.sum_nonneg fun answerA _ => ?_
  refine Finset.sum_nonneg fun answerB _ => ?_
  by_cases hab : answerA = answerB
  · simp [hab]
  · simp only [hab, if_false, _root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm]
    rw [← _root_.MIPStarRE.QPBT.ExtendedLineGame.stateQForm_pairState_eq_AA_prime_BA_prime_prime setting
      ((lineMeasurement sample).effect answerA)
      ((pointMeasurement sample).effect answerB)
      (Matrix.nonneg_iff_posSemidef.mp
        ((lineMeasurement sample).pos answerA)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp
        ((pointMeasurement sample).pos answerB)).isHermitian]
    exact _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting)
      (_root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg
        ((lineMeasurement sample).pos answerA)
        ((pointMeasurement sample).pos answerB))
