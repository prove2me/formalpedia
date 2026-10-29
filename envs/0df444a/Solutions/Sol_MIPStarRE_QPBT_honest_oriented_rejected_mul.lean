-- Prove2me | solution 1 for MIPStarRE.QPBT.honest_oriented_rejected_mul
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:09:25.097448+00:00
-- url     : https://prove2.me/submissions/d9ff9138-2562-4e1c-833d-3b1f2fd9e077

-- Generated proof for MIPStarRE.QPBT.honest_oriented_rejected_mul.
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Restriction
import Definitions.Def_QPBT_QPBT_Test_Completeness_Commutation
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy_MeasurementFamily
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_isProj_kronecker
import Theorems.Thm_MIPStarRE_QPBT_evalCoefficient_restrictToAxisLine_lowDegreeEncoding
import Theorems.Thm_MIPStarRE_QPBT_honestMeasurement_aline_eq
import Theorems.Thm_MIPStarRE_QPBT_honestMeasurement_dline_eq
import Theorems.Thm_MIPStarRE_QPBT_honest_dlinePointCondition
import Theorems.Thm_MIPStarRE_QPBT_honest_pairW_pair_rejected_mul
import Theorems.Thm_MIPStarRE_QPBT_honest_point_msVar_X_rejected_mul
import Theorems.Thm_MIPStarRE_QPBT_honest_point_msVar_Z_rejected_mul
import Theorems.Thm_MIPStarRE_QPBT_placedPauliMeasurement_postprocess_eq
import Theorems.Thm_MIPStarRE_QPBT_postprocess_effect_mul_eq_zero_of_incompatible

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Completeness/HonestStrategy/MeasurementFamily.lean. -/
/-!
# The honest Pauli measurement family

This module collects the measurements of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy` into a single measurement
family indexed by the question type of the Pauli basis test.  Each honest
measurement acts on the tensor product of the Pauli register with the qubit
supplied to the Magic Square construction, and every outcome is relabelled into
the common answer alphabet of the test.  The results recorded here are the
projectivity and the symmetry of every effect of that family.

## References

The measurement family described here is the one displayed in the proof of
`lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1237-1360`;
blueprint `lem:pauli-completeness`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ### Tensor placement and relabeling -/











/-- Placing a projective measurement on the first tensor factor preserves
projectivity. -/
theorem leftPlacedMeasurement_projective {α V W : Type*}
    [Fintype α] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α V) (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective
      (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := W) M) := by
  intro a
  exact _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.isProj_kronecker
    (hM a) (IsStarProjection.one _)















/-- Incompatible coarse-grained outcomes of two measurements on the Pauli
register have zero product after tensor placement. -/
theorem placedPauliMeasurement_mul_eq_zero_of_incompatible {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {ζ : Type*} [Fintype ζ] [DecidableEq ζ]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement ζ (_root_.MIPStarRE.QPBT.PauliRegister P))
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M)
    (f g : ζ → _root_.MIPStarRE.QPBT.PauliAnswer P)
    (a b : _root_.MIPStarRE.QPBT.PauliAnswer P)
    (hbad : ∀ h, f h = a → g h = b → False) :
    (_root_.MIPStarRE.QPBT.placedPauliMeasurement M f).effect a *
        (_root_.MIPStarRE.QPBT.placedPauliMeasurement M g).effect b = 0 := by
  change ((_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess f).effect a *
      ((_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess g).effect b = 0
  exact _root_.MIPStarRE.QPBT.postprocess_effect_mul_eq_zero_of_incompatible
    (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M)
    (_root_.MIPStarRE.QPBT.leftPlacedMeasurement_projective M hM) f g a b hbad





/-! ### The total honest measurement family -/









































end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Completeness/Rejection.lean. -/
/-!
# Rejection of wrong answers by the honest Pauli measurements

This module shows that the honest measurement family of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy.MeasurementFamily` assigns the zero
operator product to every answer pair rejected by the Pauli win predicate on a
question pair of positive weight for the Pauli question sampler.  Together with
the normalisation of the Born weights this yields the value-one assertion of
`lem:pauli-completeness`.

## References

Blueprint `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1383-1421`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

set_option maxRecDepth 8000

/-! ### Answers of an inadmissible form -/

















/-! ### Coordinate invariants of the typed Pauli conditionally linear maps -/



/-- The point block of a Point/W question is the point block of the ambient
coefficient vector; `def:pauli-question-distribution`. -/
theorem pauliPointBlock_pauliCL_point (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.pauliPointBlock W (_root_.MIPStarRE.QPBT.pauliCL P (.point W) z) = _root_.MIPStarRE.QPBT.pauliPointBlock W z := by
  cases W <;> rfl











/-- The base of the canonical axis-line description of an Axis-line/W question
is the point block carried by that question;
`def:pauli-question-distribution`. -/
theorem aLineDescOf_base_eq (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind) (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    (_root_.MIPStarRE.QPBT.aLineDescOf P.toLdParams
        (_root_.MIPStarRE.QPBT.ldALineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z))).base =
      _root_.MIPStarRE.QPBT.pauliPointBlock W (_root_.MIPStarRE.QPBT.pauliCL P (.aline W) z) := by
  cases W <;> exact _root_.MIPStarRE.QPBT.lineRepMap_apply_self _ _

/-- The direction of the canonical axis-line description of an Axis-line/W
question is the coordinate direction selected by the scalar block of that
question; `def:pauli-question-distribution`. -/
theorem aLineDescOf_direction_eq (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    (_root_.MIPStarRE.QPBT.aLineDescOf P.toLdParams
        (_root_.MIPStarRE.QPBT.ldALineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z))).direction =
      _root_.MIPStarRE.QPBT.coordinateDirection
        (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams (_root_.MIPStarRE.QPBT.pauliScalarBlock (_root_.MIPStarRE.QPBT.pauliCL P (.aline W) z))) := by
  cases W <;> rfl







/-! ### The honest measurements as coarse-grainings of one Pauli basis -/

/-- The honest Point/W measurement at a sampled Point/W question reports the
value of the low-degree encoding of the measured Pauli label at the point block
of the ambient vector. -/
theorem honestMeasurement_point_eq (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.honestMeasurement P (.point W) (_root_.MIPStarRE.QPBT.pauliCL P (.point W) z) =
      _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W)
        (fun h => _root_.MIPStarRE.QPBT.PauliAnswer.value (_root_.MIPStarRE.QPBT.lowDegreeEnc h (_root_.MIPStarRE.QPBT.pauliPointBlock W z))) := by
  have h1 : _root_.MIPStarRE.QPBT.honestMeasurement P (.point W) (_root_.MIPStarRE.QPBT.pauliCL P (.point W) z) =
      _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W)
        (fun h => _root_.MIPStarRE.QPBT.PauliAnswer.value
          (_root_.MIPStarRE.QPBT.lowDegreeEnc h (_root_.MIPStarRE.QPBT.pauliPointBlock W (_root_.MIPStarRE.QPBT.pauliCL P (.point W) z)))) :=
    _root_.MIPStarRE.QPBT.placedPauliMeasurement_postprocess_eq (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W)
      (fun h => _root_.MIPStarRE.QPBT.lowDegreeEnc h (_root_.MIPStarRE.QPBT.pauliPointBlock W (_root_.MIPStarRE.QPBT.pauliCL P (.point W) z)))
      (fun a => _root_.MIPStarRE.QPBT.PauliAnswer.value a)
  rw [h1, _root_.MIPStarRE.QPBT.pauliPointBlock_pauliCL_point]





/-- The honest Pauli/W measurement reports the measured Pauli label itself. -/
theorem honestMeasurement_pauli_eq (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.honestMeasurement P (.pauli W) (_root_.MIPStarRE.QPBT.pauliCL P (.pauli W) z) =
      _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W)
        (fun h => _root_.MIPStarRE.QPBT.PauliAnswer.pauliOutcome h) := rfl

/-- The honest Pair/X measurement at a sampled Pair/X question reports the
binary trace of the low-degree encoding of the measured Pauli label. -/
theorem honestMeasurement_pairW_X_eq (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.honestMeasurement P (.pairW .X) (_root_.MIPStarRE.QPBT.pauliCL P (.pairW .X) z) =
      _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliBasisMeasurement .X)
        (fun h => _root_.MIPStarRE.QPBT.PauliAnswer.bit
          (_root_.MIPStarRE.QPBT.pauliTraceBit P (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliRXBlock z) h)) :=
  _root_.MIPStarRE.QPBT.placedPauliMeasurement_postprocess_eq _ _ _

/-- The honest Pair/Z measurement at a sampled Pair/Z question reports the
binary trace of the low-degree encoding of the measured Pauli label. -/
theorem honestMeasurement_pairW_Z_eq (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.honestMeasurement P (.pairW .Z) (_root_.MIPStarRE.QPBT.pauliCL P (.pairW .Z) z) =
      _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliBasisMeasurement .Z)
        (fun h => _root_.MIPStarRE.QPBT.PauliAnswer.bit
          (_root_.MIPStarRE.QPBT.pauliTraceBit P (_root_.MIPStarRE.QPBT.pauliZBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z) h)) :=
  _root_.MIPStarRE.QPBT.placedPauliMeasurement_postprocess_eq _ _ _

/-- Two honest measurements coarse-graining one Pauli basis measurement have
zero operator product at every rejected answer pair, because a single Pauli
label produces an accepted pair. -/
theorem placedBasis_rejected_mul (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (x y : _root_.MIPStarRE.QPBT.PauliQuestion P) (f g : _root_.MIPStarRE.QPBT.PauliRegister P → _root_.MIPStarRE.QPBT.PauliAnswer P)
    (hacc : ∀ h : _root_.MIPStarRE.QPBT.PauliRegister P, _root_.MIPStarRE.QPBT.pauliWinPredicate P x y (f h) (g h) = true)
    (a b : _root_.MIPStarRE.QPBT.PauliAnswer P) (hrej : _root_.MIPStarRE.QPBT.pauliWinPredicate P x y a b = false) :
    (_root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W) f).effect a *
      (_root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W) g).effect b = 0 := by
  refine _root_.MIPStarRE.QPBT.placedPauliMeasurement_mul_eq_zero_of_incompatible _
    (fun h => _root_.MIPStarRE.QPBT.pauliProj_isProj W h) f g a b ?_
  intro h h1 h2
  rw [← h1, ← h2, hacc h] at hrej
  exact Bool.noConfusion hrej

/-! ### The consistency clauses along the incidence forms -/

/-- The honest Axis-line/W answer evaluates, at every line parameter of the
sampled point, to the honest Point/W value; this is the axis-line clause of
`def:pauli-win-predicate`. -/
theorem honest_alinePointCondition (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (h : _root_.MIPStarRE.QPBT.PauliRegister P) :
    _root_.MIPStarRE.QPBT.pauliAlinePointCondition P W (_root_.MIPStarRE.QPBT.pauliCL P (.aline W) z) (_root_.MIPStarRE.QPBT.pauliCL P (.point W) z)
      (_root_.MIPStarRE.QPBT.restrictToAxisLine P.toLdParams
        (_root_.MIPStarRE.QPBT.aLineDescOf P.toLdParams (_root_.MIPStarRE.QPBT.ldALineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z)))
        (_root_.MIPStarRE.QPBT.lowDegreeEncoding h))
      (_root_.MIPStarRE.QPBT.lowDegreeEnc h (_root_.MIPStarRE.QPBT.pauliPointBlock W z)) := by
  intro t ht
  rw [_root_.MIPStarRE.QPBT.pauliPointBlock_pauliCL_point] at ht
  have hkey := _root_.MIPStarRE.QPBT.evalCoefficient_restrictToAxisLine_lowDegreeEncoding P.toLdParams
    (_root_.MIPStarRE.QPBT.aLineDescOf P.toLdParams (_root_.MIPStarRE.QPBT.ldALineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z))) rfl h t
  rw [_root_.MIPStarRE.QPBT.aLineDescOf_base_eq, _root_.MIPStarRE.QPBT.aLineDescOf_direction_eq] at hkey
  rw [ht]
  exact hkey



/-! ### Zero products along the incidence forms of the Pauli type graph -/

/-- Along the Point/Axis-line incidence form the honest measurements have zero
operator product at every rejected answer pair. -/
theorem honest_point_aline_rejected_mul (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (a b : _root_.MIPStarRE.QPBT.PauliAnswer P)
    (hrej : _root_.MIPStarRE.QPBT.pauliWinPredicate P (.point W, _root_.MIPStarRE.QPBT.pauliCL P (.point W) z)
      (.aline W, _root_.MIPStarRE.QPBT.pauliCL P (.aline W) z) a b = false) :
    (_root_.MIPStarRE.QPBT.honestMeasurement P (.point W) (_root_.MIPStarRE.QPBT.pauliCL P (.point W) z)).effect a *
      (_root_.MIPStarRE.QPBT.honestMeasurement P (.aline W) (_root_.MIPStarRE.QPBT.pauliCL P (.aline W) z)).effect b = 0 := by
  rw [_root_.MIPStarRE.QPBT.honestMeasurement_point_eq, _root_.MIPStarRE.QPBT.honestMeasurement_aline_eq]
  refine _root_.MIPStarRE.QPBT.placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
  simpa [_root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer] using _root_.MIPStarRE.QPBT.honest_alinePointCondition P W z h

/-- Along the Point/Diagonal-line incidence form the honest measurements have
zero operator product at every rejected answer pair. -/
theorem honest_point_dline_rejected_mul (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (a b : _root_.MIPStarRE.QPBT.PauliAnswer P)
    (hrej : _root_.MIPStarRE.QPBT.pauliWinPredicate P (.point W, _root_.MIPStarRE.QPBT.pauliCL P (.point W) z)
      (.dline W, _root_.MIPStarRE.QPBT.pauliCL P (.dline W) z) a b = false) :
    (_root_.MIPStarRE.QPBT.honestMeasurement P (.point W) (_root_.MIPStarRE.QPBT.pauliCL P (.point W) z)).effect a *
      (_root_.MIPStarRE.QPBT.honestMeasurement P (.dline W) (_root_.MIPStarRE.QPBT.pauliCL P (.dline W) z)).effect b = 0 := by
  rw [_root_.MIPStarRE.QPBT.honestMeasurement_point_eq, _root_.MIPStarRE.QPBT.honestMeasurement_dline_eq]
  refine _root_.MIPStarRE.QPBT.placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
  simpa [_root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer] using _root_.MIPStarRE.QPBT.honest_dlinePointCondition P W z h

/-- Along the Point/Pauli incidence form the honest measurements have zero
operator product at every rejected answer pair. -/
theorem honest_point_pauli_rejected_mul (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (a b : _root_.MIPStarRE.QPBT.PauliAnswer P)
    (hrej : _root_.MIPStarRE.QPBT.pauliWinPredicate P (.point W, _root_.MIPStarRE.QPBT.pauliCL P (.point W) z)
      (.pauli W, _root_.MIPStarRE.QPBT.pauliCL P (.pauli W) z) a b = false) :
    (_root_.MIPStarRE.QPBT.honestMeasurement P (.point W) (_root_.MIPStarRE.QPBT.pauliCL P (.point W) z)).effect a *
      (_root_.MIPStarRE.QPBT.honestMeasurement P (.pauli W) (_root_.MIPStarRE.QPBT.pauliCL P (.pauli W) z)).effect b = 0 := by
  rw [_root_.MIPStarRE.QPBT.honestMeasurement_point_eq, _root_.MIPStarRE.QPBT.honestMeasurement_pauli_eq]
  refine _root_.MIPStarRE.QPBT.placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
  have hcond : _root_.MIPStarRE.QPBT.pauliPointPauliCondition P W (_root_.MIPStarRE.QPBT.pauliCL P (.point W) z) h
      (_root_.MIPStarRE.QPBT.lowDegreeEnc h (_root_.MIPStarRE.QPBT.pauliPointBlock W z)) := by
    change _root_.MIPStarRE.QPBT.lowDegreeEnc h (_root_.MIPStarRE.QPBT.pauliPointBlock W (_root_.MIPStarRE.QPBT.pauliCL P (.point W) z)) =
      _root_.MIPStarRE.QPBT.lowDegreeEnc h (_root_.MIPStarRE.QPBT.pauliPointBlock W z)
    rw [_root_.MIPStarRE.QPBT.pauliPointBlock_pauliCL_point]
  simpa [_root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer] using hcond

/-- Along the Point/Pair incidence form in the X basis the honest measurements
have zero operator product at every rejected answer pair. -/
theorem honest_point_pairW_X_rejected_mul (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (a b : _root_.MIPStarRE.QPBT.PauliAnswer P)
    (hrej : _root_.MIPStarRE.QPBT.pauliWinPredicate P (.point .X, _root_.MIPStarRE.QPBT.pauliCL P (.point .X) z)
      (.pairW .X, _root_.MIPStarRE.QPBT.pauliCL P (.pairW .X) z) a b = false) :
    (_root_.MIPStarRE.QPBT.honestMeasurement P (.point .X) (_root_.MIPStarRE.QPBT.pauliCL P (.point .X) z)).effect a *
      (_root_.MIPStarRE.QPBT.honestMeasurement P (.pairW .X) (_root_.MIPStarRE.QPBT.pauliCL P (.pairW .X) z)).effect b = 0 := by
  rw [_root_.MIPStarRE.QPBT.honestMeasurement_point_eq, _root_.MIPStarRE.QPBT.honestMeasurement_pairW_X_eq]
  refine _root_.MIPStarRE.QPBT.placedBasis_rejected_mul P .X _ _ _ _ (fun h => ?_) a b hrej
  have hcond : _root_.MIPStarRE.QPBT.pauliPointPairCondition P .X (_root_.MIPStarRE.QPBT.pauliCL P (.pairW .X) z)
      (_root_.MIPStarRE.QPBT.lowDegreeEnc h (_root_.MIPStarRE.QPBT.pauliPointBlock _root_.MIPStarRE.QPBT.PauliKind.X z))
      (_root_.MIPStarRE.QPBT.pauliTraceBit P (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliRXBlock z) h) := Or.inr rfl
  simpa [_root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer] using hcond

/-- Along the Point/Pair incidence form in the Z basis the honest measurements
have zero operator product at every rejected answer pair. -/
theorem honest_point_pairW_Z_rejected_mul (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (a b : _root_.MIPStarRE.QPBT.PauliAnswer P)
    (hrej : _root_.MIPStarRE.QPBT.pauliWinPredicate P (.point .Z, _root_.MIPStarRE.QPBT.pauliCL P (.point .Z) z)
      (.pairW .Z, _root_.MIPStarRE.QPBT.pauliCL P (.pairW .Z) z) a b = false) :
    (_root_.MIPStarRE.QPBT.honestMeasurement P (.point .Z) (_root_.MIPStarRE.QPBT.pauliCL P (.point .Z) z)).effect a *
      (_root_.MIPStarRE.QPBT.honestMeasurement P (.pairW .Z) (_root_.MIPStarRE.QPBT.pauliCL P (.pairW .Z) z)).effect b = 0 := by
  rw [_root_.MIPStarRE.QPBT.honestMeasurement_point_eq, _root_.MIPStarRE.QPBT.honestMeasurement_pairW_Z_eq]
  refine _root_.MIPStarRE.QPBT.placedBasis_rejected_mul P .Z _ _ _ _ (fun h => ?_) a b hrej
  have hcond : _root_.MIPStarRE.QPBT.pauliPointPairCondition P .Z (_root_.MIPStarRE.QPBT.pauliCL P (.pairW .Z) z)
      (_root_.MIPStarRE.QPBT.lowDegreeEnc h (_root_.MIPStarRE.QPBT.pauliPointBlock _root_.MIPStarRE.QPBT.PauliKind.Z z))
      (_root_.MIPStarRE.QPBT.pauliTraceBit P (_root_.MIPStarRE.QPBT.pauliZBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z) h) := Or.inr rfl
  simpa [_root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer] using hcond





/-! ### The Pair/W versus Pair incidence form -/





/-! ### The Magic Square incidence forms -/



/-! ### Zero products along the oriented incidence forms -/



end

end MIPStarRE.QPBT

/-!
# Rejection of wrong answers by the honest Pauli measurements

This module shows that the honest measurement family of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy.MeasurementFamily` assigns the zero
operator product to every answer pair rejected by the Pauli win predicate on a
question pair of positive weight for the Pauli question sampler.  Together with
the normalisation of the Born weights this yields the value-one assertion of
`lem:pauli-completeness`.

## References

Blueprint `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1383-1421`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



set_option maxRecDepth 8000

/-! ### Answers of an inadmissible form -/

















/-! ### Coordinate invariants of the typed Pauli conditionally linear maps -/

























/-! ### The honest measurements as coarse-grainings of one Pauli basis -/















/-! ### The consistency clauses along the incidence forms -/





/-! ### Zero products along the incidence forms of the Pauli type graph -/















/-! ### The Pair/W versus Pair incidence form -/





/-! ### The Magic Square incidence forms -/



/-! ### Zero products along the oriented incidence forms -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) {t₁ t₂ : _root_.MIPStarRE.QPBT.PauliType}
    (h : _root_.MIPStarRE.QPBT.PauliEdgeOriented t₁ t₂) (z : _root_.MIPStarRE.QPBT.PauliSpace P) (a b : _root_.MIPStarRE.QPBT.PauliAnswer P)
    (hrej : _root_.MIPStarRE.QPBT.pauliWinPredicate P (t₁, _root_.MIPStarRE.QPBT.pauliCL P t₁ z) (t₂, _root_.MIPStarRE.QPBT.pauliCL P t₂ z) a b = false) :
    (_root_.MIPStarRE.QPBT.honestMeasurement P t₁ (_root_.MIPStarRE.QPBT.pauliCL P t₁ z)).effect a *
      (_root_.MIPStarRE.QPBT.honestMeasurement P t₂ (_root_.MIPStarRE.QPBT.pauliCL P t₂ z)).effect b = 0 := by
  rcases h with ⟨W, rfl, hW⟩ | ⟨W, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hW with rfl | rfl | rfl | rfl
    · exact _root_.MIPStarRE.QPBT.honest_point_aline_rejected_mul P W z a b hrej
    · exact _root_.MIPStarRE.QPBT.honest_point_dline_rejected_mul P W z a b hrej
    · exact _root_.MIPStarRE.QPBT.honest_point_pauli_rejected_mul P W z a b hrej
    · cases W with
      | X => exact _root_.MIPStarRE.QPBT.honest_point_pairW_X_rejected_mul P z a b hrej
      | Z => exact _root_.MIPStarRE.QPBT.honest_point_pairW_Z_rejected_mul P z a b hrej
  · exact _root_.MIPStarRE.QPBT.honest_pairW_pair_rejected_mul P W z a b hrej
  · exact _root_.MIPStarRE.QPBT.honest_point_msVar_X_rejected_mul P z a b hrej
  · exact _root_.MIPStarRE.QPBT.honest_point_msVar_Z_rejected_mul P z a b hrej
