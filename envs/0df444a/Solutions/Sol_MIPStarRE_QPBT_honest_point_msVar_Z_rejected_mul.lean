-- Prove2me | solution 1 for MIPStarRE.QPBT.honest_point_msVar_Z_rejected_mul
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:05:35.141543+00:00
-- url     : https://prove2.me/submissions/02ff89fa-ea3d-49a0-b0a0-0b47e4b79691

-- Generated proof for MIPStarRE.QPBT.honest_point_msVar_Z_rejected_mul.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy_MeasurementFamily
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Measurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_isProj_kronecker
import Theorems.Thm_MIPStarRE_QPBT_honestMagicMeasurement_effect_eq_zero
import Theorems.Thm_MIPStarRE_QPBT_honestMagicMeasurement_var_eq_placedBasis
import Theorems.Thm_MIPStarRE_QPBT_honestPairMeasurement_effect_eq_zero
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



/-- An answer outside a placed coarse-graining's relabelling range has zero
effect. -/
theorem placedPauliMeasurement_effect_eq_zero_of_notMem {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α (_root_.MIPStarRE.QPBT.PauliRegister P)) (f : α → _root_.MIPStarRE.QPBT.PauliAnswer P)
    {a : _root_.MIPStarRE.QPBT.PauliAnswer P} (ha : a ∉ Set.range f) :
    (_root_.MIPStarRE.QPBT.placedPauliMeasurement M f).effect a = 0 := by
  change ((_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess f).effect a = 0
  exact _root_.MIPStarRE.QPBT.postprocess_effect_eq_zero_of_notMem _ _ ha

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

/-- The honest Point/W measurement assigns the zero effect to every answer that
is not a field value; part of the answer-format rejection clause of
`def:pauli-win-predicate`. -/
theorem honestPointMeasurement_effect_eq_zero (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (z : _root_.MIPStarRE.QPBT.PauliSpace P) {a : _root_.MIPStarRE.QPBT.PauliAnswer P}
    (ha : _root_.MIPStarRE.QPBT.validPauliAnswer (.point W) a = false) :
    (_root_.MIPStarRE.QPBT.honestPointMeasurement P W z).effect a = 0 := by
  refine _root_.MIPStarRE.QPBT.placedPauliMeasurement_effect_eq_zero_of_notMem _ _ ?_
  rintro ⟨u, rfl⟩
  simp [_root_.MIPStarRE.QPBT.validPauliAnswer] at ha

/-- The honest Axis-line/W measurement assigns the zero effect to every answer
that is not a degree-`d` coefficient list; part of the answer-format
rejection clause of `def:pauli-win-predicate`. -/
theorem honestALineMeasurement_effect_eq_zero (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (z : _root_.MIPStarRE.QPBT.PauliSpace P) {a : _root_.MIPStarRE.QPBT.PauliAnswer P}
    (ha : _root_.MIPStarRE.QPBT.validPauliAnswer (.aline W) a = false) :
    (_root_.MIPStarRE.QPBT.honestALineMeasurement P W z).effect a = 0 := by
  refine _root_.MIPStarRE.QPBT.placedPauliMeasurement_effect_eq_zero_of_notMem _ _ ?_
  rintro ⟨u, rfl⟩
  simp [_root_.MIPStarRE.QPBT.validPauliAnswer] at ha

/-- The honest Diagonal-line/W measurement assigns the zero effect to every
answer that is not a degree-`m d` coefficient list; part of the
answer-format rejection clause of `def:pauli-win-predicate`. -/
theorem honestDLineMeasurement_effect_eq_zero (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (z : _root_.MIPStarRE.QPBT.PauliSpace P) {a : _root_.MIPStarRE.QPBT.PauliAnswer P}
    (ha : _root_.MIPStarRE.QPBT.validPauliAnswer (.dline W) a = false) :
    (_root_.MIPStarRE.QPBT.honestDLineMeasurement P W z).effect a = 0 := by
  refine _root_.MIPStarRE.QPBT.placedPauliMeasurement_effect_eq_zero_of_notMem _ _ ?_
  rintro ⟨u, rfl⟩
  simp [_root_.MIPStarRE.QPBT.validPauliAnswer] at ha

/-- The honest Pauli/W measurement assigns the zero effect to every answer that
is not a Pauli label; part of the answer-format rejection clause of
`def:pauli-win-predicate`. -/
theorem honestPauliMeasurement_effect_eq_zero (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (W : _root_.MIPStarRE.QPBT.PauliKind) {a : _root_.MIPStarRE.QPBT.PauliAnswer P}
    (ha : _root_.MIPStarRE.QPBT.validPauliAnswer (.pauli W) a = false) :
    (_root_.MIPStarRE.QPBT.honestPauliMeasurement P W).effect a = 0 := by
  refine _root_.MIPStarRE.QPBT.placedPauliMeasurement_effect_eq_zero_of_notMem _ _ ?_
  rintro ⟨u, rfl⟩
  simp [_root_.MIPStarRE.QPBT.validPauliAnswer] at ha

/-- The honest Pair/W measurement assigns the zero effect to every answer that
is not a bit; part of the answer-format rejection clause of
`def:pauli-win-predicate`. -/
theorem honestPairWMeasurement_effect_eq_zero (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (z : _root_.MIPStarRE.QPBT.PauliSpace P) {a : _root_.MIPStarRE.QPBT.PauliAnswer P}
    (ha : _root_.MIPStarRE.QPBT.validPauliAnswer (.pairW W) a = false) :
    (_root_.MIPStarRE.QPBT.honestPairWMeasurement P W z).effect a = 0 := by
  refine _root_.MIPStarRE.QPBT.placedPauliMeasurement_effect_eq_zero_of_notMem _ _ ?_
  rintro ⟨u, rfl⟩
  simp [_root_.MIPStarRE.QPBT.validPauliAnswer] at ha





/-- The honest measurement family assigns the zero effect to every answer whose
form is not the one prescribed by its question type; this is the
answer-format rejection clause of `def:pauli-win-predicate`, blueprint
`def:pauli-win-predicate`. -/
theorem honestMeasurement_effect_eq_zero_of_invalid (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (t : _root_.MIPStarRE.QPBT.PauliType) (z : _root_.MIPStarRE.QPBT.PauliSpace P) {a : _root_.MIPStarRE.QPBT.PauliAnswer P}
    (ha : _root_.MIPStarRE.QPBT.validPauliAnswer t a = false) :
    (_root_.MIPStarRE.QPBT.honestMeasurement P t z).effect a = 0 := by
  cases t with
  | point W => exact _root_.MIPStarRE.QPBT.honestPointMeasurement_effect_eq_zero P W z ha
  | aline W => exact _root_.MIPStarRE.QPBT.honestALineMeasurement_effect_eq_zero P W z ha
  | dline W => exact _root_.MIPStarRE.QPBT.honestDLineMeasurement_effect_eq_zero P W z ha
  | pauli W => exact _root_.MIPStarRE.QPBT.honestPauliMeasurement_effect_eq_zero P W ha
  | pairW W => exact _root_.MIPStarRE.QPBT.honestPairWMeasurement_effect_eq_zero P W z ha
  | pair => exact _root_.MIPStarRE.QPBT.honestPairMeasurement_effect_eq_zero P z ha
  | ms s => exact _root_.MIPStarRE.QPBT.honestMagicMeasurement_effect_eq_zero P s z ha

/-! ### Coordinate invariants of the typed Pauli conditionally linear maps -/



/-- The point block of a Point/W question is the point block of the ambient
coefficient vector; `def:pauli-question-distribution`. -/
theorem pauliPointBlock_pauliCL_point (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.pauliPointBlock W (_root_.MIPStarRE.QPBT.pauliCL P (.point W) z) = _root_.MIPStarRE.QPBT.pauliPointBlock W z := by
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





/-! ### Zero products along the incidence forms of the Pauli type graph -/















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

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (a b : _root_.MIPStarRE.QPBT.PauliAnswer P)
    (hrej : _root_.MIPStarRE.QPBT.pauliWinPredicate P (.point .Z, _root_.MIPStarRE.QPBT.pauliCL P (.point .Z) z)
      (.ms (.var 4), _root_.MIPStarRE.QPBT.pauliCL P (.ms (.var 4)) z) a b = false) :
    (_root_.MIPStarRE.QPBT.honestMeasurement P (.point .Z) (_root_.MIPStarRE.QPBT.pauliCL P (.point .Z) z)).effect a *
      (_root_.MIPStarRE.QPBT.honestMeasurement P (.ms (.var 4)) (_root_.MIPStarRE.QPBT.pauliCL P (.ms (.var 4)) z)).effect b = 0 := by
  classical
  rcases (Bool.eq_false_or_eq_true
    (_root_.MIPStarRE.QPBT.validPauliAnswer (_root_.MIPStarRE.QPBT.PauliType.point _root_.MIPStarRE.QPBT.PauliKind.Z) a)).symm with hva | hva
  · rw [_root_.MIPStarRE.QPBT.honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
  rcases (Bool.eq_false_or_eq_true
    (_root_.MIPStarRE.QPBT.validPauliAnswer (_root_.MIPStarRE.QPBT.PauliType.ms (_root_.MIPStarRE.QPBT.MsType.var 4)) b)).symm with hvb | hvb
  · rw [_root_.MIPStarRE.QPBT.honestMeasurement_effect_eq_zero_of_invalid P _ _ hvb, mul_zero]
  obtain ⟨u, rfl⟩ : ∃ u, a = _root_.MIPStarRE.QPBT.PauliAnswer.value u := by
    cases a <;> first | exact ⟨_, rfl⟩ | exact absurd hva (by simp [_root_.MIPStarRE.QPBT.validPauliAnswer])
  obtain ⟨β, rfl⟩ : ∃ c, b = _root_.MIPStarRE.QPBT.PauliAnswer.bit c := by
    cases b <;> first | exact ⟨_, rfl⟩ | exact absurd hvb (by simp [_root_.MIPStarRE.QPBT.validPauliAnswer])
  by_cases hg : _root_.MIPStarRE.QPBT.pauliPairGamma P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) = 0
  · exfalso
    have hcond : _root_.MIPStarRE.QPBT.pauliPointVariableCondition P .Z
        (_root_.MIPStarRE.QPBT.pauliCL P (.ms (.var 4)) z) 4 u β := Or.inl hg
    rw [show _root_.MIPStarRE.QPBT.pauliWinPredicate P (_root_.MIPStarRE.QPBT.PauliType.point _root_.MIPStarRE.QPBT.PauliKind.Z, _root_.MIPStarRE.QPBT.pauliCL P (.point .Z) z)
        (_root_.MIPStarRE.QPBT.PauliType.ms (_root_.MIPStarRE.QPBT.MsType.var 4), _root_.MIPStarRE.QPBT.pauliCL P (.ms (.var 4)) z)
        (_root_.MIPStarRE.QPBT.PauliAnswer.value u) (_root_.MIPStarRE.QPBT.PauliAnswer.bit β) = true from by
      simpa [_root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer] using hcond] at hrej
    exact Bool.noConfusion hrej
  · have hms : _root_.MIPStarRE.QPBT.honestMeasurement P (.ms (.var 4)) (_root_.MIPStarRE.QPBT.pauliCL P (.ms (.var 4)) z) =
        _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliBasisMeasurement .Z)
          (fun h => _root_.MIPStarRE.QPBT.PauliAnswer.bit (_root_.MIPStarRE.QPBT.pauliTraceBit P
            (_root_.MIPStarRE.QPBT.pauliZBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))
            (_root_.MIPStarRE.QPBT.pauliRZBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z)) h)) :=
      (_root_.MIPStarRE.QPBT.honestMagicMeasurement_var_eq_placedBasis P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) hg).2
    rw [_root_.MIPStarRE.QPBT.honestMeasurement_point_eq, hms]
    refine _root_.MIPStarRE.QPBT.placedBasis_rejected_mul P .Z _ _ _ _ (fun h => ?_) _ _ hrej
    have hcond : _root_.MIPStarRE.QPBT.pauliPointVariableCondition P .Z (_root_.MIPStarRE.QPBT.pauliCL P (.ms (.var 4)) z) 4
        (_root_.MIPStarRE.QPBT.lowDegreeEnc h (_root_.MIPStarRE.QPBT.pauliPointBlock _root_.MIPStarRE.QPBT.PauliKind.Z z))
        (_root_.MIPStarRE.QPBT.pauliTraceBit P (_root_.MIPStarRE.QPBT.pauliZBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))
          (_root_.MIPStarRE.QPBT.pauliRZBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z)) h) :=
      Or.inr (Or.inr ⟨by decide, rfl, rfl⟩)
    simpa [_root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer] using hcond
