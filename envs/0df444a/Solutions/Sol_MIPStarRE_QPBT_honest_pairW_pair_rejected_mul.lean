-- Prove2me | solution 1 for MIPStarRE.QPBT.honest_pairW_pair_rejected_mul
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:04:45.931125+00:00
-- url     : https://prove2.me/submissions/3ac95263-f54a-482e-86b0-ee0c536b6dfa

-- Generated proof for MIPStarRE.QPBT.honest_pairW_pair_rejected_mul.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
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
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy_MeasurementFamily
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Measurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_honestMagicMeasurement_effect_eq_zero
import Theorems.Thm_MIPStarRE_QPBT_honestPairMeasurement_effect_eq_zero

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Completeness/Commutation.lean. -/
/-!
# Commutation of the honest Pauli measurements

This module proves that the honest measurement family of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy.MeasurementFamily` has commuting effects
on every question pair of positive weight for the Pauli question sampler.  The
argument first characterises the supported question pairs as the typed
conditionally linear images of a single ambient coefficient vector along an edge
of the Pauli type graph, and then treats the five edge families of that graph.

## References

This is the commutation obligation in the proof of `lem:pauli-completeness`,
blueprint `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1382`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

set_option maxRecDepth 8000

/-! ### The supported question pairs -/







/-! ### Coarse-graining and tensor placement -/



/-- The effect of a placed and relabelled measurement of the Pauli register. -/
theorem placedPauliMeasurement_effect_eq {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α (_root_.MIPStarRE.QPBT.PauliRegister P)) (f : α → _root_.MIPStarRE.QPBT.PauliAnswer P)
    (a : _root_.MIPStarRE.QPBT.PauliAnswer P) :
    (_root_.MIPStarRE.QPBT.placedPauliMeasurement M f).effect a =
      _root_.MIPStarRE.QPBT.heteroKron ((M.postprocess f).effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ZMod 2)) := by
  rw [_root_.MIPStarRE.QPBT.placedPauliMeasurement, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  change (∑ b ∈ Finset.univ.filter (fun b => f b = a),
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ZMod 2) (M.effect b)) =
    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ZMod 2)
      (∑ b ∈ Finset.univ.filter (fun b => f b = a), M.effect b)
  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum _ _









/-! ### Honest measurements sharing a Pauli basis -/





/-! ### The Pair and Magic Square measurements -/







/-! ### Commutation along the Pauli type graph -/





end

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





















/-- A zero product remains zero after placement on the first tensor factor. -/
theorem leftPlaced_mul_eq_zero {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    {A B : _root_.LIDT.MIPStarRE.Quantum.Op V} (h : A * B = 0) :
    _root_.MIPStarRE.QPBT.heteroKron A (1 : _root_.LIDT.MIPStarRE.Quantum.Op W) * _root_.MIPStarRE.QPBT.heteroKron B (1 : _root_.LIDT.MIPStarRE.Quantum.Op W) = 0 := by
  rw [_root_.MIPStarRE.QPBT.heteroKron_mul, h]
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply]









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

























/-! ### The honest measurements as coarse-grainings of one Pauli basis -/















/-! ### The consistency clauses along the incidence forms -/





/-! ### Zero products along the incidence forms of the Pauli type graph -/















/-! ### The Pair/W versus Pair incidence form -/

/-- The effect of a placed and injectively relabelled measurement of the Pauli
register at a relabelled outcome is the placed original effect. -/
theorem placedPauliMeasurement_effect_image {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α (_root_.MIPStarRE.QPBT.PauliRegister P)) (f : α → _root_.MIPStarRE.QPBT.PauliAnswer P)
    (hf : Function.Injective f) (a : α) :
    (_root_.MIPStarRE.QPBT.placedPauliMeasurement M f).effect (f a) =
      _root_.MIPStarRE.QPBT.heteroKron (M.effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ZMod 2)) := by
  rw [_root_.MIPStarRE.QPBT.placedPauliMeasurement_effect_eq, _root_.MIPStarRE.QPBT.SandwichProduct.postprocess_effect_of_injective _ _ hf]



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

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (a b : _root_.MIPStarRE.QPBT.PauliAnswer P)
    (hrej : _root_.MIPStarRE.QPBT.pauliWinPredicate P (.pairW W, _root_.MIPStarRE.QPBT.pauliCL P (.pairW W) z)
      (.pair, _root_.MIPStarRE.QPBT.pauliCL P .pair z) a b = false) :
    (_root_.MIPStarRE.QPBT.honestMeasurement P (.pairW W) (_root_.MIPStarRE.QPBT.pauliCL P (.pairW W) z)).effect a *
      (_root_.MIPStarRE.QPBT.honestMeasurement P .pair (_root_.MIPStarRE.QPBT.pauliCL P .pair z)).effect b = 0 := by
  classical
  rcases (Bool.eq_false_or_eq_true
    (_root_.MIPStarRE.QPBT.validPauliAnswer (P := P) (_root_.MIPStarRE.QPBT.PauliType.pairW W) a)).symm with hva | hva
  · rw [_root_.MIPStarRE.QPBT.honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
  rcases (Bool.eq_false_or_eq_true
    (_root_.MIPStarRE.QPBT.validPauliAnswer (P := P) _root_.MIPStarRE.QPBT.PauliType.pair b)).symm with hvb | hvb
  · rw [_root_.MIPStarRE.QPBT.honestMeasurement_effect_eq_zero_of_invalid P _ _ hvb, mul_zero]
  obtain ⟨β, rfl⟩ : ∃ c, a = _root_.MIPStarRE.QPBT.PauliAnswer.bit c := by
    cases a <;> first | exact ⟨_, rfl⟩ | exact absurd hva (by simp [_root_.MIPStarRE.QPBT.validPauliAnswer])
  obtain ⟨bits, rfl⟩ : ∃ c, b = _root_.MIPStarRE.QPBT.PauliAnswer.pairBits c := by
    cases b <;> first | exact ⟨_, rfl⟩ | exact absurd hvb (by simp [_root_.MIPStarRE.QPBT.validPauliAnswer])
  have hacc : _root_.MIPStarRE.QPBT.pauliPairCondition P W (_root_.MIPStarRE.QPBT.pauliCL P (.pairW W) z) β bits →
      _root_.MIPStarRE.QPBT.pauliWinPredicate P (_root_.MIPStarRE.QPBT.PauliType.pairW W, _root_.MIPStarRE.QPBT.pauliCL P (.pairW W) z)
        (_root_.MIPStarRE.QPBT.PauliType.pair, _root_.MIPStarRE.QPBT.pauliCL P .pair z) (_root_.MIPStarRE.QPBT.PauliAnswer.bit β)
        (_root_.MIPStarRE.QPBT.PauliAnswer.pairBits bits) = true := by
    intro hc
    simpa [_root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer] using hc
  by_cases hg : _root_.MIPStarRE.QPBT.pauliPairGamma P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) = 0
  · have hcond : ¬ _root_.MIPStarRE.QPBT.pauliPairCondition P W (_root_.MIPStarRE.QPBT.pauliCL P (.pairW W) z) β bits := by
      intro hc
      rw [hacc hc] at hrej
      exact Bool.noConfusion hrej
    have hpair : _root_.MIPStarRE.QPBT.honestMeasurement P _root_.MIPStarRE.QPBT.PauliType.pair (_root_.MIPStarRE.QPBT.pauliCL P _root_.MIPStarRE.QPBT.PauliType.pair z) =
        _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliPairMeasurement P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) hg)
          (fun c => _root_.MIPStarRE.QPBT.PauliAnswer.pairBits c) := by
      change _root_.MIPStarRE.QPBT.honestPairMeasurement P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) = _
      simp [_root_.MIPStarRE.QPBT.honestPairMeasurement, hg]
    have h2 : (_root_.MIPStarRE.QPBT.honestMeasurement P _root_.MIPStarRE.QPBT.PauliType.pair
          (_root_.MIPStarRE.QPBT.pauliCL P _root_.MIPStarRE.QPBT.PauliType.pair z)).effect (_root_.MIPStarRE.QPBT.PauliAnswer.pairBits bits) =
        _root_.MIPStarRE.QPBT.heteroKron ((_root_.MIPStarRE.QPBT.pauliTraceMeasurement P .X (_root_.MIPStarRE.QPBT.pauliXBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))
              (_root_.MIPStarRE.QPBT.pauliRXBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))).effect bits.1 *
            (_root_.MIPStarRE.QPBT.pauliTraceMeasurement P .Z (_root_.MIPStarRE.QPBT.pauliZBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))
              (_root_.MIPStarRE.QPBT.pauliRZBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))).effect bits.2)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ZMod 2)) := by
      rw [hpair]
      exact _root_.MIPStarRE.QPBT.placedPauliMeasurement_effect_image _ _ (by intro; simp) bits
    cases W with
    | X =>
        have hne : β ≠ bits.1 := by
          intro h
          refine hcond ?_
          simp only [_root_.MIPStarRE.QPBT.pauliPairCondition]
          exact Or.inr h.symm
        have h1 : (_root_.MIPStarRE.QPBT.honestMeasurement P (_root_.MIPStarRE.QPBT.PauliType.pairW _root_.MIPStarRE.QPBT.PauliKind.X)
              (_root_.MIPStarRE.QPBT.pauliCL P (.pairW .X) z)).effect (_root_.MIPStarRE.QPBT.PauliAnswer.bit β) =
            _root_.MIPStarRE.QPBT.heteroKron ((_root_.MIPStarRE.QPBT.pauliTraceMeasurement P .X (_root_.MIPStarRE.QPBT.pauliXBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))
              (_root_.MIPStarRE.QPBT.pauliRXBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))).effect β) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ZMod 2)) :=
          _root_.MIPStarRE.QPBT.placedPauliMeasurement_effect_image _ _ (by intro; simp) β
        rw [h1, h2]
        refine _root_.MIPStarRE.QPBT.leftPlaced_mul_eq_zero ?_
        rw [← mul_assoc,
          _root_.MIPStarRE.QPBT.DistanceCalculus.projective_effect_mul_effect_eq_zero
            (_root_.MIPStarRE.QPBT.pauliTraceMeasurement P .X (_root_.MIPStarRE.QPBT.pauliXBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))
              (_root_.MIPStarRE.QPBT.pauliRXBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z)))
            (_root_.MIPStarRE.QPBT.pauliTraceMeasurement_projective P .X _ _) hne,
          zero_mul]
    | Z =>
        have hne : β ≠ bits.2 := by
          intro h
          refine hcond ?_
          simp only [_root_.MIPStarRE.QPBT.pauliPairCondition]
          exact Or.inr h.symm
        have h1 : (_root_.MIPStarRE.QPBT.honestMeasurement P (_root_.MIPStarRE.QPBT.PauliType.pairW _root_.MIPStarRE.QPBT.PauliKind.Z)
              (_root_.MIPStarRE.QPBT.pauliCL P (.pairW .Z) z)).effect (_root_.MIPStarRE.QPBT.PauliAnswer.bit β) =
            _root_.MIPStarRE.QPBT.heteroKron ((_root_.MIPStarRE.QPBT.pauliTraceMeasurement P .Z (_root_.MIPStarRE.QPBT.pauliZBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))
              (_root_.MIPStarRE.QPBT.pauliRZBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))).effect β) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ZMod 2)) :=
          _root_.MIPStarRE.QPBT.placedPauliMeasurement_effect_image _ _ (by intro; simp) β
        rw [h1, h2]
        refine _root_.MIPStarRE.QPBT.leftPlaced_mul_eq_zero ?_
        rw [← mul_assoc,
          ← (_root_.MIPStarRE.QPBT.pauliTraceMeasurement_effect_commute P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) hg
            bits.1 β).eq, mul_assoc,
          _root_.MIPStarRE.QPBT.DistanceCalculus.projective_effect_mul_effect_eq_zero
            (_root_.MIPStarRE.QPBT.pauliTraceMeasurement P .Z (_root_.MIPStarRE.QPBT.pauliZBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))
              (_root_.MIPStarRE.QPBT.pauliRZBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z)))
            (_root_.MIPStarRE.QPBT.pauliTraceMeasurement_projective P .Z _ _) hne,
          mul_zero]
  · exfalso
    rw [hacc (Or.inl hg)] at hrej
    exact Bool.noConfusion hrej
