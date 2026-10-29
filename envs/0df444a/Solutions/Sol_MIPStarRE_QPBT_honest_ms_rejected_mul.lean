-- Prove2me | solution 1 for MIPStarRE.QPBT.honest_ms_rejected_mul
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:11:49.257994+00:00
-- url     : https://prove2.me/submissions/5896ff31-6c5f-467d-9b12-0bdc52918a0c

-- Generated proof for MIPStarRE.QPBT.honest_ms_rejected_mul.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy_MeasurementFamily
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Basic
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Measurements
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Observables
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_honestMagicMeasurement_effect_eq_zero
import Theorems.Thm_MIPStarRE_QPBT_honestPairMeasurement_effect_eq_zero
import Theorems.Thm_MIPStarRE_QPBT_msCellConstraintJoint_mul
import Theorems.Thm_MIPStarRE_QPBT_msGame_support_incidence
import Theorems.Thm_MIPStarRE_QPBT_msStrategyMeasurement_incident_commute

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



/-- The embedding of Magic Square answers is injective. -/
theorem pauliAnswerOfMs_injective {P : _root_.MIPStarRE.QPBT.AdmissibleParams} :
    Function.Injective (@_root_.MIPStarRE.QPBT.pauliAnswerOfMs P) := by
  intro a b h
  cases a <;> cases b <;> simp only [_root_.MIPStarRE.QPBT.pauliAnswerOfMs] at h <;> cases h <;> rfl





































end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/MagicSquareTheorems/PerfectStrategy/Measurements.lean. -/
/-!
# Measurements of the perfect Magic Square strategy

This module turns the operator table of `thm:ms-from-ac` into a measurement
family.  It forms the joint measurement of two commuting binary projective
measurements, records the post-processing identities for injective
relabellings, encodes a constraint answer as the parity triple determined by
two freely chosen bits, and assembles the nine cell measurements into the
Magic Square measurement family, closing with the multiplication rule relating
a constraint outcome to the outcomes of its incident variables.

## References

The source statement is blueprint
`thm:ms-from-ac`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:654-722`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section



















/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the triple encoding two freely chosen bits sums
to the parity `msParity i` prescribed by the constraint. -/
theorem parityTriple_sum (i : Fin 6) (ab : ZMod 2 × ZMod 2) :
    ∑ k : Fin 3, _root_.MIPStarRE.QPBT.parityTriple i ab k = _root_.MIPStarRE.QPBT.msParity i := by
  rw [Fin.sum_univ_three]
  simp [_root_.MIPStarRE.QPBT.parityTriple]



















/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): on a variable question the global measurement
family reproduces the corresponding cell measurement: its effect at the answer
`bit b` is the effect of `P j` at `b`. -/
theorem msStrategyMeasurement_var_bit
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) V)
    (hP : ∀ j, _root_.MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect a)
        ((P (_root_.MIPStarRE.QPBT.msConstraintVars i l)).effect b))
    (j : Fin 9) (b : ZMod 2) :
    (_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm (.var j)).effect (.bit b) =
      (P j).effect b := by
  exact postprocess_effect_of_injective (P j) _root_.MIPStarRE.QPBT.MsAnswer.bit
    bit_embedding_injective b

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): on a variable question the global measurement
family assigns the zero effect to every answer outside the range of
`MsAnswer.bit`. -/
theorem msStrategyMeasurement_var_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) V)
    (hP : ∀ j, _root_.MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect a)
        ((P (_root_.MIPStarRE.QPBT.msConstraintVars i l)).effect b))
    (j : Fin 9) {a : _root_.MIPStarRE.QPBT.MsAnswer}
    (ha : a ∉ Set.range (_root_.MIPStarRE.QPBT.MsAnswer.bit : ZMod 2 → _root_.MIPStarRE.QPBT.MsAnswer)) :
    (_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm (.var j)).effect a = 0 := by
  exact _root_.MIPStarRE.QPBT.postprocess_effect_eq_zero_of_notMem (P j) _root_.MIPStarRE.QPBT.MsAnswer.bit ha

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): on a constraint question the effect at the answer
triple encoding the bits `ab` equals the effect at `ab` of the joint measurement
of the first two cells of that constraint. -/
theorem msStrategyMeasurement_constraint_triple
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) V)
    (hP : ∀ j, _root_.MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect a)
        ((P (_root_.MIPStarRE.QPBT.msConstraintVars i l)).effect b))
    (i : Fin 6) (ab : ZMod 2 × ZMod 2) :
    (_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm (.constraint i)).effect
        (.triple (_root_.MIPStarRE.QPBT.parityTriple i ab)) =
      (_root_.MIPStarRE.QPBT.msConstraintJoint P hP hcomm i).effect ab := by
  exact postprocess_effect_of_injective (_root_.MIPStarRE.QPBT.msConstraintJoint P hP hcomm i)
    (fun cd => _root_.MIPStarRE.QPBT.MsAnswer.triple (_root_.MIPStarRE.QPBT.parityTriple i cd))
    (triple_embedding_injective i) ab

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): on a constraint question the global measurement
family assigns the zero effect to every answer that is not a parity triple of
the constraint. -/
theorem msStrategyMeasurement_constraint_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) V)
    (hP : ∀ j, _root_.MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect a)
        ((P (_root_.MIPStarRE.QPBT.msConstraintVars i l)).effect b))
    (i : Fin 6) {a : _root_.MIPStarRE.QPBT.MsAnswer}
    (ha : a ∉ Set.range (fun ab => _root_.MIPStarRE.QPBT.MsAnswer.triple (_root_.MIPStarRE.QPBT.parityTriple i ab))) :
    (_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm (.constraint i)).effect a = 0 := by
  exact _root_.MIPStarRE.QPBT.postprocess_effect_eq_zero_of_notMem (_root_.MIPStarRE.QPBT.msConstraintJoint P hP hcomm i)
    (fun ab => _root_.MIPStarRE.QPBT.MsAnswer.triple (_root_.MIPStarRE.QPBT.parityTriple i ab)) ha











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





/-! ### The Magic Square incidence forms -/



/-! ### Zero products along the oriented incidence forms -/



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/MagicSquareTheorems/PerfectStrategy.lean. -/
/-!
# Perfect strategies for the Magic Square game

This file completes the construction of `thm:ms-from-ac`.  It identifies the
question pairs in the support of the Magic Square distribution, shows that the
measurement family commutes there and annihilates rejected answer pairs on the
EPR state, evaluates the Born weights of the accepted answers, and assembles a
symmetric SPCC strategy of value one from an anticommuting consistent pair of
binary measurements.

## References

The source statement is blueprint
`thm:ms-from-ac`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:654-722`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

private theorem msConstraintVars_injective (i : Fin 6) :
    Function.Injective (_root_.MIPStarRE.QPBT.msConstraintVars i) := by
  intro k l h
  fin_cases i <;> fin_cases k <;> fin_cases l <;>
    simp [_root_.MIPStarRE.QPBT.msConstraintVars] at h ⊢

private theorem msConstraintVars_exists_iff
    (i : Fin 6) (k : Fin 3) (β : Fin 3 → ZMod 2) (b : ZMod 2) :
    (∃ l : Fin 3, _root_.MIPStarRE.QPBT.msConstraintVars i l = _root_.MIPStarRE.QPBT.msConstraintVars i k ∧ β l = b) ↔
      β k = b := by
  constructor
  · rintro ⟨l, hl, hlb⟩
    rwa [msConstraintVars_injective i hl] at hlb
  · intro h
    exact ⟨k, rfl, h⟩



private theorem msStrategyMeasurement_rejected_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) V)
    (hP : ∀ j, _root_.MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect a)
        ((P (_root_.MIPStarRE.QPBT.msConstraintVars i l)).effect b))
    (hmul : ∀ i k ab b,
      (_root_.MIPStarRE.QPBT.msConstraintJoint P hP hcomm i).effect ab *
          (P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect b =
        if _root_.MIPStarRE.QPBT.parityTriple i ab k = b then
          (_root_.MIPStarRE.QPBT.msConstraintJoint P hP hcomm i).effect ab else 0)
    (i : Fin 6) (k : Fin 3) (a b : _root_.MIPStarRE.QPBT.MsAnswer)
    (hrej : _root_.MIPStarRE.QPBT.msWinPredicate (.constraint i) (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) a b = false) :
    ((_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm (.constraint i)).effect a) *
      ((_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm
        (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k))).effect b) = 0 := by
  by_cases ha : a ∈ Set.range (fun ab => _root_.MIPStarRE.QPBT.MsAnswer.triple (_root_.MIPStarRE.QPBT.parityTriple i ab))
  · rcases ha with ⟨ab, rfl⟩
    rw [_root_.MIPStarRE.QPBT.msStrategyMeasurement_constraint_triple]
    by_cases hb : b ∈ Set.range (_root_.MIPStarRE.QPBT.MsAnswer.bit : ZMod 2 → _root_.MIPStarRE.QPBT.MsAnswer)
    · rcases hb with ⟨c, rfl⟩
      rw [_root_.MIPStarRE.QPBT.msStrategyMeasurement_var_bit]
      have hne : _root_.MIPStarRE.QPBT.parityTriple i ab k ≠ c := by
        simpa [_root_.MIPStarRE.QPBT.msWinPredicate, _root_.MIPStarRE.QPBT.parityTriple_sum,
          msConstraintVars_exists_iff] using hrej
      rw [hmul i k ab c]
      simp [hne]
    · rw [_root_.MIPStarRE.QPBT.msStrategyMeasurement_var_zero _ _ _ _ hb]
      simp
  · rw [_root_.MIPStarRE.QPBT.msStrategyMeasurement_constraint_zero _ _ _ _ ha]
    simp

private theorem msStrategyMeasurement_rejected_mul_reverse
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) V)
    (hP : ∀ j, _root_.MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect a)
        ((P (_root_.MIPStarRE.QPBT.msConstraintVars i l)).effect b))
    (hmul : ∀ i k ab b,
      (_root_.MIPStarRE.QPBT.msConstraintJoint P hP hcomm i).effect ab *
          (P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect b =
        if _root_.MIPStarRE.QPBT.parityTriple i ab k = b then
          (_root_.MIPStarRE.QPBT.msConstraintJoint P hP hcomm i).effect ab else 0)
    (i : Fin 6) (k : Fin 3) (a b : _root_.MIPStarRE.QPBT.MsAnswer)
    (hrej : _root_.MIPStarRE.QPBT.msWinPredicate (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) (.constraint i) a b = false) :
    ((_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm
        (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k))).effect a) *
      ((_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm (.constraint i)).effect b) = 0 := by
  rw [(_root_.MIPStarRE.QPBT.msStrategyMeasurement_incident_commute P hP hcomm i k b a).symm.eq]
  exact msStrategyMeasurement_rejected_mul P hP hcomm hmul i k b a
    (by simpa [_root_.MIPStarRE.QPBT.msWinPredicate_symm] using hrej)







/-- Formalization-only auxiliary for the perfect Magic Square strategy and the
proof of `lem:pauli-completeness`: the constructed Magic Square family has
zero operator product on rejected answers in its support, from the stated cell
and joint-measurement identities. -/
theorem msStrategyMeasurement_rejected_mul_on_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) V)
    (hP : ∀ j, _root_.MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect a)
        ((P (_root_.MIPStarRE.QPBT.msConstraintVars i l)).effect b))
    (hmul : ∀ i k ab b,
      (_root_.MIPStarRE.QPBT.msConstraintJoint P hP hcomm i).effect ab *
          (P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect b =
        if _root_.MIPStarRE.QPBT.parityTriple i ab k = b then
          (_root_.MIPStarRE.QPBT.msConstraintJoint P hP hcomm i).effect ab else 0)
    (x y : _root_.MIPStarRE.QPBT.MsType) (hxy : (x, y) ∈ _root_.MIPStarRE.QPBT.msGameSymm.μ.support)
    (a b : _root_.MIPStarRE.QPBT.MsAnswer) (hrej : _root_.MIPStarRE.QPBT.msWinPredicate x y a b = false) :
    ((_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm x).effect a) *
      ((_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm y).effect b) = 0 := by
  rcases _root_.MIPStarRE.QPBT.msGame_support_incidence x y hxy with hxy | hxy
  · rcases hxy with ⟨i, k, rfl, rfl⟩
    exact msStrategyMeasurement_rejected_mul P hP hcomm hmul i k a b hrej
  · rcases hxy with ⟨i, k, rfl, rfl⟩
    exact msStrategyMeasurement_rejected_mul_reverse P hP hcomm hmul i k a b hrej



















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

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (z : _root_.MIPStarRE.QPBT.PauliSpace P)
    {s₁ s₂ : _root_.MIPStarRE.QPBT.MsType} (hms : Sym2.mk s₁ s₂ ∈ _root_.MIPStarRE.QPBT.msEdges) (a b : _root_.MIPStarRE.QPBT.PauliAnswer P)
    (hrej : _root_.MIPStarRE.QPBT.pauliWinPredicate P (.ms s₁, _root_.MIPStarRE.QPBT.pauliCL P (.ms s₁) z)
      (.ms s₂, _root_.MIPStarRE.QPBT.pauliCL P (.ms s₂) z) a b = false) :
    (_root_.MIPStarRE.QPBT.honestMeasurement P (.ms s₁) (_root_.MIPStarRE.QPBT.pauliCL P (.ms s₁) z)).effect a *
      (_root_.MIPStarRE.QPBT.honestMeasurement P (.ms s₂) (_root_.MIPStarRE.QPBT.pauliCL P (.ms s₂) z)).effect b = 0 := by
  classical
  have hcl : ∀ s : _root_.MIPStarRE.QPBT.MsType, _root_.MIPStarRE.QPBT.pauliCL P (_root_.MIPStarRE.QPBT.PauliType.ms s) z = _root_.MIPStarRE.QPBT.pauliSharedProjection z :=
    fun _ => rfl
  simp only [hcl] at hrej ⊢
  have hsupp : (s₁, s₂) ∈ _root_.MIPStarRE.QPBT.msGameSymm.μ.support := by
    change (s₁, s₂) ∈ (Finset.univ : Finset (_root_.MIPStarRE.QPBT.MsType × _root_.MIPStarRE.QPBT.MsType)).filter
      (fun ab => Sym2.mk ab.1 ab.2 ∈ _root_.MIPStarRE.QPBT.msEdges)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hms⟩
  rcases (Bool.eq_false_or_eq_true
    (_root_.MIPStarRE.QPBT.validPauliAnswer (P := P) (_root_.MIPStarRE.QPBT.PauliType.ms s₁) a)).symm with hva | hva
  · rw [_root_.MIPStarRE.QPBT.honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
  rcases (Bool.eq_false_or_eq_true
    (_root_.MIPStarRE.QPBT.validPauliAnswer (P := P) (_root_.MIPStarRE.QPBT.PauliType.ms s₂) b)).symm with hvb | hvb
  · rw [_root_.MIPStarRE.QPBT.honestMeasurement_effect_eq_zero_of_invalid P _ _ hvb, mul_zero]
  obtain ⟨a', rfl⟩ : ∃ c, a = _root_.MIPStarRE.QPBT.pauliAnswerOfMs c := by
    cases a
    case msTriple β => exact ⟨_root_.MIPStarRE.QPBT.MsAnswer.triple β, rfl⟩
    case bit c => exact ⟨_root_.MIPStarRE.QPBT.MsAnswer.bit c, rfl⟩
    all_goals exact absurd hva (by cases s₁ <;> simp [_root_.MIPStarRE.QPBT.validPauliAnswer])
  obtain ⟨b', rfl⟩ : ∃ c, b = _root_.MIPStarRE.QPBT.pauliAnswerOfMs c := by
    cases b
    case msTriple β => exact ⟨_root_.MIPStarRE.QPBT.MsAnswer.triple β, rfl⟩
    case bit c => exact ⟨_root_.MIPStarRE.QPBT.MsAnswer.bit c, rfl⟩
    all_goals exact absurd hvb (by cases s₂ <;> simp [_root_.MIPStarRE.QPBT.validPauliAnswer])
  by_cases hg : _root_.MIPStarRE.QPBT.pauliPairGamma P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) = 0
  · exfalso
    have hpos : _root_.MIPStarRE.QPBT.pauliWinPredicate P (.ms s₁, _root_.MIPStarRE.QPBT.pauliSharedProjection z)
        (.ms s₂, _root_.MIPStarRE.QPBT.pauliSharedProjection z)
        (_root_.MIPStarRE.QPBT.pauliAnswerOfMs a') (_root_.MIPStarRE.QPBT.pauliAnswerOfMs b') = true := by
      clear hrej
      rcases _root_.MIPStarRE.QPBT.msGame_support_incidence s₁ s₂ hsupp with
        ⟨i, k, rfl, rfl⟩ | ⟨i, k, rfl, rfl⟩ <;>
        cases a' <;> cases b' <;>
        simp_all [_root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer, _root_.MIPStarRE.QPBT.pauliAnswerOfMs, _root_.MIPStarRE.QPBT.msWinPredicate]
    rw [hpos] at hrej
    exact Bool.noConfusion hrej
  · have hmsrej : _root_.MIPStarRE.QPBT.msWinPredicate s₁ s₂ a' b' = false := by
      rcases Bool.eq_false_or_eq_true (_root_.MIPStarRE.QPBT.msWinPredicate s₁ s₂ a' b') with hmsw | hmsw
      · exfalso
        have hpos : _root_.MIPStarRE.QPBT.pauliWinPredicate P (.ms s₁, _root_.MIPStarRE.QPBT.pauliSharedProjection z)
            (.ms s₂, _root_.MIPStarRE.QPBT.pauliSharedProjection z)
            (_root_.MIPStarRE.QPBT.pauliAnswerOfMs a') (_root_.MIPStarRE.QPBT.pauliAnswerOfMs b') = true := by
          clear hrej
          rcases _root_.MIPStarRE.QPBT.msGame_support_incidence s₁ s₂ hsupp with
            ⟨i, k, rfl, rfl⟩ | ⟨i, k, rfl, rfl⟩ <;>
            cases a' <;> cases b' <;>
            simp_all [_root_.MIPStarRE.QPBT.pauliWinPredicate, _root_.MIPStarRE.QPBT.validPauliAnswer, _root_.MIPStarRE.QPBT.pauliAnswerOfMs, _root_.MIPStarRE.QPBT.msWinPredicate]
        rw [hpos] at hrej
        exact Bool.noConfusion hrej
      · exact hmsw
    have hM : ∀ s : _root_.MIPStarRE.QPBT.MsType, _root_.MIPStarRE.QPBT.honestMeasurement P (.ms s) (_root_.MIPStarRE.QPBT.pauliSharedProjection z) =
        (_root_.MIPStarRE.QPBT.pauliMagicMeasurement P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) hg s).postprocess
          (_root_.MIPStarRE.QPBT.pauliAnswerOfMs (P := P)) := by
      intro s
      change _root_.MIPStarRE.QPBT.honestMagicMeasurement P s (_root_.MIPStarRE.QPBT.pauliSharedProjection z) = _
      simp [_root_.MIPStarRE.QPBT.honestMagicMeasurement, hg]
    have hmul : ∀ (i : Fin 6) (k : Fin 3) (ab : ZMod 2 × ZMod 2) (c : ZMod 2),
        (_root_.MIPStarRE.QPBT.msConstraintJoint (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) hg)
              (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement_projective P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) hg)
              (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement_commute P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) hg)
              i).effect ab *
            (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) hg
              (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect c =
          if _root_.MIPStarRE.QPBT.parityTriple i ab k = c then
            (_root_.MIPStarRE.QPBT.msConstraintJoint (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) hg)
              (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement_projective P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) hg)
              (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement_commute P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) hg)
              i).effect ab
          else 0 := by
      intro i k ab c
      exact _root_.MIPStarRE.QPBT.msCellConstraintJoint_mul _ _
        (_root_.MIPStarRE.QPBT.obsOf_conjTranspose _ (_root_.MIPStarRE.QPBT.pauliTraceMeasurement_projective P .X
          (_root_.MIPStarRE.QPBT.pauliXBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))
          (_root_.MIPStarRE.QPBT.pauliRXBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))))
        (_root_.MIPStarRE.QPBT.obsOf_conjTranspose _ (_root_.MIPStarRE.QPBT.pauliTraceMeasurement_projective P .Z
          (_root_.MIPStarRE.QPBT.pauliZBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))
          (_root_.MIPStarRE.QPBT.pauliRZBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))))
        (_root_.MIPStarRE.QPBT.obsOf_sq _ (_root_.MIPStarRE.QPBT.pauliTraceMeasurement_projective P .X
          (_root_.MIPStarRE.QPBT.pauliXBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))
          (_root_.MIPStarRE.QPBT.pauliRXBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))))
        (_root_.MIPStarRE.QPBT.obsOf_sq _ (_root_.MIPStarRE.QPBT.pauliTraceMeasurement_projective P .Z
          (_root_.MIPStarRE.QPBT.pauliZBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))
          (_root_.MIPStarRE.QPBT.pauliRZBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))))
        (_root_.MIPStarRE.QPBT.obsOf_pauliTraceMeasurement_anticommute P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) hg)
        i k ab c
    rw [hM s₁, hM s₂,
      _root_.MIPStarRE.QPBT.SandwichProduct.postprocess_effect_of_injective _ _ _root_.MIPStarRE.QPBT.pauliAnswerOfMs_injective a',
      _root_.MIPStarRE.QPBT.SandwichProduct.postprocess_effect_of_injective _ _ _root_.MIPStarRE.QPBT.pauliAnswerOfMs_injective b']
    exact _root_.MIPStarRE.QPBT.msStrategyMeasurement_rejected_mul_on_support _ _ _ hmul s₁ s₂ hsupp a' b' hmsrej
