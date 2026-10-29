-- Prove2me | solution 1 for MIPStarRE.QPBT.honestMeasurement_rejected_mul
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:24:14.230055+00:00
-- url     : https://prove2.me/submissions/174e64df-5858-4811-bbb4-58f838bbce4f

-- Generated proof for MIPStarRE.QPBT.honestMeasurement_rejected_mul.
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
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Test_Completeness
import Definitions.Def_QPBT_QPBT_Test_Completeness_Commutation
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy_MeasurementFamily
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Measurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_honestMagicMeasurement_effect_eq_zero
import Theorems.Thm_MIPStarRE_QPBT_honestMeasurement_commute_of_oriented
import Theorems.Thm_MIPStarRE_QPBT_honestPairMeasurement_effect_eq_zero
import Theorems.Thm_MIPStarRE_QPBT_honest_ms_rejected_mul
import Theorems.Thm_MIPStarRE_QPBT_honest_oriented_rejected_mul
import Theorems.Thm_MIPStarRE_QPBT_pauliEdges_cases
import Theorems.Thm_MIPStarRE_QPBT_pauliQuestionDistribution_pos_incidence

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

/-!
# Completeness of the Pauli basis test

The Pauli basis test admits a symmetric presentation and a value-one SPCC
strategy.

## References

The source statement is blueprint
`lem:pauli-completeness`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1421`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



/-! ### Auxiliary facts about the Pauli question sampler

The two lemmas of this section are formalization-only.  They record that the
uniform law on the Pauli edge type, and the typed bind seeded by it, do not
depend on the finiteness and decidability data used to form them.  The general
identities about finite weighted distributions that this file uses are stated
in `MIPStarRE/QPBT/Games/DistributionAux.lean`.
-/





/-! ### The Pauli question sampler as a typed conditionally linear distribution -/





/-! ### Symmetry of the Pauli basis test -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (x y : _root_.MIPStarRE.QPBT.PauliQuestion P) (hxy : 0 < (_root_.MIPStarRE.QPBT.pauliQuestionDistribution P).weight (x, y))
    (a b : _root_.MIPStarRE.QPBT.PauliAnswer P) (hrej : _root_.MIPStarRE.QPBT.pauliWinPredicate P x y a b = false) :
    (_root_.MIPStarRE.QPBT.honestMeasurement P x.1 x.2).effect a *
      (_root_.MIPStarRE.QPBT.honestMeasurement P y.1 y.2).effect b = 0 := by
  classical
  obtain ⟨z, hedge, hx, hy⟩ := _root_.MIPStarRE.QPBT.pauliQuestionDistribution_pos_incidence P x y hxy
  obtain ⟨t₁, x₁⟩ := x
  obtain ⟨t₂, x₂⟩ := y
  dsimp only at hx hy hedge ⊢
  subst hx
  subst hy
  rcases _root_.MIPStarRE.QPBT.pauliEdges_cases hedge with heq | ⟨s₁, s₂, hs₁, hs₂, hms⟩ | hor | hor
  · rw [heq] at hrej ⊢
    rcases (Bool.eq_false_or_eq_true
      (_root_.MIPStarRE.QPBT.validPauliAnswer (P := P) t₂ a)).symm with hva | hva
    · rw [_root_.MIPStarRE.QPBT.honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
    have hab : a ≠ b := by
      rintro rfl
      rw [show _root_.MIPStarRE.QPBT.pauliWinPredicate P (t₂, _root_.MIPStarRE.QPBT.pauliCL P t₂ z) (t₂, _root_.MIPStarRE.QPBT.pauliCL P t₂ z) a a
          = true from by simp [_root_.MIPStarRE.QPBT.pauliWinPredicate, hva]] at hrej
      exact Bool.noConfusion hrej
    exact _root_.MIPStarRE.QPBT.DistanceCalculus.projective_effect_mul_effect_eq_zero _
      (_root_.MIPStarRE.QPBT.honestMeasurement_projective P t₂ _) hab
  · subst hs₁
    subst hs₂
    exact _root_.MIPStarRE.QPBT.honest_ms_rejected_mul P z hms a b hrej
  · exact _root_.MIPStarRE.QPBT.honest_oriented_rejected_mul P hor z a b hrej
  · rw [← (_root_.MIPStarRE.QPBT.honestMeasurement_commute_of_oriented P hor z b a).eq]
    refine _root_.MIPStarRE.QPBT.honest_oriented_rejected_mul P hor z b a ?_
    rw [_root_.MIPStarRE.QPBT.pauliWinPredicate_symm]
    exact hrej
