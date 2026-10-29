-- Prove2me | solution 1 for MIPStarRE.QPBT.honestMagicMeasurement_effect_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:01:05.881857+00:00
-- url     : https://prove2.me/submissions/4ea0a43e-3af8-4f40-980a-909b0f858a7c

-- Generated proof for MIPStarRE.QPBT.honestMagicMeasurement_effect_eq_zero.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy_MeasurementFamily
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Measurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

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









/-- A deterministic measurement has zero effect away from its prescribed
outcome. -/
theorem deterministicMeasurement_effect_eq_zero_of_ne {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]
    {a₀ a : α} (ha : a ≠ a₀) :
    (_root_.MIPStarRE.QPBT.deterministicMeasurement (V := V) a₀).effect a = 0 := by
  rw [show _root_.MIPStarRE.QPBT.deterministicMeasurement (V := V) a₀ =
      (_root_.MIPStarRE.QPBT.unitMeasurement V).postprocess (fun _ => a₀) by rfl]
  apply _root_.MIPStarRE.QPBT.postprocess_effect_eq_zero_of_notMem
  rintro ⟨u, hu⟩
  exact ha hu.symm























/-! ### The total honest measurement family -/









































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

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (s : _root_.MIPStarRE.QPBT.MsType) (z : _root_.MIPStarRE.QPBT.PauliSpace P) {a : _root_.MIPStarRE.QPBT.PauliAnswer P}
    (ha : _root_.MIPStarRE.QPBT.validPauliAnswer (.ms s) a = false) :
    (_root_.MIPStarRE.QPBT.honestMagicMeasurement P s z).effect a = 0 := by
  classical
  cases s with
  | constraint i =>
      by_cases hg : _root_.MIPStarRE.QPBT.pauliPairGamma P z = 0
      · have h1 : _root_.MIPStarRE.QPBT.honestMagicMeasurement P (.constraint i) z =
            _root_.MIPStarRE.QPBT.deterministicMeasurement (V := _root_.MIPStarRE.QPBT.HonestIndex P)
              (_root_.MIPStarRE.QPBT.PauliAnswer.msTriple 0 : _root_.MIPStarRE.QPBT.PauliAnswer P) := by
          simp [_root_.MIPStarRE.QPBT.honestMagicMeasurement, hg]
        rw [h1]
        refine _root_.MIPStarRE.QPBT.deterministicMeasurement_effect_eq_zero_of_ne ?_
        rintro rfl
        simp [_root_.MIPStarRE.QPBT.validPauliAnswer] at ha
      · have h1 : _root_.MIPStarRE.QPBT.honestMagicMeasurement P (.constraint i) z =
            (_root_.MIPStarRE.QPBT.pauliMagicMeasurement P z hg (.constraint i)).postprocess
              (_root_.MIPStarRE.QPBT.pauliAnswerOfMs (P := P)) := by
          simp [_root_.MIPStarRE.QPBT.honestMagicMeasurement, hg]
        rw [h1, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
        refine Finset.sum_eq_zero fun c hc => ?_
        have hca : _root_.MIPStarRE.QPBT.pauliAnswerOfMs c = a := (Finset.mem_filter.mp hc).2
        cases c with
        | triple β =>
            exact absurd ha (by rw [← hca]; simp [_root_.MIPStarRE.QPBT.pauliAnswerOfMs, _root_.MIPStarRE.QPBT.validPauliAnswer])
        | bit β =>
            refine _root_.MIPStarRE.QPBT.msStrategyMeasurement_constraint_zero _ _ _ i ?_
            rintro ⟨ab, hab⟩
            exact _root_.MIPStarRE.QPBT.MsAnswer.noConfusion hab
  | var j =>
      by_cases hg : _root_.MIPStarRE.QPBT.pauliPairGamma P z = 0
      · have h1 : _root_.MIPStarRE.QPBT.honestMagicMeasurement P (.var j) z =
            _root_.MIPStarRE.QPBT.deterministicMeasurement (V := _root_.MIPStarRE.QPBT.HonestIndex P)
              (_root_.MIPStarRE.QPBT.PauliAnswer.bit 0 : _root_.MIPStarRE.QPBT.PauliAnswer P) := by
          simp [_root_.MIPStarRE.QPBT.honestMagicMeasurement, hg]
        rw [h1]
        refine _root_.MIPStarRE.QPBT.deterministicMeasurement_effect_eq_zero_of_ne ?_
        rintro rfl
        simp [_root_.MIPStarRE.QPBT.validPauliAnswer] at ha
      · have h1 : _root_.MIPStarRE.QPBT.honestMagicMeasurement P (.var j) z =
            (_root_.MIPStarRE.QPBT.pauliMagicMeasurement P z hg (.var j)).postprocess
              (_root_.MIPStarRE.QPBT.pauliAnswerOfMs (P := P)) := by
          simp [_root_.MIPStarRE.QPBT.honestMagicMeasurement, hg]
        rw [h1, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
        refine Finset.sum_eq_zero fun c hc => ?_
        have hca : _root_.MIPStarRE.QPBT.pauliAnswerOfMs c = a := (Finset.mem_filter.mp hc).2
        cases c with
        | triple β =>
            refine _root_.MIPStarRE.QPBT.msStrategyMeasurement_var_zero _ _ _ j ?_
            rintro ⟨b, hb⟩
            exact _root_.MIPStarRE.QPBT.MsAnswer.noConfusion hb
        | bit β =>
            exact absurd ha (by rw [← hca]; simp [_root_.MIPStarRE.QPBT.pauliAnswerOfMs, _root_.MIPStarRE.QPBT.validPauliAnswer])
