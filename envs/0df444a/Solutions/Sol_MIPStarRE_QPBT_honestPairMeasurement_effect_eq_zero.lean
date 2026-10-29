-- Prove2me | solution 1 for MIPStarRE.QPBT.honestPairMeasurement_effect_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:01:05.431+00:00
-- url     : https://prove2.me/submissions/ee704395-a209-4f36-818e-33ad8e400076

-- Generated proof for MIPStarRE.QPBT.honestPairMeasurement_effect_eq_zero.
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
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy_MeasurementFamily
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
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) {a : _root_.MIPStarRE.QPBT.PauliAnswer P}
    (ha : _root_.MIPStarRE.QPBT.validPauliAnswer .pair a = false) :
    (_root_.MIPStarRE.QPBT.honestPairMeasurement P z).effect a = 0 := by
  classical
  by_cases hg : _root_.MIPStarRE.QPBT.pauliPairGamma P z = 0
  · have h1 : _root_.MIPStarRE.QPBT.honestPairMeasurement P z =
        _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliPairMeasurement P z hg)
          (fun c => _root_.MIPStarRE.QPBT.PauliAnswer.pairBits c) := by
      simp [_root_.MIPStarRE.QPBT.honestPairMeasurement, hg]
    rw [h1]
    refine _root_.MIPStarRE.QPBT.placedPauliMeasurement_effect_eq_zero_of_notMem _ _ ?_
    rintro ⟨u, rfl⟩
    simp [_root_.MIPStarRE.QPBT.validPauliAnswer] at ha
  · have h1 : _root_.MIPStarRE.QPBT.honestPairMeasurement P z =
        _root_.MIPStarRE.QPBT.deterministicMeasurement (V := _root_.MIPStarRE.QPBT.HonestIndex P)
          (_root_.MIPStarRE.QPBT.PauliAnswer.pairBits (0, 0)) := by
      simp [_root_.MIPStarRE.QPBT.honestPairMeasurement, hg]
    rw [h1]
    refine _root_.MIPStarRE.QPBT.deterministicMeasurement_effect_eq_zero_of_ne ?_
    rintro rfl
    simp [_root_.MIPStarRE.QPBT.validPauliAnswer] at ha
