-- Prove2me | solution 1 for MIPStarRE.QPBT.honestMagicMeasurement_var_eq_placedBasis
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:57:54.152198+00:00
-- url     : https://prove2.me/submissions/e7965893-dc2b-49d3-aa44-42726520a38f

-- Generated proof for MIPStarRE.QPBT.honestMagicMeasurement_var_eq_placedBasis.
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
import Definitions.Def_QPBT_QPBT_Upstream
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_pauliMagicMeasurement_var_effect
import Theorems.Thm_MIPStarRE_QPBT_placedPauliMeasurement_postprocess_eq

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
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

















end

end MIPStarRE.QPBT

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



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



set_option maxRecDepth 8000

/-! ### The supported question pairs -/







/-! ### Coarse-graining and tensor placement -/













/-! ### Honest measurements sharing a Pauli basis -/





/-! ### The Pair and Magic Square measurements -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (hg : _root_.MIPStarRE.QPBT.pauliPairGamma P z ≠ 0) :
    _root_.MIPStarRE.QPBT.honestMagicMeasurement P (.var 0) z =
        _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliBasisMeasurement .X)
          (fun h => .bit (_root_.MIPStarRE.QPBT.pauliTraceBit P (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliRXBlock z) h)) ∧
      _root_.MIPStarRE.QPBT.honestMagicMeasurement P (.var 4) z =
        _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliBasisMeasurement .Z)
          (fun h => .bit (_root_.MIPStarRE.QPBT.pauliTraceBit P (_root_.MIPStarRE.QPBT.pauliZBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z) h)) := by
  classical
  have hcell : ∀ (j : Fin 9) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
      (r : _root_.MIPStarRE.QPBT.PauliScalar P),
      (∀ b, (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement P z hg j).effect b =
        _root_.MIPStarRE.QPBT.heteroKron ((_root_.MIPStarRE.QPBT.pauliTraceMeasurement P W u r).effect b) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ZMod 2))) →
      _root_.MIPStarRE.QPBT.honestMagicMeasurement P (.var j) z =
        _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W)
          (fun h => .bit (_root_.MIPStarRE.QPBT.pauliTraceBit P u r h)) := by
    intro j W u r hj
    have hstep : _root_.MIPStarRE.QPBT.honestMagicMeasurement P (.var j) z =
        (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement P z hg j).postprocess
          (fun b : ZMod 2 => (_root_.MIPStarRE.QPBT.PauliAnswer.bit b : _root_.MIPStarRE.QPBT.PauliAnswer P)) := by
      have hunfold : _root_.MIPStarRE.QPBT.honestMagicMeasurement P (.var j) z =
          (_root_.MIPStarRE.QPBT.pauliMagicMeasurement P z hg (.var j)).postprocess
            (_root_.MIPStarRE.QPBT.pauliAnswerOfMs (P := P)) := by
        simp [_root_.MIPStarRE.QPBT.honestMagicMeasurement, hg]
      rw [hunfold, show _root_.MIPStarRE.QPBT.pauliMagicMeasurement P z hg (.var j) =
        (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement P z hg j).postprocess _root_.MIPStarRE.QPBT.MsAnswer.bit from rfl,
        _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
      rfl
    have hplaced : _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2)
        (_root_.MIPStarRE.QPBT.pauliTraceMeasurement P W u r) = _root_.MIPStarRE.QPBT.pauliMagicCellMeasurement P z hg j :=
      _root_.LIDT.MIPStarRE.Quantum.Measurement.ext fun b => (hj b).symm
    rw [hstep, ← hplaced]
    exact _root_.MIPStarRE.QPBT.placedPauliMeasurement_postprocess_eq (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W)
      (_root_.MIPStarRE.QPBT.pauliTraceBit P u r) (fun b => _root_.MIPStarRE.QPBT.PauliAnswer.bit b)
  have hA : ∀ b, (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement P z hg 0).effect b =
      _root_.MIPStarRE.QPBT.heteroKron
        ((_root_.MIPStarRE.QPBT.pauliTraceMeasurement P .X (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliRXBlock z)).effect b)
        (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ZMod 2)) := by
    intro b
    rw [← _root_.MIPStarRE.QPBT.msStrategyMeasurement_var_bit (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement P z hg)
      (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement_projective P z hg)
      (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement_commute P z hg) 0 b]
    exact (_root_.MIPStarRE.QPBT.pauliMagicMeasurement_var_effect P z hg b).1
  have hB : ∀ b, (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement P z hg 4).effect b =
      _root_.MIPStarRE.QPBT.heteroKron
        ((_root_.MIPStarRE.QPBT.pauliTraceMeasurement P .Z (_root_.MIPStarRE.QPBT.pauliZBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z)).effect b)
        (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ZMod 2)) := by
    intro b
    rw [← _root_.MIPStarRE.QPBT.msStrategyMeasurement_var_bit (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement P z hg)
      (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement_projective P z hg)
      (_root_.MIPStarRE.QPBT.pauliMagicCellMeasurement_commute P z hg) 4 b]
    exact (_root_.MIPStarRE.QPBT.pauliMagicMeasurement_var_effect P z hg b).2
  exact ⟨hcell 0 .X (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliRXBlock z) hA,
    hcell 4 .Z (_root_.MIPStarRE.QPBT.pauliZBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z) hB⟩
