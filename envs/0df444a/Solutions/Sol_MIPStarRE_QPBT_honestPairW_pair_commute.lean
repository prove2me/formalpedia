-- Prove2me | solution 1 for MIPStarRE.QPBT.honestPairW_pair_commute
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:01:05.757105+00:00
-- url     : https://prove2.me/submissions/3d1dbece-9ddd-490f-b828-cc680bcd4fb3

-- Generated proof for MIPStarRE.QPBT.honestPairW_pair_commute.
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
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy_MeasurementFamily
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Measurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_postprocess_effect_commute

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









/-- Commutation is preserved when both operators are placed on the first
tensor factor. -/
theorem leftPlaced_commute {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    {A B : _root_.LIDT.MIPStarRE.Quantum.Op V} (h : Commute A B) :
    Commute (_root_.MIPStarRE.QPBT.heteroKron A (1 : _root_.LIDT.MIPStarRE.Quantum.Op W)) (_root_.MIPStarRE.QPBT.heteroKron B (1 : _root_.LIDT.MIPStarRE.Quantum.Op W)) := by
  rw [commute_iff_eq, _root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.heteroKron_mul, h.eq]













/-! ### The total honest measurement family -/









































end

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



/-- Placed measurements of the Pauli register with pairwise commuting effects
have commuting effects. -/
theorem placedPauliMeasurement_commute_of_commute {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α (_root_.MIPStarRE.QPBT.PauliRegister P)) (N : _root_.LIDT.MIPStarRE.Quantum.Measurement β (_root_.MIPStarRE.QPBT.PauliRegister P))
    (h : ∀ x y, Commute (M.effect x) (N.effect y))
    (f : α → _root_.MIPStarRE.QPBT.PauliAnswer P) (g : β → _root_.MIPStarRE.QPBT.PauliAnswer P) (a b : _root_.MIPStarRE.QPBT.PauliAnswer P) :
    Commute ((_root_.MIPStarRE.QPBT.placedPauliMeasurement M f).effect a)
      ((_root_.MIPStarRE.QPBT.placedPauliMeasurement N g).effect b) := by
  rw [_root_.MIPStarRE.QPBT.placedPauliMeasurement_effect_eq, _root_.MIPStarRE.QPBT.placedPauliMeasurement_effect_eq]
  refine _root_.MIPStarRE.QPBT.leftPlaced_commute ?_
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  exact Commute.sum_left _ _ _ fun x _ => Commute.sum_right _ _ _ fun y _ => h x y

/-- The deterministic measurement reports its prescribed outcome with the
identity effect. -/
theorem deterministicMeasurement_effect_self {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V] (a₀ : α) :
    (_root_.MIPStarRE.QPBT.deterministicMeasurement (V := V) a₀).effect a₀ = 1 := by
  change ((_root_.MIPStarRE.QPBT.unitMeasurement V).postprocess (fun _ => a₀)).effect a₀ = 1
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp [_root_.MIPStarRE.QPBT.unitMeasurement, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne]

/-- Every effect of a deterministic measurement commutes with every
operator. -/
theorem deterministicMeasurement_effect_commute {α V : Type*}
    [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V]
    (a₀ a : α) (A : _root_.LIDT.MIPStarRE.Quantum.Op V) :
    Commute ((_root_.MIPStarRE.QPBT.deterministicMeasurement (V := V) a₀).effect a) A := by
  by_cases h : a = a₀
  · subst h
    rw [_root_.MIPStarRE.QPBT.deterministicMeasurement_effect_self]
    exact Commute.one_left A
  · rw [_root_.MIPStarRE.QPBT.deterministicMeasurement_effect_eq_zero_of_ne h]
    exact Commute.zero_left A

/-! ### Honest measurements sharing a Pauli basis -/





/-! ### The Pair and Magic Square measurements -/







/-! ### Commutation along the Pauli type graph -/





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

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) (a b : _root_.MIPStarRE.QPBT.PauliAnswer P) :
    Commute ((_root_.MIPStarRE.QPBT.honestPairWMeasurement P W z).effect a)
      ((_root_.MIPStarRE.QPBT.honestPairMeasurement P z).effect b) := by
  classical
  by_cases hg : _root_.MIPStarRE.QPBT.pauliPairGamma P z = 0
  · have hpair : _root_.MIPStarRE.QPBT.honestPairMeasurement P z =
        _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliPairMeasurement P z hg)
          (fun c => _root_.MIPStarRE.QPBT.PauliAnswer.pairBits c) := by
      simp [_root_.MIPStarRE.QPBT.honestPairMeasurement, hg]
    rw [hpair]
    refine _root_.MIPStarRE.QPBT.placedPauliMeasurement_commute_of_commute _ _ ?_ _ _ a b
    intro x c
    cases W with
    | X =>
        exact Commute.mul_right
          (_root_.MIPStarRE.QPBT.postprocess_effect_commute (_root_.MIPStarRE.QPBT.pauliBasisMeasurement .X)
            (fun h => _root_.MIPStarRE.QPBT.pauliProj_isProj .X h)
            (_root_.MIPStarRE.QPBT.pauliTraceBit P (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliRXBlock z))
            (_root_.MIPStarRE.QPBT.pauliTraceBit P (_root_.MIPStarRE.QPBT.pauliXBlock z) (_root_.MIPStarRE.QPBT.pauliRXBlock z)) x c.1)
          (_root_.MIPStarRE.QPBT.pauliTraceMeasurement_effect_commute P z hg x c.2)
    | Z =>
        exact Commute.mul_right
          ((_root_.MIPStarRE.QPBT.pauliTraceMeasurement_effect_commute P z hg c.1 x).symm)
          (_root_.MIPStarRE.QPBT.postprocess_effect_commute (_root_.MIPStarRE.QPBT.pauliBasisMeasurement .Z)
            (fun h => _root_.MIPStarRE.QPBT.pauliProj_isProj .Z h)
            (_root_.MIPStarRE.QPBT.pauliTraceBit P (_root_.MIPStarRE.QPBT.pauliZBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z))
            (_root_.MIPStarRE.QPBT.pauliTraceBit P (_root_.MIPStarRE.QPBT.pauliZBlock z) (_root_.MIPStarRE.QPBT.pauliRZBlock z)) x c.2)
  · have hpair : _root_.MIPStarRE.QPBT.honestPairMeasurement P z =
        _root_.MIPStarRE.QPBT.deterministicMeasurement (V := _root_.MIPStarRE.QPBT.HonestIndex P)
          (_root_.MIPStarRE.QPBT.PauliAnswer.pairBits (0, 0)) := by
      simp [_root_.MIPStarRE.QPBT.honestPairMeasurement, hg]
    rw [hpair]
    exact (_root_.MIPStarRE.QPBT.deterministicMeasurement_effect_commute _ _ _).symm
