-- Prove2me | solution 1 for MIPStarRE.QPBT.honestMeasurement_commute_of_oriented
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:05:35.122838+00:00
-- url     : https://prove2.me/submissions/099f257d-2961-42f1-8738-e22b2c4f60c4

-- Generated proof for MIPStarRE.QPBT.honestMeasurement_commute_of_oriented.
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
import Definitions.Def_QPBT_QPBT_Test_Completeness_Commutation
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy_MeasurementFamily
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Measurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_isProj_kronecker
import Theorems.Thm_MIPStarRE_QPBT_exists_placedBasis_of_basisType
import Theorems.Thm_MIPStarRE_QPBT_honestMagicMeasurement_var_eq_placedBasis
import Theorems.Thm_MIPStarRE_QPBT_honestPairW_pair_commute
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

















/-- Coarse-grainings of one Pauli basis measurement commute after tensor
placement. -/
theorem placedPauliMeasurement_commute {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {ζ : Type*} [Fintype ζ] [DecidableEq ζ]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement ζ (_root_.MIPStarRE.QPBT.PauliRegister P))
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M)
    (f g : ζ → _root_.MIPStarRE.QPBT.PauliAnswer P)
    (a b : _root_.MIPStarRE.QPBT.PauliAnswer P) :
    Commute ((_root_.MIPStarRE.QPBT.placedPauliMeasurement M f).effect a)
      ((_root_.MIPStarRE.QPBT.placedPauliMeasurement M g).effect b) := by
  change Commute
    (((_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess f).effect a)
    (((_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M).postprocess g).effect b)
  exact _root_.MIPStarRE.QPBT.postprocess_effect_commute
    (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ZMod 2) M)
    (_root_.MIPStarRE.QPBT.leftPlacedMeasurement_projective M hM) f g a b



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



/-- Honest measurements reading one and the same Pauli basis have commuting
effects, whatever the coefficient vectors carried by their questions. -/
theorem honestMeasurement_basis_commute (P : _root_.MIPStarRE.QPBT.AdmissibleParams) {t₁ t₂ : _root_.MIPStarRE.QPBT.PauliType}
    (W : _root_.MIPStarRE.QPBT.PauliKind) (z₁ z₂ : _root_.MIPStarRE.QPBT.PauliSpace P)
    (h₁ : t₁ = .point W ∨ t₁ = .aline W ∨ t₁ = .dline W ∨ t₁ = .pauli W ∨
      t₁ = .pairW W)
    (h₂ : t₂ = .point W ∨ t₂ = .aline W ∨ t₂ = .dline W ∨ t₂ = .pauli W ∨
      t₂ = .pairW W)
    (a b : _root_.MIPStarRE.QPBT.PauliAnswer P) :
    Commute ((_root_.MIPStarRE.QPBT.honestMeasurement P t₁ z₁).effect a)
      ((_root_.MIPStarRE.QPBT.honestMeasurement P t₂ z₂).effect b) := by
  obtain ⟨f₁, hf₁⟩ := _root_.MIPStarRE.QPBT.exists_placedBasis_of_basisType P t₁ W z₁ h₁
  obtain ⟨f₂, hf₂⟩ := _root_.MIPStarRE.QPBT.exists_placedBasis_of_basisType P t₂ W z₂ h₂
  rw [hf₁, hf₂]
  exact _root_.MIPStarRE.QPBT.placedPauliMeasurement_commute (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W)
    (fun h => _root_.MIPStarRE.QPBT.pauliProj_isProj W h) f₁ f₂ a b

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







/-! ### Commutation along the Pauli type graph -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    {t₁ t₂ : _root_.MIPStarRE.QPBT.PauliType} (h : _root_.MIPStarRE.QPBT.PauliEdgeOriented t₁ t₂) (z : _root_.MIPStarRE.QPBT.PauliSpace P)
    (a b : _root_.MIPStarRE.QPBT.PauliAnswer P) :
    Commute ((_root_.MIPStarRE.QPBT.honestMeasurement P t₁ (_root_.MIPStarRE.QPBT.pauliCL P t₁ z)).effect a)
      ((_root_.MIPStarRE.QPBT.honestMeasurement P t₂ (_root_.MIPStarRE.QPBT.pauliCL P t₂ z)).effect b) := by
  classical
  rcases h with ⟨W, rfl, hW⟩ | ⟨W, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine _root_.MIPStarRE.QPBT.honestMeasurement_basis_commute P W _ _ (Or.inl rfl) ?_ a b
    rcases hW with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · exact _root_.MIPStarRE.QPBT.honestPairW_pair_commute P W (_root_.MIPStarRE.QPBT.pauliSharedProjection z) a b
  · by_cases hg : _root_.MIPStarRE.QPBT.pauliPairGamma P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) = 0
    · have hdet : _root_.MIPStarRE.QPBT.honestMagicMeasurement P (.var 0) (_root_.MIPStarRE.QPBT.pauliSharedProjection z) =
          _root_.MIPStarRE.QPBT.deterministicMeasurement (V := _root_.MIPStarRE.QPBT.HonestIndex P)
            (_root_.MIPStarRE.QPBT.PauliAnswer.bit 0) := by
        simp [_root_.MIPStarRE.QPBT.honestMagicMeasurement, hg]
      change Commute ((_root_.MIPStarRE.QPBT.honestMeasurement P (.point .X) _).effect a)
        ((_root_.MIPStarRE.QPBT.honestMagicMeasurement P (.var 0) (_root_.MIPStarRE.QPBT.pauliSharedProjection z)).effect b)
      rw [hdet]
      exact (_root_.MIPStarRE.QPBT.deterministicMeasurement_effect_commute _ _ _).symm
    · obtain ⟨f₁, hf₁⟩ := _root_.MIPStarRE.QPBT.exists_placedBasis_of_basisType P (.point .X) .X
        (_root_.MIPStarRE.QPBT.pauliCL P (.point .X) z) (Or.inl rfl)
      have h₂ : _root_.MIPStarRE.QPBT.honestMagicMeasurement P (.var 0) (_root_.MIPStarRE.QPBT.pauliSharedProjection z) =
          _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliBasisMeasurement .X)
            (fun h => .bit (_root_.MIPStarRE.QPBT.pauliTraceBit P
              (_root_.MIPStarRE.QPBT.pauliXBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))
              (_root_.MIPStarRE.QPBT.pauliRXBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z)) h)) :=
        (_root_.MIPStarRE.QPBT.honestMagicMeasurement_var_eq_placedBasis P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) hg).1
      change Commute ((_root_.MIPStarRE.QPBT.honestMeasurement P (.point .X) _).effect a)
        ((_root_.MIPStarRE.QPBT.honestMagicMeasurement P (.var 0) (_root_.MIPStarRE.QPBT.pauliSharedProjection z)).effect b)
      rw [hf₁, h₂]
      exact _root_.MIPStarRE.QPBT.placedPauliMeasurement_commute (_root_.MIPStarRE.QPBT.pauliBasisMeasurement .X)
        (fun h => _root_.MIPStarRE.QPBT.pauliProj_isProj .X h) f₁ _ a b
  · by_cases hg : _root_.MIPStarRE.QPBT.pauliPairGamma P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) = 0
    · have hdet : _root_.MIPStarRE.QPBT.honestMagicMeasurement P (.var 4) (_root_.MIPStarRE.QPBT.pauliSharedProjection z) =
          _root_.MIPStarRE.QPBT.deterministicMeasurement (V := _root_.MIPStarRE.QPBT.HonestIndex P)
            (_root_.MIPStarRE.QPBT.PauliAnswer.bit 0) := by
        simp [_root_.MIPStarRE.QPBT.honestMagicMeasurement, hg]
      change Commute ((_root_.MIPStarRE.QPBT.honestMeasurement P (.point .Z) _).effect a)
        ((_root_.MIPStarRE.QPBT.honestMagicMeasurement P (.var 4) (_root_.MIPStarRE.QPBT.pauliSharedProjection z)).effect b)
      rw [hdet]
      exact (_root_.MIPStarRE.QPBT.deterministicMeasurement_effect_commute _ _ _).symm
    · obtain ⟨f₁, hf₁⟩ := _root_.MIPStarRE.QPBT.exists_placedBasis_of_basisType P (.point .Z) .Z
        (_root_.MIPStarRE.QPBT.pauliCL P (.point .Z) z) (Or.inl rfl)
      have h₂ : _root_.MIPStarRE.QPBT.honestMagicMeasurement P (.var 4) (_root_.MIPStarRE.QPBT.pauliSharedProjection z) =
          _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliBasisMeasurement .Z)
            (fun h => .bit (_root_.MIPStarRE.QPBT.pauliTraceBit P
              (_root_.MIPStarRE.QPBT.pauliZBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z))
              (_root_.MIPStarRE.QPBT.pauliRZBlock (_root_.MIPStarRE.QPBT.pauliSharedProjection z)) h)) :=
        (_root_.MIPStarRE.QPBT.honestMagicMeasurement_var_eq_placedBasis P (_root_.MIPStarRE.QPBT.pauliSharedProjection z) hg).2
      change Commute ((_root_.MIPStarRE.QPBT.honestMeasurement P (.point .Z) _).effect a)
        ((_root_.MIPStarRE.QPBT.honestMagicMeasurement P (.var 4) (_root_.MIPStarRE.QPBT.pauliSharedProjection z)).effect b)
      rw [hf₁, h₂]
      exact _root_.MIPStarRE.QPBT.placedPauliMeasurement_commute (_root_.MIPStarRE.QPBT.pauliBasisMeasurement .Z)
        (fun h => _root_.MIPStarRE.QPBT.pauliProj_isProj .Z h) f₁ _ a b
