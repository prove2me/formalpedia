-- Prove2me | solution 1 for MIPStarRE.QPBT.basis_character_opDistSq_le_four_consistencyDefect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:10:09.702555+00:00
-- url     : https://prove2.me/submissions/0330c127-f20f-45d9-b68d-a18adfcba34a

-- Generated proof for MIPStarRE.QPBT.basis_character_opDistSq_le_four_consistencyDefect.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_PointObs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_postprocess_le
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_two_mul_consistencyDefect
import Theorems.Thm_MIPStarRE_QPBT_povm_to_obs

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Extraction/CharacterConsistency.lean. -/
/-!
# Finite-character estimates for extracted observables

Parseval identifies the uniform average over field characters with the sum of
squared outcome norms. A fixed binary basis character instead admits a bound
by four times the consistency defect, using binary postprocessing.

## References

These are finite-dimensional auxiliary results for blueprint
`lem:qld-construct-the-paulis`, Item 2, and paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1542-1551`.
They do not assert the preceding pulled-apart measurement comparison
`eq:qld-pulling-cons`, whose extraction obligation is recorded under
issue Dengnifer/MIPStarRE-QPBT-bak#123 in `docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus
open WinImplications

noncomputable section





/-- Regroup a field-weighted observable by its binary trace label. This is the
postprocessing at paper `14_analysis_of_the_pauli_basis_test.tex:1547-1551`. -/
theorem sum_basis_character_effect_eq {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P) ι)
    (j : Fin P.model.basisDim) :
    (∑ a, _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (P.model.basis j * a)) • A.effect a) =
      ∑ b : ZMod 2, _root_.MIPStarRE.QPBT.phaseSign b •
        (A.postprocess (fun a => _root_.MIPStarRE.QPBT.fixedBinTrace P.model (P.model.basis j * a))).effect b := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun a : _root_.MIPStarRE.QPBT.PauliScalar P => _root_.MIPStarRE.QPBT.fixedBinTrace P.model (P.model.basis j * a))
    (t := (Finset.univ : Finset (ZMod 2))) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro b _
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]





end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/DistanceTheorems.lean. -/
/-! # State-dependent distance calculus

This module records the consistency and state-dependent distance estimates used
throughout the quantum Pauli basis test. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

The operator-level inequalities they rest on live in
`MIPStarRE.QPBT.Games.DistanceTheorems.Calculus`.

## References

The source results run from blueprint `fact:agreement` through
`lem:close-strategies-have-close-values`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-461` and
`:531-540`. The observable conversion lemmas come from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:95-131`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus































/-- Passing from answer-indexed POVM effects to unit-modulus weighted
observables costs at most the answer-alphabet cardinality. This is
blueprint
`lem:povm-to-obs`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:115-129`. -/
theorem povm_to_obs_of_measurements {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (c : α → ℂ) (hc : ∀ a, ‖c a‖ = 1) (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opDistSq μ (fun x => ∑ a, c a • (A x).effect a)
        (fun x => ∑ a, c a • (B x).effect a) ψ ≤
      Fintype.card α * _root_.MIPStarRE.QPBT.opFamilyDistSq μ
        (fun x a => (A x).effect a) (fun x a => (B x).effect a) ψ := by
  exact _root_.MIPStarRE.QPBT.povm_to_obs μ (fun x a => (A x).effect a)
    (fun x a => (B x).effect a) c hc ψ



end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/PointObs.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyPointObs
/-!
# Self-consistency of the strategy point observables

This module converts the trace-coarse-grained point consistency of item 1 of
`lem:qld-win-implications` into the observable relation
`eq:pts-obs-consistency` of `lem:qld-win-implications-obs`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:294-308`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications



/-! ## Linearity of the tensor placement -/

/-- The left tensor placement commutes with weighted finite sums. This is
formalization-only support for `lem:povm-to-obs`, blueprint
`ch14_qpbt_observables.tex:365-382`. -/
theorem heteroKron_left_sum_smul {α ιA ιB : Type*} [Fintype α]
    (c : α → ℂ) (A : α → _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron (∑ a, c a • A a) B = ∑ a, c a • _root_.MIPStarRE.QPBT.heteroKron (A a) B := by
  ext i j
  simp only [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul,
    mul_assoc]

/-- The right tensor placement commutes with weighted finite sums. This is
formalization-only support for `lem:povm-to-obs`, blueprint
`ch14_qpbt_observables.tex:365-382`. -/
theorem heteroKron_right_sum_smul {α ιA ιB : Type*} [Fintype α]
    (c : α → ℂ) (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : α → _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron A (∑ a, c a • B a) = ∑ a, c a • _root_.MIPStarRE.QPBT.heteroKron A (B a) := by
  ext i j
  simp only [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The binary phase character has unit modulus. Paper
`references/qpbt-paper/04_preliminaries.tex:1052-1081`. -/
theorem norm_phaseSign (t : ZMod 2) : ‖_root_.MIPStarRE.QPBT.phaseSign t‖ = 1 := by
  by_cases ht : t = 0 <;> simp [_root_.MIPStarRE.QPBT.phaseSign, ht]

/-! ## The point observable as a binary observable -/



/-! ## Trace-coarse-grained point self-consistency -/







/-! ## The observable consistency relation -/



end WinImplications

end

end MIPStarRE.QPBT

/-!
# Finite-character estimates for extracted observables

Parseval identifies the uniform average over field characters with the sum of
squared outcome norms. A fixed binary basis character instead admits a bound
by four times the consistency defect, using binary postprocessing.

## References

These are finite-dimensional auxiliary results for blueprint
`lem:qld-construct-the-paulis`, Item 2, and paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1542-1551`.
They do not assert the preceding pulled-apart measurement comparison
`eq:qld-pulling-cons`, whose extraction obligation is recorded under
issue Dengnifer/MIPStarRE-QPBT-bak#123 in `docs/paper-gaps/qpbt_extraction-transfer.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open MIPStarRE.QPBT.WinImplications

theorem solution
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {X ιA ιB : Type*}
    [Fintype X] [DecidableEq X]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P) ιA)
    (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliScalar P) ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (j : Fin P.model.basisDim) :
    _root_.MIPStarRE.QPBT.opDistSq μ
      (fun x => _root_.MIPStarRE.QPBT.heteroKron
        (∑ a, _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (P.model.basis j * a)) • (A x).effect a) 1)
      (fun x => _root_.MIPStarRE.QPBT.heteroKron 1
        (∑ a, _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (P.model.basis j * a)) • (B x).effect a)) ψ ≤
      4 * _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ := by
  classical
  let f := fun a : _root_.MIPStarRE.QPBT.PauliScalar P => _root_.MIPStarRE.QPBT.fixedBinTrace P.model (P.model.basis j * a)
  let A' := fun x => (A x).postprocess f
  let B' := fun x => (B x).postprocess f
  have hdef := _root_.MIPStarRE.QPBT.consistencyDefect_postprocess_le μ A B ψ f
  have hfam := (_root_.MIPStarRE.QPBT.opFamilyDistSq_le_two_mul_consistencyDefect μ
    (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (A' x))
    (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (B' x)) ψ).trans
      (mul_le_mul_of_nonneg_left hdef (by norm_num : (0 : ℝ) ≤ 2))
  have hobs := _root_.MIPStarRE.QPBT.povm_to_obs_of_measurements μ
    (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (A' x))
    (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (B' x)) _root_.MIPStarRE.QPBT.phaseSign _root_.MIPStarRE.QPBT.WinImplications.norm_phaseSign ψ
  simp only [ZMod.card, Nat.cast_ofNat] at hobs
  have hbound := hobs.trans (mul_le_mul_of_nonneg_left hfam (by norm_num : (0 : ℝ) ≤ 2))
  simpa only [_root_.MIPStarRE.QPBT.sum_basis_character_effect_eq, _root_.MIPStarRE.QPBT.WinImplications.heteroKron_left_sum_smul,
    _root_.MIPStarRE.QPBT.WinImplications.heteroKron_right_sum_smul, _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num]
    using hbound
