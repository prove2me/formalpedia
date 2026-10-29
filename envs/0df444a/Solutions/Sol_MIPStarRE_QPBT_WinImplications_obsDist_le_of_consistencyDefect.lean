-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.obsDist_le_of_consistencyDefect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:08:33.345242+00:00
-- url     : https://prove2.me/submissions/18daae03-e12c-404d-89d2-41e3bd9736ae

-- Generated proof for MIPStarRE.QPBT.WinImplications.obsDist_le_of_consistencyDefect.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_PointObs
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Basic
import Mathlib
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

/- Source helpers from QPBT/Observables/WinImplications/AnticommutingObs.lean. -/
/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/













/-! ## Reflections and the product transfer -/











/-! ## From the Magic Square variables to the point observables -/

/-- The signed sum of the effects of a binary measurement is its observable.
Formalization-only support for `lem:povm-to-obs`, blueprint
`ch14_qpbt_observables.tex:365-382`. -/
theorem sum_phaseSign_smul_effect_eq_obsOf {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) ι) :
    ∑ b : ZMod 2, _root_.MIPStarRE.QPBT.phaseSign b • M.effect b = _root_.MIPStarRE.QPBT.obsOf M := by
  rw [_root_.MIPStarRE.QPBT.sum_zmod_two, _root_.MIPStarRE.QPBT.obsOf]
  have hzero : _root_.MIPStarRE.QPBT.phaseSign (0 : ZMod 2) = 1 := by simp [_root_.MIPStarRE.QPBT.phaseSign]
  have hone : _root_.MIPStarRE.QPBT.phaseSign (1 : ZMod 2) = -1 := by
    have h : (1 : ZMod 2) ≠ 0 := by decide
    simp [_root_.MIPStarRE.QPBT.phaseSign, h]
  rw [hzero, hone, one_smul, neg_one_smul]
  abel







/-! ## The anticommuting half of the twisted commutation -/





















end WinImplications

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/Interchange.lean. -/
/-!
# Interchange of the tensor factors in the winning implications

This module collects the statements shared by the operator-distance companions
of the winning implications and by their factor-interchanged forms: transport of
the state-dependent distance along the interchange of the two tensor factors,
the constant-factor passage from consistency to distance, the reversed
verifier edges, and the clause-by-clause symmetry of the Pauli win predicate
on the ordered type pairs that the implications use.

## References

The declarations support the trailing clause of `lem:qld-win-implications` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:616-706`. Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`,
whose closing sentences at lines 227 and 263-264 state both companions.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Transport of the distance functional along the factor interchange -/













/-- Consistency bounds the state-dependent distance of two oppositely placed
measurement families. This is the first item of `fact:agreement`, blueprint
`ch12_qpbt_games.tex:260-276`, in the placed form used by the trailing clause
of `lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:699-701`,
paper `14_analysis_of_the_pauli_basis_test.tex:263-264`. -/
theorem opFamilyDistSq_placed_le_two_mul_consistencyDefect
    {X α ιA ιB : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ ≤
      2 * _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ :=
  _root_.MIPStarRE.QPBT.opFamilyDistSq_le_two_mul_consistencyDefect μ
    (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (A x))
    (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (B x)) ψ

/-- Consistency at level `c` gives operator distance at level `2 * c` for two
oppositely placed measurement families. This is the quantitative form of
`fact:agreement`, blueprint `ch12_qpbt_games.tex:260-276`, used by the trailing
clause of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:699-701`, paper
`14_analysis_of_the_pauli_basis_test.tex:263-264`. -/
theorem opFamilyDistSq_placed_le_of_consistencyDefect_le
    {X α ιA ιB : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) {c : ℝ}
    (h : _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
      (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ ≤ c) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
      (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ ≤ 2 * c := by
  have hstep := _root_.MIPStarRE.QPBT.WinImplications.opFamilyDistSq_placed_le_two_mul_consistencyDefect μ A B ψ
  linarith

/-! ## Reversed verifier edges

The Pauli type graph is a set of unordered pairs, so every ordered edge used by
the exact implications has its reverse in the graph. The reversed edges carry
the interchanged conclusions of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:701-703`. -/













/-! ## Symmetry of the win predicate on the subtests used here

`def:pauli-win-predicate` lists every clause together with its mirror image, so
on each ordered type pair occurring in `lem:qld-win-implications` exchanging the
two questions and the two answers leaves the predicate unchanged. Paper
`08_classical_and_quantum_low_degree_tests.tex:1126-1225`, blueprint
`ch13_qpbt_test.tex:410-449`. -/













/-! ## Numeric bookkeeping -/





end WinImplications

end

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
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/













/-! ## Reflections and the product transfer -/











/-! ## From the Magic Square variables to the point observables -/

theorem solution {X ιL ιR : Type*}
    [Fintype X] [DecidableEq X] [Fintype ιL] [DecidableEq ιL]
    [Fintype ιR] [DecidableEq ιR] (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X)
    (M : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) ιL)
    (N : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) ιR)
    (χ : EuclideanSpace ℂ (ιL × ιR)) {c : ℝ}
    (h : _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((M x).effect a) 1)
      (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((N x).effect a)) χ ≤ c) :
    _root_.MIPStarRE.QPBT.opDistSq μ (fun x => _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.obsOf (M x)) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR))
      (fun x => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (_root_.MIPStarRE.QPBT.obsOf (N x))) χ ≤ 4 * c := by
  classical
  set A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) (ιL × ιR) := fun x =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ιR) (M x) with hAdef
  set B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) (ιL × ιR) := fun x =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := ιL) (N x) with hBdef
  have hfam : _root_.MIPStarRE.QPBT.opFamilyDistSq μ
      (fun x b => (A x).effect b) (fun x b => (B x).effect b) χ ≤ 2 * c :=
    _root_.MIPStarRE.QPBT.WinImplications.opFamilyDistSq_placed_le_of_consistencyDefect_le μ M N χ h
  have hobs := _root_.MIPStarRE.QPBT.povm_to_obs_of_measurements μ A B _root_.MIPStarRE.QPBT.phaseSign _root_.MIPStarRE.QPBT.WinImplications.norm_phaseSign χ
  have hleft : ∀ x, (∑ b : ZMod 2, _root_.MIPStarRE.QPBT.phaseSign b • (A x).effect b) =
      _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.obsOf (M x)) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) := by
    intro x
    rw [← _root_.MIPStarRE.QPBT.WinImplications.sum_phaseSign_smul_effect_eq_obsOf, _root_.MIPStarRE.QPBT.WinImplications.heteroKron_left_sum_smul]
    rfl
  have hright : ∀ x, (∑ b : ZMod 2, _root_.MIPStarRE.QPBT.phaseSign b • (B x).effect b) =
      _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (_root_.MIPStarRE.QPBT.obsOf (N x)) := by
    intro x
    rw [← _root_.MIPStarRE.QPBT.WinImplications.sum_phaseSign_smul_effect_eq_obsOf, _root_.MIPStarRE.QPBT.WinImplications.heteroKron_right_sum_smul]
    rfl
  have hrw : _root_.MIPStarRE.QPBT.opDistSq μ (fun x => _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.obsOf (M x)) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR))
      (fun x => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιL) (_root_.MIPStarRE.QPBT.obsOf (N x))) χ =
    _root_.MIPStarRE.QPBT.opDistSq μ (fun x => ∑ b : ZMod 2, _root_.MIPStarRE.QPBT.phaseSign b • (A x).effect b)
      (fun x => ∑ b : ZMod 2, _root_.MIPStarRE.QPBT.phaseSign b • (B x).effect b) χ := by
    congr 1 <;> funext x
    · exact (hleft x).symm
    · exact (hright x).symm
  rw [hrw]
  have hcast : (Fintype.card (ZMod 2) : ℝ) = 2 := by simp
  calc
    _ ≤ (Fintype.card (ZMod 2) : ℝ) * _root_.MIPStarRE.QPBT.opFamilyDistSq μ
        (fun x b => (A x).effect b) (fun x b => (B x).effect b) χ := hobs
    _ ≤ 2 * (2 * c) := by
      rw [hcast]
      exact mul_le_mul_of_nonneg_left hfam (by norm_num)
    _ = 4 * c := by ring
