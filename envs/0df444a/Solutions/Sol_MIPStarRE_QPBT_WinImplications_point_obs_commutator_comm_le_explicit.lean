-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:37:32.307345+00:00
-- url     : https://prove2.me/submissions/948b1022-e909-4fb0-87ee-7ab8469073e2

-- Generated proof for MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_explicit.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_CommutingObs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_point_trace_commutator_comm_le_explicit
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_trans_le
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_two_mul_consistencyDefect
import Theorems.Thm_MIPStarRE_QPBT_sum_indicatorVec_mul_indicatorVec

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Games/Defs.lean. -/
/-!
# Games, tensor-product strategies, and value

This file provides the finite game carrier used by the Pauli basis test.  Pure
states are vectors in `EuclideanSpace`, and POVMs use the project's matrix
`Measurement` structure.

## References

The source-facing nodes are blueprint `def:game`, `def:povm-conventions`,
`def:tensor-product-strategy`, and `def:tensor-product-value`.
The paper origin is `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:10-57`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



attribute [instance] _root_.MIPStarRE.QPBT.Game.questionAFintype _root_.MIPStarRE.QPBT.Game.questionBFintype
  _root_.MIPStarRE.QPBT.Game.answerAFintype _root_.MIPStarRE.QPBT.Game.answerBFintype _root_.MIPStarRE.QPBT.Game.questionADecidableEq
  _root_.MIPStarRE.QPBT.Game.questionBDecidableEq _root_.MIPStarRE.QPBT.Game.answerADecidableEq _root_.MIPStarRE.QPBT.Game.answerBDecidableEq









attribute [instance] _root_.MIPStarRE.QPBT.Strategy.ιAFintype _root_.MIPStarRE.QPBT.Strategy.ιBFintype
  _root_.MIPStarRE.QPBT.Strategy.ιADecidableEq _root_.MIPStarRE.QPBT.Strategy.ιBDecidableEq



/-! ### Algebra of the tensor placement

The shared tensor-placement API.  These identities are used both by the perfect
Magic Square strategy (blueprint `thm:ms-from-ac`) and by the rigidity transfer
step (blueprint `thm:ms-rigidity`), so they live
with the definition rather than in either development. -/













/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`: the
tensor placement of possibly rectangular matrices respects differences in the
left factor.  This is the general form of `heteroKron_sub_left` below, needed
where the left factor is the matrix of an isometry between distinct index
types (blueprint
`thm:ms-rigidity`). -/
theorem kroneckerMap_sub_left {m n p q : Type*} (A B : Matrix m n ℂ) (C : Matrix p q ℂ) :
    Matrix.kroneckerMap (· * ·) (A - B) C =
      Matrix.kroneckerMap (· * ·) A C - Matrix.kroneckerMap (· * ·) B C := by
  ext p' q'
  simp [Matrix.kroneckerMap, sub_mul]



/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
respects differences in the left factor. -/
theorem heteroKron_sub_left {ιA ιB : Type*} (A B : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (C : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron (A - B) C = _root_.MIPStarRE.QPBT.heteroKron A C - _root_.MIPStarRE.QPBT.heteroKron B C :=
  _root_.MIPStarRE.QPBT.kroneckerMap_sub_left A B C



/- The Euclidean linear map is the shared action used by the value and distance
functionals.  Keeping it at the Euclidean-space level avoids accidentally
using the function-space supremum norm of `Matrix.mulVec`. -/








































end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/Anticommuting.lean. -/
/-!
# Commuting and anticommuting Pauli tuples

This module defines the tuple phase used in the Pauli basis test and the
conditional uniform distributions used by its observable analysis.

## References

The definitions and probability bounds formalize blueprint
`def:anticommuting-tuple` and `fact:omega-anticomm-prob`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:64-95`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section















/-! ### Auxiliary counting lemmas

The declarations of this section are formalization-only auxiliaries for the
proof of blueprint
`fact:omega-anticomm-prob`. They record the cardinalities used by the
exact computation of the anticommuting probability. -/

/-- Formalization-only auxiliary: the scalar carrier of an admissible parameter
tuple has characteristic two, since it is an algebra over the two-element
field. Blueprint `fact:omega-anticomm-prob`. -/
private theorem pauliScalar_charTwo (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    CharP (_root_.MIPStarRE.QPBT.PauliScalar P) 2 :=
  (Algebra.charP_iff (ZMod 2) (_root_.MIPStarRE.QPBT.PauliScalar P) 2).mp (ZMod.charP 2)



/-- The phase bit of a Pauli tuple is the trace of `r_Z r_X` times the product
of the coordinate sums `1 + u_{X,i} + u_{Z,i}`. This is the closed form of
`γ(ω)` derived in the proof of blueprint
`fact:omega-anticomm-prob`. -/
private theorem gammaValue_eq_trace_prod (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (uX uZ : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (rX rZ : _root_.MIPStarRE.QPBT.PauliScalar P) :
    _root_.MIPStarRE.QPBT.gammaValue P uX uZ rX rZ =
      _root_.MIPStarRE.QPBT.fixedBinTrace P.model (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) := by
  haveI := pauliScalar_charTwo P
  have hprod : (∑ y : _root_.MIPStarRE.QPBT.Cube P.m, _root_.MIPStarRE.QPBT.indicatorVec uX y * _root_.MIPStarRE.QPBT.indicatorVec uZ y)
      = ∏ i : Fin P.m, (1 + uX i + uZ i) :=
    _root_.MIPStarRE.QPBT.sum_indicatorVec_mul_indicatorVec uX uZ
  unfold _root_.MIPStarRE.QPBT.gammaValue
  congr 1
  rw [← hprod]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring











/-! ### The exact anticommuting probability -/













/-! ### Conditional uniform distributions -/







/-- The commuting conditional distribution is probabilistic. This is the
well-formedness companion to the conditional sampling in
blueprint `lem:qld-win-implications`. -/
theorem commTupleDist_isProbability (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (_root_.MIPStarRE.QPBT.commTupleDist P).IsProbability := by
  refine _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset_isProbability _ ⟨0, ?_⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  change _root_.MIPStarRE.QPBT.gammaValue P 0 0 0 0 = 0
  rw [gammaValue_eq_trace_prod]
  simp [_root_.MIPStarRE.QPBT.fixedBinTrace, _root_.MIPStarRE.QPBT.binTrace]

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

/- Source helpers from QPBT/Observables/WinImplications/CommutingObs.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyCommObs
/-!
# Approximate commutation of the point observables on commuting tuples

This module carries out the commuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`: the chain of
consistency relations `eq:lc-11`, the commutation analysis
`lem:commutation-analysis`, and the expansion `eq:lc-12` of the observables in
terms of the trace-coarse-grained point projections.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-341`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications



/-! ## Algebraic preliminaries -/

/-- The left tensor placement is homogeneous in its left factor.
Formalization-only support for `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-341`. -/
theorem heteroKron_smul_left {ιA ιB : Type*} (c : ℂ) (M : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron (c • M) B = c • _root_.MIPStarRE.QPBT.heteroKron M B := by
  ext i j
  simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, mul_assoc]

/-- The commutator of two reflections written as `1 - 2P` is four times the
commutator of the projections. This is the algebra of Equation `eq:lc-12`,
paper `14_analysis_of_the_pauli_basis_test.tex:330-341`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem reflection_commutator_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (1 - (2 : ℂ) • A) * (1 - (2 : ℂ) • B) -
        (1 - (2 : ℂ) • B) * (1 - (2 : ℂ) • A) =
      (4 : ℂ) • (A * B - B * A) := by
  have h2 : ∀ M : _root_.LIDT.MIPStarRE.Quantum.Op ι, (2 : ℂ) • M = M + M := fun M => two_smul ℂ M
  have h4 : ∀ M : _root_.LIDT.MIPStarRE.Quantum.Op ι, (4 : ℂ) • M = M + M + (M + M) := by
    intro M
    rw [show (4 : ℂ) = 2 + 2 by norm_num, add_smul, h2]
  rw [h2, h2, h4]
  noncomm_ring



/-! ## Pair/W self-consistency on commuting tuples -/





/-! ## The chained relation of Equation `eq:lc-11` -/

/-- Chaining the commuting-case consistency relations gives the point/Pair
relation `eq:lc-11`. The statement is generic in the two tensor factors and in
the state, so that both orientations of `eq:pts-obs-commutation` use it. Paper
`14_analysis_of_the_pauli_basis_test.tex:311-322`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem pointTrace_pairComponent_dist_le {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    {ιL ιR : Type} [Fintype ιL] [DecidableEq ιL] [Fintype ιR] [DecidableEq ιR]
    (MP QL : _root_.MIPStarRE.QPBT.PauliTuple P → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) ιL)
    (QR RR : _root_.MIPStarRE.QPBT.PauliTuple P → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) ιR)
    (χ : EuclideanSpace ℂ (ιL × ιR)) (hχ : ‖χ‖ = 1) {c₁ c₂ c₃ : ℝ}
    (h1 : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.commTupleDist P)
      (fun ω a => _root_.MIPStarRE.QPBT.heteroKron ((MP ω).effect a) 1)
      (fun ω a => _root_.MIPStarRE.QPBT.heteroKron 1 ((QR ω).effect a)) χ ≤ c₁)
    (h2 : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.commTupleDist P)
      (fun ω a => _root_.MIPStarRE.QPBT.heteroKron ((QL ω).effect a) 1)
      (fun ω a => _root_.MIPStarRE.QPBT.heteroKron 1 ((QR ω).effect a)) χ ≤ c₂)
    (h3 : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.commTupleDist P)
      (fun ω a => _root_.MIPStarRE.QPBT.heteroKron ((QL ω).effect a) 1)
      (fun ω a => _root_.MIPStarRE.QPBT.heteroKron 1 ((RR ω).effect a)) χ ≤ c₃) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.commTupleDist P)
      (fun ω a => _root_.MIPStarRE.QPBT.heteroKron ((MP ω).effect a) 1)
      (fun ω a => _root_.MIPStarRE.QPBT.heteroKron 1 ((RR ω).effect a)) χ ≤
        2 * (c₁ + 2 * Real.sqrt (c₂ + c₃)) := by
  classical
  have hchain := _root_.MIPStarRE.QPBT.consistencyDefect_trans_le (_root_.MIPStarRE.QPBT.commTupleDist P)
    (fun ω => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ιR) (MP ω))
    (fun ω => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := ιL) (QR ω))
    (fun ω => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ιR) (QL ω))
    (fun ω => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := ιL) (RR ω))
    χ c₁ c₂ c₃ (_root_.MIPStarRE.QPBT.commTupleDist_isProbability P) hχ h1 h2 h3
  exact _root_.MIPStarRE.QPBT.WinImplications.opFamilyDistSq_placed_le_of_consistencyDefect_le (_root_.MIPStarRE.QPBT.commTupleDist P)
    MP RR χ hchain

/-! ## The commutation analysis on commuting tuples -/









/-! ## From projections to observables -/

/-- Applying a scaled operator scales the resulting state. Formalization-only
support for `eq:lc-12`, paper
`14_analysis_of_the_pauli_basis_test.tex:330-341`. -/
theorem applyOperatorToState_smul_op {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) (v : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (c • M) v = c • _root_.MIPStarRE.QPBT.applyOperatorToState M v := by
  unfold _root_.MIPStarRE.QPBT.applyOperatorToState
  rw [map_smul, LinearMap.smul_apply]

/-- Writing the two observables as the reflections `1 - 2P` makes their
commutator four times the commutator of the two projections, so the squared
state-dependent norm of the observable commutator is sixteen times that of the
projection commutator, on every state and both tensor factors. This is the
passage from Equation `eq:qld-obs-comm` to the observables in Equation
`eq:lc-12`, paper `14_analysis_of_the_pauli_basis_test.tex:330-341`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem norm_pointObs_commutator_sq {ιL ιR : Type*} [Fintype ιL]
    [DecidableEq ιL] [Fintype ιR] [DecidableEq ιR] (PX PZ OX OZ : _root_.LIDT.MIPStarRE.Quantum.Op ιL)
    (hX : OX = 1 - (2 : ℂ) • PX) (hZ : OZ = 1 - (2 : ℂ) • PZ)
    (χ : EuclideanSpace ℂ (ιL × ιR)) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (OX * OZ) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
          _root_.MIPStarRE.QPBT.heteroKron (OZ * OX) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ ^ 2 =
      16 * ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (PX * PZ - PZ * PX) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ ^ 2 := by
  rw [← _root_.MIPStarRE.QPBT.heteroKron_sub_left, hX, hZ, _root_.MIPStarRE.QPBT.WinImplications.reflection_commutator_eq,
    _root_.MIPStarRE.QPBT.WinImplications.heteroKron_smul_left, _root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_smul_op, norm_smul]
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [h4]
  ring





end WinImplications

end

end MIPStarRE.QPBT

/-!
# Approximate commutation of the point observables on commuting tuples

This module carries out the commuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`: the chain of
consistency relations `eq:lc-11`, the commutation analysis
`lem:commutation-analysis`, and the expansion `eq:lc-12` of the observables in
terms of the trace-coarse-grained point projections.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-341`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications



/-! ## Algebraic preliminaries -/







/-! ## Pair/W self-consistency on commuting tuples -/





/-! ## The chained relation of Equation `eq:lc-11` -/



/-! ## The commutation analysis on commuting tuples -/









/-! ## From projections to observables -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyCommObs

theorem solution :
    ∀ {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ιL ιR : Type} [Fintype ιL] [DecidableEq ιL]
        [Fintype ιR] [DecidableEq ιR]
        (MX MZ QX QZ : _root_.MIPStarRE.QPBT.PauliTuple P →
          _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) ιL)
        (VX VZ : _root_.MIPStarRE.QPBT.PauliTuple P → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) ιR)
        (N : _root_.MIPStarRE.QPBT.PauliTuple P →
          _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2 × ZMod 2) ιR)
        (OX OZ : _root_.MIPStarRE.QPBT.PauliTuple P → _root_.LIDT.MIPStarRE.Quantum.Op ιL)
        (χ : EuclideanSpace ℂ (ιL × ιR)) {c₁ c₂ c₃ : ℝ},
      ‖χ‖ = 1 → 0 ≤ c₁ →
      (∀ ω, _root_.MIPStarRE.QPBT.Measurement.IsProjective (N ω)) →
      (∀ ω, OX ω = 1 - (2 : ℂ) • (MX ω).effect 1) →
      (∀ ω, OZ ω = 1 - (2 : ℂ) • (MZ ω).effect 1) →
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.commTupleDist P)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron ((MX ω).effect a) 1)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron 1 ((VX ω).effect a)) χ ≤ c₁ →
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.commTupleDist P)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron ((MZ ω).effect a) 1)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron 1 ((VZ ω).effect a)) χ ≤ c₁ →
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.commTupleDist P)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron ((QX ω).effect a) 1)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron 1 ((VX ω).effect a)) χ ≤ c₂ →
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.commTupleDist P)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron ((QZ ω).effect a) 1)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron 1 ((VZ ω).effect a)) χ ≤ c₂ →
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.commTupleDist P)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron ((QX ω).effect a) 1)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron 1
          (((N ω).postprocess (fun bits => bits.1)).effect a)) χ ≤ c₃ →
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.commTupleDist P)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron ((QZ ω).effect a) 1)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron 1
          (((N ω).postprocess (fun bits => bits.2)).effect a)) χ ≤ c₃ →
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.commTupleDist P) (fun ω =>
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
            _root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ ^ 2) ≤
        1024 * (c₁ + Real.sqrt (c₂ + c₃)) := by
  classical
  intro P ιL ιR _ _ _ _ MX MZ QX QZ VX VZ N OX OZ χ c₁ c₂ c₃ hn hc hp hx hz a1 a2 b1 b2 d1 d2
  set δ : ℝ := 2 * (c₁ + 2 * Real.sqrt (c₂ + c₃)) with hδdef
  have hchainX := _root_.MIPStarRE.QPBT.WinImplications.pointTrace_pairComponent_dist_le MX QX VX
    (fun ω => (N ω).postprocess (fun bits => bits.1)) χ hn a1 b1 d1
  have hchainZ := _root_.MIPStarRE.QPBT.WinImplications.pointTrace_pairComponent_dist_le MZ QZ VZ
    (fun ω => (N ω).postprocess (fun bits => bits.2)) χ hn a2 b2 d2
  have hproj := _root_.MIPStarRE.QPBT.WinImplications.point_trace_commutator_comm_le_explicit MX MZ N χ hp hchainX hchainZ
  have hcongr : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.commTupleDist P) (fun ω =>
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (OX ω * OZ ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR) -
          _root_.MIPStarRE.QPBT.heteroKron (OZ ω * OX ω) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ ^ 2) =
    16 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.commTupleDist P) (fun ω =>
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron
        ((MX ω).effect 1 * (MZ ω).effect 1 -
          (MZ ω).effect 1 * (MX ω).effect 1) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιR)) χ‖ ^ 2) := by
    rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ (fun ω => ?_)
    exact _root_.MIPStarRE.QPBT.WinImplications.norm_pointObs_commutator_sq ((MX ω).effect 1) ((MZ ω).effect 1)
      (OX ω) (OZ ω) (hx ω) (hz ω) χ
  rw [hcongr]
  have hs : (0 : ℝ) ≤ Real.sqrt (c₂ + c₃) := Real.sqrt_nonneg _
  have hfinal : 16 * (16 * δ) ≤ 1024 * (c₁ + Real.sqrt (c₂ + c₃)) := by
    rw [hδdef]
    nlinarith
  exact le_trans (mul_le_mul_of_nonneg_left hproj (by norm_num)) hfinal
