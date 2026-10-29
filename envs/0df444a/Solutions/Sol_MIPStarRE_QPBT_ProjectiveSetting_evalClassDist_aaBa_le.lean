-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.evalClassDist_aaBa_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:37:05.992654+00:00
-- url     : https://prove2.me/submissions/34e99eef-0f0f-4e66-be63-e6470966d5e1

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.evalClassDist_aaBa_le.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedPlacement
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_consistencyDefect_eq_one_sub_overlap
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_sum_stateQForm_evalClass_AA_prime_BA_prime_prime_eq
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_stateQForm_reindexState
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_two_mul_consistencyDefect

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Games/DistanceTheorems/TensorSupport.lean. -/
/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective





/-- Formalization-only auxiliary lemma for Fact 4.26: products of left and right
placements evaluate as a Kronecker product. -/
theorem placed_product_stateQForm_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A 1 * _root_.MIPStarRE.QPBT.heteroKron 1 B) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A B) := by
  congr 1
  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor A B































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Observables/ExpandedPlacement.lean. -/
/-!
# Placing operators on the expanded state

The four register placements of `def:symmetric-equivalents` put an operator of
one player's expanded local space on one of the register pairs `AA'`, `BA''`,
`BB'` and `AB''` of the expanded state `psiHat`.  This module records how such
a placement acts on `psiHat`: after the shuffle of `eq:def-psihat` the placed
operator is a threefold tensor product, so a factorized operator whose Pauli
factor is an isometry has the same state-dependent norm as its strategy factor
placed on the original state.  No symmetry between the two players is used;
each of the four placements is treated explicitly.

## References

The declarations support `def:symmetric-equivalents` and `lem:qld-comm-cons`
in `blueprint/src/chapter/ch14_qpbt_observables.tex:1002-1031` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1178`.  Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-505`.
-/

@[expose] public section

-- The unshuffled six-register index type of `eq:def-psihat` is a fourfold
-- iterated product; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default.
set_option synthInstance.maxSize 400

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Coordinate tensors -/











namespace ProjectiveSetting





variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The strategy factor of a placement -/





/-! ## The action of a placement on the expanded state -/

/-- The expanded state is the shuffle of the coordinate tensor of the strategy
state with the two EPR ancillas. This is `eq:def-psihat`, paper
`14_analysis_of_the_pauli_basis_test.tex:367-372`, blueprint
`ch14_qpbt_observables.tex:895-918`. -/
theorem psiHat_eq_reindexState (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) :
    S.psiHat = _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.vecTensor S.toStrategy.ψ (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)))
        (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))) := rfl

/-- The expanded strategy state is normalized. -/
theorem psiHat_norm (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) : ‖S.psiHat‖ = 1 := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.psiHat_eq_reindexState, _root_.MIPStarRE.QPBT.reindexState_norm_eq, _root_.MIPStarRE.QPBT.vecTensor_norm_eq,
    _root_.MIPStarRE.QPBT.vecTensor_norm_eq, S.toStrategy.ψ_norm, _root_.MIPStarRE.QPBT.eprState_norm]
  norm_num

/-! ## Opposite-placement bipartitions -/













/-! ## The four placements -/



























end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/FactorTransport.lean. -/
/-!
# Transport of the winning implications to the interchanged tensor factor

This module carries the state-dependent functionals of the winning
implications across the interchange of the two tensor factors.  The
factor-interchanged conclusions of `lem:qld-win-implications` are stated with
the second player on the left factor and the reindexed state
`ProjectiveSetting.swappedState`; the lemmas here identify those quantities
with the ones proved on `S.toStrategy.psi`, so that the second pass of
`lem:qld-win-implications-obs` can reuse the first pass verbatim on the
interchanged side.

## References

The declarations support the trailing clause of `lem:qld-win-implications` and
the second assertion of `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:701-703`.  Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:227,309-362`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reindexing the identity and the strategy state -/





/-! ## Transport of the consistency defect -/



/-- Reindexing an operator along an equivalence is multiplicative.
Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M N : _root_.LIDT.MIPStarRE.Quantum.Op κ) :
    _root_.MIPStarRE.QPBT.reindexOp e (M * N) = _root_.MIPStarRE.QPBT.reindexOp e M * _root_.MIPStarRE.QPBT.reindexOp e N := by
  ext i j
  change (M * N) (e i) (e j) = ∑ k : ι, M (e i) (e k) * N (e k) (e j)
  rw [Matrix.mul_apply, ← e.sum_comp (fun l : κ => M (e i) l * N l (e j))]





/-! ## Transport of the phase-signed operator distance -/





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



/-- Reindexing an operator is computed entrywise, hence commutes with
subtraction. Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_sub {ι ι' : Type*} (e : ι ≃ ι') (M N : _root_.LIDT.MIPStarRE.Quantum.Op ι') :
    _root_.MIPStarRE.QPBT.reindexOp e (M - N) = _root_.MIPStarRE.QPBT.reindexOp e M - _root_.MIPStarRE.QPBT.reindexOp e N := rfl



/-- Coordinates of an operator applied to a reindexed state. Formalization-only
support for the interchanged conclusions of `lem:qld-win-implications`,
blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem applyOperatorToState_reindexState_ofLp {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (T : _root_.LIDT.MIPStarRE.Quantum.Op κ) (ψ : EuclideanSpace ℂ ι) (k : κ) :
    (_root_.MIPStarRE.QPBT.applyOperatorToState T (_root_.MIPStarRE.QPBT.reindexState e ψ)).ofLp k =
      (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.reindexOp e T) ψ).ofLp (e.symm k) := by
  change (T *ᵥ (_root_.MIPStarRE.QPBT.reindexState e ψ).ofLp) k = (_root_.MIPStarRE.QPBT.reindexOp e T *ᵥ ψ.ofLp) (e.symm k)
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
    ← e.sum_comp (fun l : κ => T k l * (_root_.MIPStarRE.QPBT.reindexState e ψ).ofLp l)]
  apply Finset.sum_congr rfl
  intro j _
  simp [_root_.MIPStarRE.QPBT.reindexState, _root_.MIPStarRE.QPBT.reindexOp]

/-- Reindexing a state and its operator preserves the length of the image.
Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem norm_applyOperatorToState_reindexState {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (T : _root_.LIDT.MIPStarRE.Quantum.Op κ) (ψ : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState T (_root_.MIPStarRE.QPBT.reindexState e ψ)‖ =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.reindexOp e T) ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← e.symm.sum_comp (fun i : ι =>
      ‖(_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.reindexOp e T) ψ).ofLp i‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro k _
  rw [_root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_reindexState_ofLp]



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

/- Source helpers from QPBT/Observables/LineMeasurement/BipartiteTransport.lean. -/
/-!
# Bipartite estimates and transport for the expanded line measurements

This module collects the generic distance estimates used by items 2 and 3 of
the expanded-line consistency lemma, and the identities that transport the
placed families of the six-register expanded state to the two opposite-
placement bipartitions. The generic estimates are: the distance between two
oppositely placed complete measurements is at most twice the complement of
their diagonal overlap (`fact:agreement`), and a projective family compared
with itself followed by an effect selected through a coarse-graining is at
most as far as the coarse-grained families are from each other
(`fact:add-a-proj2` for a projective refinement). The transport identities
are formalization-only auxiliaries: they carry a relation between placed
operators on the six-register expanded state to the product shape in which the
generic estimates are stated, a step the source leaves implicit.

## References

Items 2 and 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`,
blueprint `eq:qld-comm-line-pt-cons` and `eq:qld-comm-line-pt-cons2`, and
the generic estimates `fact:agreement` and `fact:add-a-proj2` of
`blueprint/src/chapter/ch12_qpbt_games.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Generic bipartite estimates -/

namespace DistanceCalculus



/-- The distance between two oppositely placed complete measurements is at
most twice their inconsistency, expressed through the diagonal overlap. This
is `fact:agreement` combined with the overlap form of the consistency defect. -/
theorem opFamilyDistSq_placed_le_two_mul_one_sub_overlap {X α ιA ιB : Type*}
    [Finite X] [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (hμ : μ.IsProbability)
    (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA)
    (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ ≤
      2 * (1 - _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1 *
          _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)))) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  refine (_root_.MIPStarRE.QPBT.WinImplications.opFamilyDistSq_placed_le_two_mul_consistencyDefect
    μ A B ψ).trans (le_of_eq ?_)
  congr 1
  exact _root_.MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ
    (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (A x))
    (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (B x)) ψ hμ hψ





end DistanceCalculus

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## Transport between the six registers and the bipartitions -/





set_option synthInstance.maxSize 400 in
/-- On the `AA' | BA''(B'B'')` bipartition, the overlap of left and right
tensor placements is the overlap of the `AA'` and `BA''` placements. -/
theorem stateQForm_aaBa_mul_eq (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (X : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P))
    (Y : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P)) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
        (_root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.ProjectiveSetting.aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat)
        (_root_.MIPStarRE.QPBT.heteroKron X (1 : _root_.LIDT.MIPStarRE.Quantum.Op ((S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P) ×
            (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P))) *
          _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P))
            (_root_.MIPStarRE.QPBT.heteroKron Y (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P)))) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat (S.place .AA' X * S.place .BA'' Y) := by
  rw [_root_.MIPStarRE.QPBT.WinImplications.stateQForm_reindexState, _root_.MIPStarRE.QPBT.WinImplications.reindexOp_mul,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_aaBaBipartition_left, _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_aaBaBipartition_right]







end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/LineMeasurement/SelfConsistency.lean. -/
/-!
# Self-consistency of the expanded line measurements

This module proves item 1 of the expanded-line consistency lemma on the two
opposite-placement bipartitions. The strategy line measurements are
self-consistent between the two players on average over the line-point
distribution, because a disagreement on a sampled line is rejected by the
corresponding self-loop of the Pauli basis test; the Pauli line projectors are
perfectly consistent on an EPR pair; and the data-processing inequality
transfers the product estimate to the addition postprocessing that defines the
expanded line measurement.

The module also records that the error parameter of a projective setting is
nonnegative, which is not assumed by the structure and is needed by the other
two items as well.

## References

The declarations formalize `enu:qld-comm-line-self-cons`, item 1 of
`lem:qld-comm-line-cons`, whose paper source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-532`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Self-consistency of the unexpanded line measurements -/











namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The error parameter -/



/-! ## Placement of differences on the two bipartitions -/

-- The four-level product indices below exceed the default instance-search
-- size.

set_option synthInstance.maxSize 400 in
/-- On the `AA' | BA''(B'B'')` bipartition, the difference of an `AA'` and a
`BA''` placement acts on the expanded state as the corresponding difference
of left and right tensor placements. Formalization-only transport for the
placement pairs of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-545`. -/
theorem norm_place_AA'_sub_place_BA'' (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (O₁ : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P))
    (O₂ : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P)) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place .AA' O₁ - S.place .BA'' O₂) S.psiHat‖ =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron O₁ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ((S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P) ×
            (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P))) -
          _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P))
            (_root_.MIPStarRE.QPBT.heteroKron O₂ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P))))
        (_root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.ProjectiveSetting.aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat)‖ := by
  rw [_root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState,
    _root_.MIPStarRE.QPBT.WinImplications.reindexOp_sub, _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_aaBaBipartition_left,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_aaBaBipartition_right]



set_option synthInstance.maxSize 400 in
/-- Reindexing the expanded state along any equivalence onto a product of
the six registers leaves it a unit vector. Formalization-only auxiliary
carrying the normalization of `def:expanded-state` to the two bipartitions
used by the consistency estimates. -/
theorem norm_reindexState_psiHat (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (e : _root_.MIPStarRE.QPBT.SixReg P S.toStrategy.ιA S.toStrategy.ιB ≃
      (S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P) ×
        ((S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P) ×
          (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P))) :
    ‖_root_.MIPStarRE.QPBT.reindexState e S.psiHat‖ = 1 := by
  rw [_root_.MIPStarRE.QPBT.reindexState_norm_eq, _root_.MIPStarRE.QPBT.ProjectiveSetting.psiHat_norm]

/-! ## Fine-product consistency on the two bipartitions -/





/-! ## Data processing and transport back to the six registers -/













end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/LineMeasurement/EvalClassConsistency.lean. -/
/-!
# Consistency of expanded evaluation classes with expanded points

This module proves item 3 of the expanded-line consistency lemma on the four
directed opposite-placement pairs. On each bipartition the distance between
the evaluation classes of the expanded line measurement and the completed
expanded point measurement is at most twice their inconsistency, which by the
overlap identity equals the inconsistency of the strategy's evaluation classes
with its completed point measurement. The trivial bound `4` on the same
distance supplies the large-`ε` case of the common square-root error.

## References

Item 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:540-545`,
blueprint `eq:qld-comm-line-pt-cons2`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## Overlaps of the evaluation classes -/









/-! ## Item 3: evaluation classes versus completed expanded points -/

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `AA'`--`BA''`
pair equals the distance of the left- and right-placed families on the
corresponding bipartition. Formalization-only transport for item 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_aaBa_eq (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => S.place .AA'
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BA''
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat =
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => _root_.MIPStarRE.QPBT.heteroKron ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op ((S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P) × (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P))))
        (fun sample a => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P))
          ((_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement
            (ιB := _root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P)
            (S.pointMeasExpOption .bob W sample.2)).effect a))
        (_root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.ProjectiveSetting.aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro sample
  apply Finset.sum_congr rfl
  intro a _
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.norm_place_AA'_sub_place_BA'']
  rfl























end ProjectiveSetting

end

end MIPStarRE.QPBT

/-!
# Consistency of expanded evaluation classes with expanded points

This module proves item 3 of the expanded-line consistency lemma on the four
directed opposite-placement pairs. On each bipartition the distance between
the evaluation classes of the expanded line measurement and the completed
expanded point measurement is at most twice their inconsistency, which by the
overlap identity equals the inconsistency of the strategy's evaluation classes
with its completed point measurement. The trivial bound `4` on the same
distance supplies the large-`ε` case of the common square-root error.

## References

Item 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:540-545`,
blueprint `eq:qld-comm-line-pt-cons2`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## Overlaps of the evaluation classes -/









/-! ## Item 3: evaluation classes versus completed expanded points -/

set_option synthInstance.maxSize 400 in

theorem solution (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => S.place .AA'
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BA''
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat ≤
      2 * _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => _root_.MIPStarRE.QPBT.heteroKron
          ((S.lineEvalMeas .alice W sample.1 sample.2).effect a) 1)
        (fun sample a => _root_.MIPStarRE.QPBT.heteroKron 1
          ((S.pointMeasOption .bob W sample.2).effect a))
        S.toStrategy.ψ := by
  let X := _root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
  let R := _root_.MIPStarRE.QPBT.PauliRegister P
  let μ := _root_.MIPStarRE.QPBT.linePointDist P.toLdParams
  let e := _root_.MIPStarRE.QPBT.ProjectiveSetting.aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (Option (_root_.MIPStarRE.QPBT.PauliScalar P)) (S.toStrategy.ιA × R) :=
    fun sample => S.lineEvalMeasExp .alice W sample.1 sample.2
  let B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (Option (_root_.MIPStarRE.QPBT.PauliScalar P))
      ((S.toStrategy.ιB × R) × (R × R)) := fun sample =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := R × R)
      (S.pointMeasExpOption .bob W sample.2)
  have hμ : μ.IsProbability := _root_.MIPStarRE.QPBT.linePointDist_isProbability P.toLdParams
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.evalClassDist_aaBa_eq]
  refine (_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_placed_le_two_mul_one_sub_overlap μ hμ
    A B _ (_root_.MIPStarRE.QPBT.ProjectiveSetting.norm_reindexState_psiHat S e)).trans (le_of_eq ?_)
  have hstrat := _root_.MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ
    (fun sample => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement
      (S.lineEvalMeas .alice W sample.1 sample.2))
    (fun sample => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement
      (S.pointMeasOption .bob W sample.2)) S.toStrategy.ψ hμ S.toStrategy.ψ_norm
  change _ = 2 * _root_.MIPStarRE.QPBT.consistencyDefect μ
    (fun sample a => (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement
      (S.lineEvalMeas .alice W sample.1 sample.2)).effect a)
    (fun sample a => (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement
      (S.pointMeasOption .bob W sample.2)).effect a) S.toStrategy.ψ
  rw [hstrat]
  congr 2
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro sample
  calc
    _ = ∑ a : Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
          (S.place .AA' ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a) *
            S.place .BA'' ((S.pointMeasExpOption .bob W sample.2).effect a)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      exact _root_.MIPStarRE.QPBT.ProjectiveSetting.stateQForm_aaBa_mul_eq S _ _
    _ = ∑ a : Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.toStrategy.ψ
          (_root_.MIPStarRE.QPBT.heteroKron ((S.lineEvalMeas .alice W sample.1 sample.2).effect a)
            ((S.pointMeasOption .bob W sample.2).effect a)) :=
      _root_.MIPStarRE.QPBT.ProjectiveSetting.sum_stateQForm_evalClass_AA_prime_BA_prime_prime_eq S W sample.1 sample.2
    _ = _ := by
      refine Finset.sum_congr rfl fun a _ => ?_
      exact (_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq _ _ _).symm
