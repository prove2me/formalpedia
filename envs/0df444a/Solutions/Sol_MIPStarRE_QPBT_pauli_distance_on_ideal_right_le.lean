-- Prove2me | solution 1 for MIPStarRE.QPBT.pauli_distance_on_ideal_right_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:20:47.997292+00:00
-- url     : https://prove2.me/submissions/71edf630-f610-45f4-b253-5cd187c1bc00

-- Generated proof for MIPStarRE.QPBT.pauli_distance_on_ideal_right_le.
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
import Definitions.Def_QPBT_QPBT_Algebra_Decoding
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Extraction_EncodingSupport
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_stateQForm_reindexState
import Theorems.Thm_MIPStarRE_QPBT_pauli_distance_on_ideal_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
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

/- Source helpers from QPBT/Extraction/ConcretePauliComparison.lean. -/
/-!
# Pauli comparison for the concrete extraction maps

The ideal-state distance estimate is transported back to the six-register
operators occurring in the extraction witness, for both players.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1827-1858`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement

noncomputable section

/-- Coordinate transport preserves the distance between two state vectors. -/
theorem norm_reindexState_sub_eq {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (psi phi : EuclideanSpace ℂ I) :
    ‖_root_.MIPStarRE.QPBT.reindexState e psi - _root_.MIPStarRE.QPBT.reindexState e phi‖ = ‖psi - phi‖ := by
  change ‖_root_.MIPStarRE.QPBT.reindexState e (psi - phi)‖ = _
  exact _root_.MIPStarRE.QPBT.reindexState_norm_eq e _





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





/-- Interchanging the two tensor factors turns a Kronecker product into the
product of the exchanged factors. Formalization-only support for the
interchanged conclusions of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_prodComm_heteroKron {ιA ιB : Type*}
    (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.reindexOp (Equiv.prodComm ιA ιB) (_root_.MIPStarRE.QPBT.heteroKron B A) = _root_.MIPStarRE.QPBT.heteroKron A B := by
  ext i j
  simp [_root_.MIPStarRE.QPBT.reindexOp, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.reindex_apply, mul_comm]

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

/-!
# Pauli comparison for the concrete extraction maps

The ideal-state distance estimate is transported back to the six-register
operators occurring in the extraction witness, for both players.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1827-1858`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliRegister P) (J × _root_.MIPStarRE.QPBT.PauliRegister P)) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (aux : EuclideanSpace ℂ (I × J)) (haux : ‖aux‖ = 1)
    (theta : EuclideanSpace ℂ ((I × _root_.MIPStarRE.QPBT.PauliRegister P) × (J × _root_.MIPStarRE.QPBT.PauliRegister P)))
    (htheta : ‖theta‖ = 1) :
    let ideal := _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor aux (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)))
    let B := _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := I) (_root_.MIPStarRE.QPBT.pauliRegisterMeas (params := P) W)
    (∑ h : _root_.MIPStarRE.QPBT.PauliRegister P, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (I × _root_.MIPStarRE.QPBT.PauliRegister P))
        (A.effect h - _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op J) (_root_.MIPStarRE.QPBT.pauliProj W h))) ideal‖ ^ 2) ≤
      2 * (1 - _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun u =>
        ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm theta
          (_root_.MIPStarRE.QPBT.heteroKron ((B.postprocess (fun h => _root_.MIPStarRE.QPBT.evalPoly (_root_.MIPStarRE.QPBT.encodingPoly h) u)).effect a)
            ((A.postprocess (fun h => _root_.MIPStarRE.QPBT.evalPoly (_root_.MIPStarRE.QPBT.encodingPoly h) u)).effect a)))) +
        2 * ((P.m * P.d : ℝ) / P.q) + 4 * ‖theta - ideal‖ := by
  let e := Equiv.prodComm (I × _root_.MIPStarRE.QPBT.PauliRegister P) (J × _root_.MIPStarRE.QPBT.PauliRegister P)
  let ideal := _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor aux (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)))
  have hideal : _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle
      (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.reindexState (Equiv.prodComm I J) aux) (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))) =
      _root_.MIPStarRE.QPBT.reindexState e ideal := by
    ext p
    simp [_root_.MIPStarRE.QPBT.reindexState, _root_.MIPStarRE.QPBT.vecTensor, _root_.MIPStarRE.QPBT.prodShuffle, _root_.MIPStarRE.QPBT.eprState, e, ideal, eq_comm]
  have h := _root_.MIPStarRE.QPBT.pauli_distance_on_ideal_le A W (_root_.MIPStarRE.QPBT.reindexState (Equiv.prodComm I J) aux)
    (by rw [_root_.MIPStarRE.QPBT.reindexState_norm_eq, haux]) (_root_.MIPStarRE.QPBT.reindexState e theta)
    (by rw [_root_.MIPStarRE.QPBT.reindexState_norm_eq, htheta])
  dsimp only at h ⊢
  rw [hideal, _root_.MIPStarRE.QPBT.norm_reindexState_sub_eq] at h
  dsimp only [e] at h
  simp_rw [_root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState,
    _root_.MIPStarRE.QPBT.WinImplications.stateQForm_reindexState, _root_.MIPStarRE.QPBT.WinImplications.reindexOp_prodComm_heteroKron] at h
  exact h
