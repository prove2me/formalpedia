-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_bob_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:49:36.034075+00:00
-- url     : https://prove2.me/submissions/e355635d-cb04-4d7e-9608-f87f4f41b6bc

-- Generated proof for MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_bob_explicit.
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
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Commuting
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_InterchangedCommutation
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_consistencyDefect_swappedState
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_pairW_self_consistency_comm_le
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_pointObs_eq_one_sub_two_smul
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_point_obs_commutator_comm_le_explicit
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_win_comm_cons_interchanged_explicit
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_win_comm_interchanged_explicit

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

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

/-- The identity operator acts trivially on a state. Formalization-only support
for blueprint `def:strategy-observables`. -/
theorem applyOperatorToState_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) : _root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ψ = ψ := by
  ext i
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState]





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

/- Source helpers from QPBT/Observables/WinImplications/InterchangedCommutation.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyInterchanged
/-!
# The factor-interchanged phase-signed commutation relation

Interchanging the tensor factors places Bob's point observables on the left.
The reversed consistency estimates of `lem:qld-win-implications` and Alice's
Magic Square anticommutation give the bound, which is then transported to the
original state. This proves the factor-interchanged relation in
`lem:qld-win-implications-obs`.

## References

The declarations formalize the trailing clause of
`lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-362`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications



/-! ## The interchanged consistency inputs on the interchanged state -/



/-- The fixed coefficient in `win_comm_cons_swapped_proof`. -/
theorem win_comm_cons_swapped_explicit {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (hε : 0 ≤ ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.commTupleDist P)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron
          ((S.pointTraceMeas .bob W (_root_.MIPStarRE.QPBT.WinImplications.selectedTuplePoint W ω)
            (_root_.MIPStarRE.QPBT.WinImplications.selectedTupleScalar W ω)).effect a) 1)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron 1
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.swappedState ≤ 2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
  refine le_trans (le_of_eq ?_)
    (_root_.MIPStarRE.QPBT.WinImplications.win_comm_cons_interchanged_explicit P ε S hε W)
  exact _root_.MIPStarRE.QPBT.WinImplications.consistencyDefect_swappedState (_root_.MIPStarRE.QPBT.commTupleDist P)
    (fun ω a => (S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a)
    (fun ω a => (S.pointTraceMeas .bob W (_root_.MIPStarRE.QPBT.WinImplications.selectedTuplePoint W ω)
      (_root_.MIPStarRE.QPBT.WinImplications.selectedTupleScalar W ω)).effect a) S.toStrategy.ψ

/-- Pair-W self-consistency with Bob on the left factor, transported to the
interchanged state. Paper
`14_analysis_of_the_pauli_basis_test.tex:315-320`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem pairW_self_consistency_comm_swapped {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.commTupleDist P)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron 1
          ((S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a))
        S.swappedState ≤ 2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
  refine le_trans (le_of_eq ?_) (_root_.MIPStarRE.QPBT.WinImplications.pairW_self_consistency_comm_le S W)
  exact _root_.MIPStarRE.QPBT.WinImplications.consistencyDefect_swappedState (_root_.MIPStarRE.QPBT.commTupleDist P)
    (fun ω a => (S.pairWMeas .alice W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a)
    (fun ω a => (S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a)
    S.toStrategy.ψ



/-- The fixed coefficient in `win_comm_swapped_proof`. -/
theorem win_comm_swapped_explicit {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (hε : 0 ≤ ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.MIPStarRE.QPBT.commTupleDist P)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron
          ((S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a) 1)
        (fun ω a => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.pairComponentMeas .alice W ω).effect a))
        S.swappedState ≤ 2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
  refine le_trans (le_of_eq ?_) (_root_.MIPStarRE.QPBT.WinImplications.win_comm_interchanged_explicit P ε S hε W)
  exact _root_.MIPStarRE.QPBT.WinImplications.consistencyDefect_swappedState (_root_.MIPStarRE.QPBT.commTupleDist P)
    (fun ω a => (S.pairComponentMeas .alice W ω).effect a)
    (fun ω a => (S.pairWMeas .bob W ω.1 ω.2.1 ω.2.2.1 ω.2.2.2).effect a)
    S.toStrategy.ψ





/-! ## The two halves on Bob's factor -/











/-! ## The interchanged twisted commutation relation -/





end WinImplications

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

/-- Reindexing the identity operator gives the identity operator.
Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_one {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) : _root_.MIPStarRE.QPBT.reindexOp e (1 : _root_.LIDT.MIPStarRE.Quantum.Op κ) = (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
  ext i j
  simp [_root_.MIPStarRE.QPBT.reindexOp, Matrix.one_apply, e.injective.eq_iff]

/-- The interchanged strategy state is again a unit vector.  This is needed to
chain consistency relations on the interchanged side of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`,
paper `14_analysis_of_the_pauli_basis_test.tex:227`. -/
theorem norm_swappedState {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) : ‖S.swappedState‖ = 1 := by
  have h := _root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState
    (Equiv.prodComm S.toStrategy.ιA S.toStrategy.ιB)
    (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιB × S.toStrategy.ιA)) S.toStrategy.ψ
  rw [_root_.MIPStarRE.QPBT.WinImplications.reindexOp_one, _root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_one, _root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_one] at h
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.swappedState, h]
  exact S.toStrategy.ψ_norm

/-! ## Transport of the consistency defect -/









/-! ## Transport of the phase-signed operator distance -/





end WinImplications

end

end MIPStarRE.QPBT

/-!
# The factor-interchanged phase-signed commutation relation

Interchanging the tensor factors places Bob's point observables on the left.
The reversed consistency estimates of `lem:qld-win-implications` and Alice's
Magic Square anticommutation give the bound, which is then transported to the
original state. This proves the factor-interchanged relation in
`lem:qld-win-implications-obs`.

## References

The declarations formalize the trailing clause of
`lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-362`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications



/-! ## The interchanged consistency inputs on the interchanged state -/















/-! ## The two halves on Bob's factor -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyInterchanged

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε), 0 ≤ ε →
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.commTupleDist P) (fun ω =>
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.heteroKron (S.pointObs .bob .X ω.2.2.1 ω.1 *
              S.pointObs .bob .Z ω.2.2.2 ω.2.1) (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA) -
            _root_.MIPStarRE.QPBT.heteroKron (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
              S.pointObs .bob .X ω.2.2.1 ω.1) (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA))
          S.swappedState‖ ^ 2) ≤
        (1024 * (2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) +
          1024 * Real.sqrt (4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ))) *
            (ε + Real.sqrt ε) := by
  classical
  have hcard : (1 : ℝ) ≤ (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card _root_.MIPStarRE.QPBT.PauliEdge)
  set K : ℝ := 4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) with hKdef
  have hK : (0 : ℝ) ≤ K := by rw [hKdef]; linarith
  intro P ε S hε
  have hsq : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hmain := _root_.MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_explicit
    (ιL := S.toStrategy.ιB) (ιR := S.toStrategy.ιA)
    (fun ω => S.pointTraceMeas .bob .X ω.1 ω.2.2.1)
    (fun ω => S.pointTraceMeas .bob .Z ω.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .bob .X ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .bob .Z ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .alice .X ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .alice .Z ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairMeas .alice ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pointObs .bob .X ω.2.2.1 ω.1)
    (fun ω => S.pointObs .bob .Z ω.2.2.2 ω.2.1)
    S.swappedState (_root_.MIPStarRE.QPBT.WinImplications.norm_swappedState S) (by positivity)
    (fun ω => _root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective _ (S.isProjective.1 _) _)
    (fun ω => _root_.MIPStarRE.QPBT.WinImplications.pointObs_eq_one_sub_two_smul S .bob .X ω.2.2.1 ω.1)
    (fun ω => _root_.MIPStarRE.QPBT.WinImplications.pointObs_eq_one_sub_two_smul S .bob .Z ω.2.2.2 ω.2.1)
    (_root_.MIPStarRE.QPBT.WinImplications.win_comm_cons_swapped_explicit S hε .X)
    (_root_.MIPStarRE.QPBT.WinImplications.win_comm_cons_swapped_explicit S hε .Z)
    (_root_.MIPStarRE.QPBT.WinImplications.pairW_self_consistency_comm_swapped S .X)
    (_root_.MIPStarRE.QPBT.WinImplications.pairW_self_consistency_comm_swapped S .Z)
    (_root_.MIPStarRE.QPBT.WinImplications.win_comm_swapped_explicit S hε .X) (_root_.MIPStarRE.QPBT.WinImplications.win_comm_swapped_explicit S hε .Z)
  refine le_trans hmain ?_
  have hKsplit : Real.sqrt (2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε +
      2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε) =
      Real.sqrt K * Real.sqrt ε := by
    rw [show 2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε +
        2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε = K * ε by
      rw [hKdef]; ring]
    exact Real.sqrt_mul hK ε
  rw [hKsplit]
  nlinarith [Real.sqrt_nonneg K, hε, hsq]
