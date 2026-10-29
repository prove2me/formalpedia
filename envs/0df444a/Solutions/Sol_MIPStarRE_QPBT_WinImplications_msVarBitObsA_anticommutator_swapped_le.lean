-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.msVarBitObsA_anticommutator_swapped_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:03:32.162312+00:00
-- url     : https://prove2.me/submissions/88aba2ce-2590-4499-ab03-5c62932fe053

-- Generated proof for MIPStarRE.QPBT.WinImplications.msVarBitObsA_anticommutator_swapped_le.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_InterchangedCommutation
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Basic
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_Strategy_value_le_one
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_msVarObsA_anticommutator_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

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









/-! ## The anticommuting half of the twisted commutation -/



/-- Every strategy value is at most one. This is an alias of the Games-layer
`MIPStarRE.QPBT.Strategy.value_le_one`, which carries the single proof; the name
is kept here so the existing callers of this layer resolve unchanged.
Formalization-only support for `def:tensor-product-value`, blueprint
`ch12_qpbt_games.tex:71-82`. -/
theorem strategy_value_le_one {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) : S.value ≤ 1 :=
  _root_.MIPStarRE.QPBT.Strategy.value_le_one S

/-- The Magic Square value defect of a tuple is nonnegative and admissible as
an error parameter for the rigidity input. Formalization-only support for
`eq:qld-implication-ms-anticomm`, paper
`14_analysis_of_the_pauli_basis_test.tex:349-356`. -/
theorem msValueAt_defect_nonneg {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (ω : _root_.MIPStarRE.QPBT.PauliTuple P) :
    0 ≤ 1 - S.msValueAt ω ∧
      1 - (1 - S.msValueAt ω) ≤ (S.msStrategyAt ω).value := by
  have hle := _root_.MIPStarRE.QPBT.WinImplications.strategy_value_le_one (S.msStrategyAt ω)
  have heq : S.msValueAt ω = (S.msStrategyAt ω).value := rfl
  constructor
  · rw [heq]; linarith
  · rw [heq]; linarith



/-- The first-factor companion of the previous estimate: the Magic Square
variable observables of Alice approximately anticommute at one tuple. Paper
`14_analysis_of_the_pauli_basis_test.tex:349-356`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem msVarBitObsA_anticommutator_le {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (ω : _root_.MIPStarRE.QPBT.PauliTuple P) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron
          (_root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 0 ω) *
              _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 4 ω) +
            _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 4 ω) *
              _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 0 ω))
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB))
        S.toStrategy.ψ‖ ^ 2 ≤ 1183680 * (1 - S.msValueAt ω) := by
  obtain ⟨hnn, hwin⟩ := _root_.MIPStarRE.QPBT.WinImplications.msValueAt_defect_nonneg S ω
  exact _root_.MIPStarRE.QPBT.WinImplications.msVarObsA_anticommutator_le (S.msStrategyAt ω) (1 - S.msValueAt ω) hnn
    hwin











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

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (ω : _root_.MIPStarRE.QPBT.PauliTuple P) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (ιA := S.toStrategy.ιB) (ιB := S.toStrategy.ιA) 1
          (_root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 0 ω) *
              _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 4 ω) +
            _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 4 ω) *
              _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 0 ω)))
        S.swappedState‖ ^ 2 ≤ 1183680 * (1 - S.msValueAt ω) := by
  have htrans := _root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState
    (Equiv.prodComm S.toStrategy.ιA S.toStrategy.ιB)
    (_root_.MIPStarRE.QPBT.heteroKron (ιA := S.toStrategy.ιB) (ιB := S.toStrategy.ιA) 1
      (_root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 0 ω) *
          _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 4 ω) +
        _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 4 ω) *
          _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 0 ω)))
    S.toStrategy.ψ
  have hswap : _root_.MIPStarRE.QPBT.reindexOp (Equiv.prodComm S.toStrategy.ιA S.toStrategy.ιB)
      (_root_.MIPStarRE.QPBT.heteroKron (ιA := S.toStrategy.ιB) (ιB := S.toStrategy.ιA) 1
        (_root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 0 ω) * _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 4 ω) +
          _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 4 ω) * _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 0 ω))) =
    _root_.MIPStarRE.QPBT.heteroKron
      (_root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 0 ω) * _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 4 ω) +
        _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 4 ω) * _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .alice 0 ω))
      (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) := by
    exact _root_.MIPStarRE.QPBT.WinImplications.reindexOp_prodComm_heteroKron _ _
  rw [hswap] at htrans
  exact le_of_eq_of_le (congrArg (fun t : ℝ => t ^ 2) htrans)
    (_root_.MIPStarRE.QPBT.WinImplications.msVarBitObsA_anticommutator_le S ω)
