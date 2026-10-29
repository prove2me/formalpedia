-- Prove2me | solution 1 for MIPStarRE.QPBT.exp_line_point_cons_explicit_prime
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:57:54.227104+00:00
-- url     : https://prove2.me/submissions/43725a20-dc24-4911-84f8-968b5dcd2719

-- Generated proof for MIPStarRE.QPBT.exp_line_point_cons_explicit'.
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
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedPlacement
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_opFamilyDistSq_placed_le_four
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_evalClassDist_aaBa_le
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_evalClassDist_abBb_le
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_evalClassDist_baAa_le
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_evalClassDist_bbAb_le
import Theorems.Thm_MIPStarRE_QPBT_Strategy_value_le_one
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_win_low_degree_explicit
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_win_low_degree_interchanged_explicit
import Theorems.Thm_MIPStarRE_QPBT_le_mul_sqrt_of_le_mul_of_le_four

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

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective





























































/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14), item 2: state-dependent squared distance between operator families is
nonnegative. -/
theorem opFamilyDistSq_nonneg {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (M N : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    0 ≤ _root_.MIPStarRE.QPBT.opFamilyDistSq μ M N ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq _root_.LIDT.MIPStarRE.LDT.avgOver
  exact Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonnegative x)
    (Finset.sum_nonneg fun a _ => sq_nonneg _)



























/-- Formalization-only auxiliary lemma for Proposition 4.29: state-dependent
operator-family distance is symmetric. -/
theorem opFamilyDistSq_symm {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ B A ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, map_sub, LinearMap.sub_apply]
  rw [norm_sub_rev]

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

/-- The error parameter of a projective setting is nonnegative. Nothing in the
structure assumes this: it follows from the winning premise `1 - ε ≤ value`
together with the bound `value ≤ 1` satisfied by the value of every strategy.
Formalization-only auxiliary supplying the sign condition of the winning
implications used in items 2 and 3 of `lem:qld-comm-line-cons`. -/
theorem eps_nonneg (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) : 0 ≤ ε := by
  have hv := _root_.MIPStarRE.QPBT.WinImplications.strategy_value_le_one S.toStrategy
  have hw := S.win
  linarith

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
/-- On the `AB'' | BB'(A'A'')` bipartition, the difference of an `AB''` and a
`BB'` placement acts on the expanded state as the corresponding difference of
left and right tensor placements. Formalization-only transport for the
placement pairs of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-545`. -/
theorem norm_place_AB''_sub_place_BB' (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (O₁ : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P))
    (O₂ : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P)) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place .AB'' O₁ - S.place .BB' O₂) S.psiHat‖ =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron O₁ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ((S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P) ×
            (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P))) -
          _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P))
            (_root_.MIPStarRE.QPBT.heteroKron O₂ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P))))
        (_root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.ProjectiveSetting.abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat)‖ := by
  rw [_root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState,
    _root_.MIPStarRE.QPBT.WinImplications.reindexOp_sub, _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_abBbBipartition_left,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_abBbBipartition_right]

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



set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `AA'`--`BA''`
pair is at most four. This trivial bound supplies the large-`ε` case of the
common square-root error in item 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_aaBa_le_four (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => S.place .AA'
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BA''
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat ≤ 4 := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.evalClassDist_aaBa_eq]
  exact _root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_placed_le_four _
    (_root_.MIPStarRE.QPBT.linePointDist_isProbability P.toLdParams) _ _ _
    (_root_.MIPStarRE.QPBT.ProjectiveSetting.norm_reindexState_psiHat S _)

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `BA''`--`AA'`
pair equals the distance of the left- and right-placed families on the
corresponding bipartition. Formalization-only transport for item 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_baAa_eq (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => S.place .BA''
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AA'
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat =
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeasExpOption .alice W sample.2).effect a)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op ((S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P) × (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P))))
        (fun sample a => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P))
          ((_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement
            (ιB := _root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P)
            (S.lineEvalMeasExp .bob W sample.1 sample.2)).effect a))
        (_root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.ProjectiveSetting.aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) := by
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_symm]
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro sample
  apply Finset.sum_congr rfl
  intro a _
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.norm_place_AA'_sub_place_BA'']
  rfl



set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `BA''`--`AA'`
pair is at most four. This trivial bound supplies the large-`ε` case of the
common square-root error in item 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_baAa_le_four (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => S.place .BA''
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AA'
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat ≤ 4 := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.evalClassDist_baAa_eq]
  exact _root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_placed_le_four _
    (_root_.MIPStarRE.QPBT.linePointDist_isProbability P.toLdParams) _ _ _
    (_root_.MIPStarRE.QPBT.ProjectiveSetting.norm_reindexState_psiHat S _)

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `AB''`--`BB'`
pair equals the distance of the left- and right-placed families on the
corresponding bipartition. Formalization-only transport for item 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_abBb_eq (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => S.place .AB''
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BB'
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat =
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => _root_.MIPStarRE.QPBT.heteroKron ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op ((S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P) × (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P))))
        (fun sample a => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P))
          ((_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement
            (ιB := _root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P)
            (S.pointMeasExpOption .bob W sample.2)).effect a))
        (_root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.ProjectiveSetting.abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro sample
  apply Finset.sum_congr rfl
  intro a _
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.norm_place_AB''_sub_place_BB']
  rfl



set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `AB''`--`BB'`
pair is at most four. This trivial bound supplies the large-`ε` case of the
common square-root error in item 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_abBb_le_four (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => S.place .AB''
          ((S.lineEvalMeasExp .alice W sample.1 sample.2).effect a))
        (fun sample a => S.place .BB'
          ((S.pointMeasExpOption .bob W sample.2).effect a))
        S.psiHat ≤ 4 := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.evalClassDist_abBb_eq]
  exact _root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_placed_le_four _
    (_root_.MIPStarRE.QPBT.linePointDist_isProbability P.toLdParams) _ _ _
    (_root_.MIPStarRE.QPBT.ProjectiveSetting.norm_reindexState_psiHat S _)

set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `BB'`--`AB''`
pair equals the distance of the left- and right-placed families on the
corresponding bipartition. Formalization-only transport for item 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_bbAb_eq (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => S.place .BB'
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AB''
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat =
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeasExpOption .alice W sample.2).effect a)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op ((S.toStrategy.ιB × _root_.MIPStarRE.QPBT.PauliRegister P) × (_root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P))))
        (fun sample a => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.toStrategy.ιA × _root_.MIPStarRE.QPBT.PauliRegister P))
          ((_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement
            (ιB := _root_.MIPStarRE.QPBT.PauliRegister P × _root_.MIPStarRE.QPBT.PauliRegister P)
            (S.lineEvalMeasExp .bob W sample.1 sample.2)).effect a))
        (_root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.ProjectiveSetting.abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) := by
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_symm]
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro sample
  apply Finset.sum_congr rfl
  intro a _
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.norm_place_AB''_sub_place_BB']
  rfl



set_option synthInstance.maxSize 400 in
/-- The expanded evaluation-class distance on the directed `BB'`--`AB''`
pair is at most four. This trivial bound supplies the large-`ε` case of the
common square-root error in item 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:540-545`. -/
theorem evalClassDist_bbAb_le_four (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => S.place .BB'
          ((S.lineEvalMeasExp .bob W sample.1 sample.2).effect a))
        (fun sample a => S.place .AB''
          ((S.pointMeasExpOption .alice W sample.2).effect a))
        S.psiHat ≤ 4 := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.evalClassDist_bbAb_eq]
  exact _root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_placed_le_four _
    (_root_.MIPStarRE.QPBT.linePointDist_isProbability P.toLdParams) _ _ _
    (_root_.MIPStarRE.QPBT.ProjectiveSetting.norm_reindexState_psiHat S _)

end ProjectiveSetting

end

end MIPStarRE.QPBT

/-!
# Expanded line measurements

For a generalized-Pauli basis `W` and a canonical line, the expanded line
measurement is the convolution of the strategy line measurement with the
projective measurement of one Pauli register whose outcome is the restriction
to that line of the low-degree encoding of the measured basis label. This file
states the three consistency conclusions the source draws for that family,
together with the existential form in which the source states them.

The argument runs as follows. Restricting a multilinear low-degree encoding to
a line gives a polynomial of degree at most `m*d` in the line parameter, and at
most `d` on an axis-parallel line (`LineMeasurement.Restriction`), whose
partial evaluation at a sampled point obeys the elementary calculus of
`LineMeasurement.Evaluation`.
Coarse-graining the generalized Pauli basis measurement along that restriction
gives the ancillary projectors `tau^{W,line}`, which are symmetric and hence
perfectly self-consistent on an EPR pair (`LineMeasurement.Projector`). Their
convolution with the strategy line measurement is again projective and vanishes
outside the degree-`d` outcomes on an axis line (`LineMeasurement.Expanded`).
Self-consistency of the convolution follows from self-consistency of the
strategy line measurements and the data-processing inequality
(`LineMeasurement.SelfConsistency`). The overlap of an expanded line
measurement with the expanded point effects selected by evaluation at the
sampled point factorizes exactly through the ancillary consistency of
`tau^{W,line}` with `tau^{W,u}` (`LineMeasurement.LinePointOverlap`); the
generic bipartite estimates of `LineMeasurement.BipartiteTransport` carry that
overlap to the two bipartitions of the six registers, giving the
evaluation-class conclusion (`LineMeasurement.EvalClassConsistency`) and, by
projective refinement, the line-versus-point conclusion
(`LineMeasurement.LinePointConsistency`).

Two features of this route differ from the source. The source derives its third
item from its second; here the evaluation-class estimate comes first, from the
exact overlap identity, and the second item follows from it by projective
refinement, so that the source's elementary sub-measurement inequality is not
needed. The source also transports a relation proved for one pair of register
placements to the remaining three by the symmetry of the test
(`lem:symmetric-equivalents-transfer`, which is not formalized); here each of
the four directed opposite-placement pairs is proved directly. The estimates
established are linear in `ε` for all three items, hence stronger than the
square-root error whenever `ε ≤ 1`; they are weakened to the common error
`deltaLine ε = √ε` only because the source states the three items with a single
error function (`LineMeasurement.SquareRootError`).

## References

The declarations formalize `def:expanded-line-measurement` and
`lem:qld-comm-line-cons` of `blueprint/src/chapter/ch14_qpbt_observables.tex`.
Their paper source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:523-678`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
attribute [local instance] _root_.MIPStarRE.QPBT.pauliEdgeNonemptyLineMeasurement

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
      (p₁ p₂ : _root_.MIPStarRE.QPBT.Placement), p₁.IsOpposite p₂ → ∀ W : _root_.MIPStarRE.QPBT.PauliKind,
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
        (fun sample a => S.place p₁
          ((S.lineEvalMeasExp p₁.side W sample.1 sample.2).effect a))
        (fun sample a => S.place p₂
          ((S.pointMeasExpOption p₂.side W sample.2).effect a))
        S.psiHat ≤ 348 * _root_.MIPStarRE.QPBT.deltaLine ε := by
  intro P ε S p₁ p₂ hopp W
  have hε : 0 ≤ ε := S.eps_nonneg
  have key : ∀ (x a : ℝ), 1 ≤ a → a ≤ 86 + 86 → 0 ≤ x → x ≤ 2 * (a * ε) →
      x ≤ 4 → x ≤ 348 * _root_.MIPStarRE.QPBT.deltaLine ε := by
    intro x a ha haC hx0 hxa hx4
    calc
      x ≤ (2 * a + 4) * Real.sqrt ε :=
        _root_.MIPStarRE.QPBT.le_mul_sqrt_of_le_mul_of_le_four (by linarith) hx0
          (by rw [mul_assoc]; exact hxa) hx4
      _ ≤ 348 * Real.sqrt ε := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg ε)
        linarith
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  cases p₁ <;> cases p₂ <;> simp only [_root_.MIPStarRE.QPBT.Placement.IsOpposite] at hopp
  · have hb := (_root_.MIPStarRE.QPBT.ProjectiveSetting.evalClassDist_aaBa_le S W).trans
      (mul_le_mul_of_nonneg_left
        (_root_.MIPStarRE.QPBT.WinImplications.win_low_degree_explicit P ε S hε W) htwo)
    simpa only [_root_.MIPStarRE.QPBT.Placement.side] using key _ 86 (by norm_num) (by norm_num)
      (_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) hb
      (_root_.MIPStarRE.QPBT.ProjectiveSetting.evalClassDist_aaBa_le_four S W)
  · have hb := (_root_.MIPStarRE.QPBT.ProjectiveSetting.evalClassDist_baAa_le S W).trans
      (mul_le_mul_of_nonneg_left
        (_root_.MIPStarRE.QPBT.WinImplications.win_low_degree_interchanged_explicit P ε S hε W) htwo)
    simpa only [_root_.MIPStarRE.QPBT.Placement.side] using key _ 86 (by norm_num) (by norm_num)
      (_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) hb
      (_root_.MIPStarRE.QPBT.ProjectiveSetting.evalClassDist_baAa_le_four S W)
  · have hb := (_root_.MIPStarRE.QPBT.ProjectiveSetting.evalClassDist_bbAb_le S W).trans
      (mul_le_mul_of_nonneg_left
        (_root_.MIPStarRE.QPBT.WinImplications.win_low_degree_interchanged_explicit P ε S hε W) htwo)
    simpa only [_root_.MIPStarRE.QPBT.Placement.side] using key _ 86 (by norm_num) (by norm_num)
      (_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) hb
      (_root_.MIPStarRE.QPBT.ProjectiveSetting.evalClassDist_bbAb_le_four S W)
  · have hb := (_root_.MIPStarRE.QPBT.ProjectiveSetting.evalClassDist_abBb_le S W).trans
      (mul_le_mul_of_nonneg_left
        (_root_.MIPStarRE.QPBT.WinImplications.win_low_degree_explicit P ε S hε W) htwo)
    simpa only [_root_.MIPStarRE.QPBT.Placement.side] using key _ 86 (by norm_num) (by norm_num)
      (_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _) hb
      (_root_.MIPStarRE.QPBT.ProjectiveSetting.evalClassDist_abBb_le_four S W)
