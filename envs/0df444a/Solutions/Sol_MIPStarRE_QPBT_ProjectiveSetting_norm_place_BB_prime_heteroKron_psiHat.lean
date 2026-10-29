-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.norm_place_BB_prime_heteroKron_psiHat
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:56:26.17764+00:00
-- url     : https://prove2.me/submissions/d8dd8d17-85ae-4c77-82bc-6698acae1377

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.norm_place_BB'_heteroKron_psiHat.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Reflections
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_applyOperatorToState_heteroKron_vecTensor

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

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



/-! ## Opposite-placement bipartitions -/













/-! ## The four placements -/





/-- The `BB'` placement in the unshuffled tensor order of `psiHat`. -/
theorem reindexOp_sixRegShuffle_place_BB'_heteroKron
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (T : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB)
    (V : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) :
    _root_.MIPStarRE.QPBT.reindexOp (_root_.MIPStarRE.QPBT.sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
        (S.place .BB' (_root_.MIPStarRE.QPBT.heteroKron T V)) =
      _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA) T)
          (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))
            (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))))
        (_root_.MIPStarRE.QPBT.heteroKron V (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))) := by
  ext i j
  obtain ⟨⟨⟨iA, iB⟩, iA', iA''⟩, iB', iB''⟩ := i
  obtain ⟨⟨⟨jA, jB⟩, jA', jA''⟩, jB', jB''⟩ := j
  simp only [_root_.MIPStarRE.QPBT.reindexOp, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, _root_.MIPStarRE.QPBT.ProjectiveSetting.place, _root_.MIPStarRE.QPBT.sixRegShuffle, Equiv.coe_fn_mk, _root_.MIPStarRE.QPBT.heteroKron,
    Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, Matrix.one_apply]
  ring





















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

/-- The tensor placement respects the adjoint. Formalization-only support for
`fact:add-a-proj`, blueprint `ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_conjTranspose {ιA ιB : Type*} (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    (_root_.MIPStarRE.QPBT.heteroKron A B)ᴴ = _root_.MIPStarRE.QPBT.heteroKron Aᴴ Bᴴ := by
  ext i j
  simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.conjTranspose_apply]

/-- Placing an isometry on the first factor gives an isometry.
Formalization-only support for `fact:add-a-proj`, blueprint
`ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_left_isometry {ιA ιB : Type*} [DecidableEq ιA]
    [DecidableEq ιB] [Fintype ιA] [Fintype ιB] (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA)
    (hA : Aᴴ * A = 1) :
    (_root_.MIPStarRE.QPBT.heteroKron A (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB))ᴴ * _root_.MIPStarRE.QPBT.heteroKron A 1 = 1 := by
  rw [_root_.MIPStarRE.QPBT.WinImplications.heteroKron_conjTranspose, _root_.MIPStarRE.QPBT.heteroKron_mul, hA, Matrix.conjTranspose_one,
    one_mul, _root_.MIPStarRE.QPBT.heteroKron_one_one]







/-! ## From the Magic Square variables to the point observables -/









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



-- The unshuffled six-register index type of `eq:def-psihat` is a fourfold
-- iterated product; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default.
set_option synthInstance.maxSize 400

open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



/-! ## Coordinate tensors -/











open MIPStarRE.QPBT.ProjectiveSetting





variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The strategy factor of a placement -/





/-! ## The action of a placement on the expanded state -/





/-! ## Opposite-placement bipartitions -/













/-! ## The four placements -/

theorem solution (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (T : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) (V : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) (hV : Vᴴ * V = 1) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place .BB' (_root_.MIPStarRE.QPBT.heteroKron T V)) S.psiHat‖ =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA) T) S.toStrategy.ψ‖ := by
  classical
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.psiHat_eq_reindexState,
    _root_.MIPStarRE.QPBT.WinImplications.norm_applyOperatorToState_reindexState,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.reindexOp_sixRegShuffle_place_BB'_heteroKron,
    _root_.MIPStarRE.QPBT.applyOperatorToState_heteroKron_vecTensor,
    _root_.MIPStarRE.QPBT.applyOperatorToState_heteroKron_vecTensor, _root_.MIPStarRE.QPBT.vecTensor_norm_eq, _root_.MIPStarRE.QPBT.vecTensor_norm_eq,
    _root_.MIPStarRE.QPBT.heteroKron_one_one, _root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_one,
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_of_isometry
      (_root_.MIPStarRE.QPBT.WinImplications.heteroKron_left_isometry (ιB := _root_.MIPStarRE.QPBT.PauliRegister P) V hV),
    _root_.MIPStarRE.QPBT.eprState_norm]
  ring
