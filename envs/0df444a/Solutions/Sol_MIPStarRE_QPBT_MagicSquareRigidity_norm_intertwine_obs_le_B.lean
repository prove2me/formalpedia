-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.norm_intertwine_obs_le_B
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:04:46.162301+00:00
-- url     : https://prove2.me/submissions/f8972009-49f7-4531-aec5-7323fe75b2c5

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.norm_intertwine_obs_le_B.
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
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_AnticommutatorB
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Relations
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Transfer

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

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

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`: the
tensor placement of possibly rectangular matrices respects differences in the
right factor.  This is the general form of `heteroKron_sub_right` below. -/
theorem kroneckerMap_sub_right {m n p q : Type*} (A : Matrix m n ℂ) (B C : Matrix p q ℂ) :
    Matrix.kroneckerMap (· * ·) A (B - C) =
      Matrix.kroneckerMap (· * ·) A B - Matrix.kroneckerMap (· * ·) A C := by
  ext p' q'
  simp [Matrix.kroneckerMap, mul_sub]

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
respects differences in the left factor. -/
theorem heteroKron_sub_left {ιA ιB : Type*} (A B : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (C : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron (A - B) C = _root_.MIPStarRE.QPBT.heteroKron A C - _root_.MIPStarRE.QPBT.heteroKron B C :=
  _root_.MIPStarRE.QPBT.kroneckerMap_sub_left A B C

/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
respects differences in the right factor. -/
theorem heteroKron_sub_right {ιA ιB : Type*} (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B C : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron A (B - C) = _root_.MIPStarRE.QPBT.heteroKron A B - _root_.MIPStarRE.QPBT.heteroKron A C :=
  _root_.MIPStarRE.QPBT.kroneckerMap_sub_right A B C

/- The Euclidean linear map is the shared action used by the value and distance
functionals.  Keeping it at the Euclidean-space level avoids accidentally
using the function-space supremum norm of `Matrix.mulVec`. -/








































end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Transfer.lean. -/
/-!
# Transfer of rigidity bounds along the projective dilation

The self-testing argument behind `thm:ms-rigidity` is carried out for the
projective dilation `msDilatedStrategy S` of an arbitrary Magic Square strategy
`S`.  Its conclusions are state-dependent bounds for the *dilated* projectors,
conjugated by local isometries `φ_A`, `φ_B` out of the enlarged local spaces.
The witness for the original strategy is obtained by composing these isometries
with the ground embeddings, and the operators appearing in its bounds are the
conjugates of the *original* effects, that is, of the compressions `Π P Π` of
the dilated projectors `P` to the ground slice (`Π` the ground projection).

Naimark dilation preserves Born probabilities but not state-dependent `≈_δ`
estimates in general (`references/ldt-paper/orthonormalization.tex:82-101`,
blueprint `ex:easy-but-long`), so `Π P Π` and `P` need not act
alike on the dilated state.  Their difference on the dilated state `ψ'` is the
*leakage* `(1 - Π) P ψ'` of `P` out of the ground slice, and the point of this
file is that in the Magic Square game this leakage is controlled by the
cell-consistency defect of the value-to-parity layer: the dilated effect
`P ⊗ 1` almost agrees with the partner effect `1 ⊗ Q` on the other side, and
`(1 - Π) ⊗ 1` annihilates `1 ⊗ Q ψ'`.  Combined with the closeness of
`(φ_A ⊗ φ_B) ψ'` to the ideal state and the fact that all operators involved
are contractions, this pulls every bound of `thm:ms-rigidity` back from the
dilated strategy to the original one with explicit constants.

## Main statements

* `ms_effect_transfer_A`, `ms_effect_transfer_B`: the bit-measurement distances
  of the original strategy are bounded by three times those of the dilated
  strategy plus `216 ε + 24 η²`, where `η` bounds the state closeness.
* `ms_anticommutator_transfer_A`, `ms_anticommutator_transfer_B`: the
  anticommutator defects transfer with the bound `3 · (dilated) + 15552 ε +
  48 η²`.
* `ms_state_transfer`: the state closeness is unchanged.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Cell consistency of the postprocessed effects -/





/-! ## The dilated effects on the enlarged ground spaces -/









/-! ## Compressions of the dilated postprocessed effects -/

















/-! ## Transfer of the effect estimates -/















/-! ## Transfer of the anticommutator estimates -/



/-- The action on states respects differences of operators. -/
theorem applyOperatorToState_sub_op {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : _root_.LIDT.MIPStarRE.Quantum.Op ι) (v : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (M - N) v =
      _root_.MIPStarRE.QPBT.applyOperatorToState M v - _root_.MIPStarRE.QPBT.applyOperatorToState N v := by
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState]





























end

end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# Transfer of Bob's anticommutator estimate along the projective dilation

The right-placed counterpart of the Alice-side anticommutator transfer in
`Rigidity/Transfer.lean`: Bob's dilated observables leak out of the ground
slice by at most the forward cell-consistency defects, and the product of the
compressed observables is compared with the product of the dilated ones on the
dilated state through Alice's partner observable.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (i : Fin 6) (k : Fin 3) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsAf S (.constraint i) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k)) 1 -
        _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsB S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) _root_.MIPStarRE.QPBT.msBitOrZero))
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ)‖ ≤
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectA S (.constraint i) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k) 0) 1 -
          _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectB S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) _root_.MIPStarRE.QPBT.msBitOrZero 0))
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ)‖ +
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectA S (.constraint i) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k) 1) 1 -
          _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectB S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) _root_.MIPStarRE.QPBT.msBitOrZero 1))
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ)‖ := by
  have hsplit : _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsAf S (.constraint i) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k)) (1 : _root_.LIDT.MIPStarRE.Quantum.Op _) -
      _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsB S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) _root_.MIPStarRE.QPBT.msBitOrZero) =
      (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectA S (.constraint i) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k) 0) 1 -
        _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectB S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) _root_.MIPStarRE.QPBT.msBitOrZero 0)) -
      (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectA S (.constraint i) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k) 1) 1 -
        _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectB S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) _root_.MIPStarRE.QPBT.msBitOrZero 1)) := by
    change _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectA S (.constraint i) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k) 0 -
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectA S (.constraint i) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k) 1) (1 : _root_.LIDT.MIPStarRE.Quantum.Op _) -
      _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectB S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) _root_.MIPStarRE.QPBT.msBitOrZero 0 -
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectB S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) _root_.MIPStarRE.QPBT.msBitOrZero 1) = _
    rw [_root_.MIPStarRE.QPBT.heteroKron_sub_left, _root_.MIPStarRE.QPBT.heteroKron_sub_right]
    abel
  rw [hsplit, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_sub_op]
  exact norm_sub_le _ _
