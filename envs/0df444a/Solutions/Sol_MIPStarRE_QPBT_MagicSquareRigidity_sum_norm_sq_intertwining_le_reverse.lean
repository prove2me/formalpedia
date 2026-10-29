-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.sum_norm_sq_intertwining_le_reverse
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:37:43.681472+00:00
-- url     : https://prove2.me/submissions/c180e296-6a56-4fc8-82f2-78d3028002ad

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.sum_norm_sq_intertwining_le_reverse.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Relations
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Transfer
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_defect_eq
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_distance_le_two_defect
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_naimarkCompression_naimarkDilatedEffect
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_sum_stateQForm_reverse_eq

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Dilation.lean. -/
/-!
# A simultaneous projective dilation of a Magic Square strategy

The rigidity argument for the Magic Square game is stated for an arbitrary
tensor-product strategy, whose measurements are positive operator valued
measures.  The self-testing argument, however, manipulates projections.  This
file removes that discrepancy by dilating an arbitrary strategy to a projective
one without changing any observable quantity.

Each local Hilbert space `ℂ^ι` is enlarged by one auxiliary register whose
basis is indexed by `Option MsAnswer`, and the original space is identified with
the *ground slice* `ℂ^ι ⊗ |⊥⟩`.  The one-measurement Naimark lemma of the low
individual degree development supplies, for every question separately, a family
of projections on the enlarged space whose compression to the ground slice
returns the original effects; the ancilla is the same for all questions, so the
identification of `ℂ^ι` with the ground slice is a single isometry serving every
question at once.  Folding the deficiency `1 - ∑_a P_a` into one distinguished
answer turns the dilated family into a complete projective measurement without
disturbing the compression, because the original effects already sum to the
identity.

Since the dilated state is the image of the original state under the two ground
embeddings, every Born probability, and hence the game value and all the
rejection, malformed-answer, cell-consistency and parity masses of the
value-to-parity layer, is unchanged.  Conversely, the local isometries produced
by a rigidity argument applied to the dilated strategy compose with the ground
embeddings to give local isometries of the original strategy, and the
state-dependent norms occurring in the conclusion of `thm:ms-rigidity` transfer
along that composition.

## References

The rigidity statement supported here is blueprint
`thm:ms-rigidity`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, Theorem 6.9.  The dilation reuses the
one-measurement Naimark lemma of
`references/ldt-paper/orthonormalization.tex:121-159`, formalized as
`MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimark`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

noncomputable section

/-! ## Orthogonality inside a subnormalized family of projections -/







/-! ## The ground slice of an enlarged local space -/



























/-! ## The dilated projective measurement -/

























/-! ## The dilated state -/





/-- The quadratic form of an operator on a pure state, written out in the
computational basis.  Formalization-only support for the dilation of
blueprint `thm:ms-rigidity`. -/
theorem inner_applyOperatorToState {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : _root_.LIDT.MIPStarRE.Quantum.Op ι) (u : EuclideanSpace ℂ ι) :
    inner ℂ u (_root_.MIPStarRE.QPBT.applyOperatorToState K u) =
      ∑ p : ι, ∑ q : ι, (starRingEnd ℂ) (u p) * (K p q * u q) := by
  simp [PiLp.inner_apply, RCLike.inner_apply, _root_.MIPStarRE.QPBT.applyOperatorToState,
    Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm]



/-- The quadratic form of a product operator on the dilated state agrees with the
quadratic form of the two ground-slice compressions on the original state.  This
is the identity that makes the dilation invisible to every observable quantity of
the strategy. -/
theorem inner_heteroKron_naimarkDilatedState (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB))
    (M : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × Option α)) (N : _root_.LIDT.MIPStarRE.Quantum.Op (ιB × Option α)) :
    inner ℂ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)
        (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron M N) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)) =
      inner ℂ ψ (_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression M) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression N)) ψ) := by
  classical
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.inner_applyOperatorToState, _root_.MIPStarRE.QPBT.MagicSquareRigidity.inner_applyOperatorToState]
  simp [Fintype.sum_prod_type, Fintype.sum_option, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState_apply_mul,
    _root_.MIPStarRE.QPBT.heteroKron, Matrix.kroneckerMap_apply, mul_comm, mul_assoc]



/-! ## The dilated Magic Square strategy -/













/-! ## Preservation of the value-to-parity layer -/

/-- The dilation preserves every conditioned Born mass. -/
theorem ms_dilated_strategy_outcome_weight (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (x y : _root_.MIPStarRE.QPBT.MsType)
    (a b : _root_.MIPStarRE.QPBT.MsAnswer) :
    _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S) x y a b = _root_.MIPStarRE.QPBT.outcomeWeight S x y a b := by
  change (inner ℂ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ)
      (_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedEffect (α := _root_.MIPStarRE.QPBT.MsAnswer) (S.A x) (_root_.MIPStarRE.QPBT.MsAnswer.bit 0) a)
          (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedEffect (α := _root_.MIPStarRE.QPBT.MsAnswer) (S.B y) (_root_.MIPStarRE.QPBT.MsAnswer.bit 0) b))
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ))).re =
    (inner ℂ S.ψ (_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron ((S.A x).effect a) ((S.B y).effect b)) S.ψ)).re
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.inner_heteroKron_naimarkDilatedState, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression_naimarkDilatedEffect,
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression_naimarkDilatedEffect]





/-- The dilation preserves the mass of every answer event. -/
theorem ms_dilated_strategy_outcome_event_weight (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (x y : _root_.MIPStarRE.QPBT.MsType)
    (E : _root_.MIPStarRE.QPBT.MsAnswer → _root_.MIPStarRE.QPBT.MsAnswer → Prop) [DecidableRel E] :
    _root_.MIPStarRE.QPBT.outcomeEventWeight (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S) x y E = _root_.MIPStarRE.QPBT.outcomeEventWeight S x y E := by
  unfold _root_.MIPStarRE.QPBT.outcomeEventWeight
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
    by_cases h : E a b <;> simp [h, _root_.MIPStarRE.QPBT.MagicSquareRigidity.ms_dilated_strategy_outcome_weight]





















/-- The dilation preserves the reverse cell-consistency defect. -/
theorem ms_dilated_strategy_reverse_cell_mismatch_mass (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame)
    (i : Fin 6) (k : Fin 3) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.reverseCellMismatchMass (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S) i k = _root_.MIPStarRE.QPBT.MagicSquareRigidity.reverseCellMismatchMass S i k :=
  _root_.MIPStarRE.QPBT.MagicSquareRigidity.ms_dilated_strategy_outcome_event_weight S _ _ _





/-! ## Composition of the dilation with later local isometries -/



















/-! ## Transfer of state-dependent bounds -/

















end

end MIPStarRE.QPBT.MagicSquareRigidity

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



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Cell consistency of the postprocessed effects -/





/-! ## The dilated effects on the enlarged ground spaces -/

theorem solution (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (i : Fin 6) (k : Fin 3) :
    ∑ b : ZMod 2, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectA S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) _root_.MIPStarRE.QPBT.msBitOrZero b) 1 -
          _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectB S (.constraint i) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k) b))
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ)‖ ^ 2 ≤ 2 * _root_.MIPStarRE.QPBT.MagicSquareRigidity.reverseCellMismatchMass S i k := by
  set S' := _root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S
  set PA := (S'.A (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k))).postprocess _root_.MIPStarRE.QPBT.msBitOrZero
  set QB := (S'.B (.constraint i)).postprocess (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k)
  have h1 := _root_.MIPStarRE.QPBT.DistanceCalculus.point_distance_le_two_defect (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := S'.ιB) PA)
    (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := S'.ιA) QB) S'.ψ
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq] at h1
  have hnorm : ‖S'.ψ‖ = 1 := S'.ψ_norm
  have hover : ∑ a : ZMod 2, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S'.ψ
      ((_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := S'.ιB) PA).effect a *
        (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := S'.ιA) QB).effect a) =
      1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.reverseCellMismatchMass S i k := by
    rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.ms_dilated_strategy_reverse_cell_mismatch_mass S i k,
      ← _root_.MIPStarRE.QPBT.MagicSquareRigidity.sum_stateQForm_reverse_eq S' i k]
    refine Finset.sum_congr rfl fun a _ => ?_
    change _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S'.ψ (_root_.MIPStarRE.QPBT.heteroKron (PA.effect a) 1 * _root_.MIPStarRE.QPBT.heteroKron 1 (QB.effect a)) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S'.ψ (_root_.MIPStarRE.QPBT.heteroKron (PA.effect a) (QB.effect a))
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hnorm, hover] at h1
  have h2 : ∑ b : ZMod 2, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectA S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) _root_.MIPStarRE.QPBT.msBitOrZero b) 1 -
        _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectB S (.constraint i) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k) b))
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ)‖ ^ 2 ≤
      2 * (1 ^ 2 - (1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.reverseCellMismatchMass S i k)) := h1
  linarith
