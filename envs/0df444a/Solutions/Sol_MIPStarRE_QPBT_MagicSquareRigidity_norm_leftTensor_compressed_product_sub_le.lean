-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.norm_leftTensor_compressed_product_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:37:43.492243+00:00
-- url     : https://prove2.me/submissions/35e0ccd9-eebb-412a-83be-cd5757d21e38

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.norm_leftTensor_compressed_product_sub_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono

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













/-! ## The dilated Magic Square strategy -/













/-! ## Preservation of the value-to-parity layer -/



































/-! ## Composition of the dilation with later local isometries -/



















/-! ## Transfer of state-dependent bounds -/









/-- The action of an operator on the dilated state only sees its ground-slice
columns. -/
theorem applyOperatorToState_naimarkDilatedState (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (K : _root_.LIDT.MIPStarRE.Quantum.Op ((ιA × Option α) × (ιB × Option α)))
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (p : (ιA × Option α) × (ιB × Option α)) :
    _root_.MIPStarRE.QPBT.applyOperatorToState K (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ) p =
      ∑ k : ιA, ∑ l : ιB, K p ((k, none), (l, none)) * ψ (k, l) := by
  classical
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_option, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState_apply_mul]

/-- Inflated operators act on the dilated state exactly as the original
operators act on the original state.  This is the identity that transfers
state-dependent effect bounds back to the undilated strategy. -/
theorem applyOperatorToState_heteroKron_naimarkInflation
    (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (N : _root_.LIDT.MIPStarRE.Quantum.Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) M) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) N))
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ) =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron M N) ψ) := by
  classical
  ext p
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_naimarkDilatedState, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState_apply]
  obtain ⟨⟨i, oa⟩, ⟨j, ob⟩⟩ := p
  by_cases hoa : oa = none
  · by_cases hob : ob = none
    · simp [hoa, hob, _root_.MIPStarRE.QPBT.heteroKron, _root_.MIPStarRE.QPBT.applyOperatorToState, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, mul_assoc]
    · simp [hob, _root_.MIPStarRE.QPBT.heteroKron]
  · simp [hoa, _root_.MIPStarRE.QPBT.heteroKron]





end

end MIPStarRE.QPBT.MagicSquareRigidity

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

/-- The action on states respects negation of operators. -/
theorem applyOperatorToState_neg_op {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) (v : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (-M) v = -_root_.MIPStarRE.QPBT.applyOperatorToState M v := by
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState]



























end

end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean. -/
/-!
# Contractions, isometries and the ground slice of the dilation

Support for the transfer step of `thm:ms-rigidity` (blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`):
the calculus needed to compare the dilated projective strategy of
`Rigidity/Dilation.lean` with the original strategy on states.

* Contractions: operators `K` with `Kᴴ K ≤ 1` do not increase norms; effects,
  observables of binary measurements, orthogonal projections, tensor placements,
  products and isometry conjugates are contractions.
* Matrices of isometries: `Vᴴ V = 1`, the two-sided isometry image of a state
  preserves norms, and a conjugated local operator acts on the transported state
  as the original operator acts on the original state.
* The ground projection `Π` of an enlarged local space: an orthogonal projection
  fixing the dilated state, with `Π P Π` the inflation of the compression of `P`.
* Leakage: the part `(1 - Π) P ψ'` of a dilated operator that leaves the ground
  slice is bounded by the intertwining defect of `P ⊗ 1` against any `1 ⊗ Q`,
  because `(1 - Π) ⊗ 1` annihilates `(1 ⊗ Q) ψ'`.  This is the estimate that
  replaces the `≈_δ`-preservation which Naimark dilation lacks in general
  (`references/ldt-paper/orthonormalization.tex:82-101`, blueprint
  `ex:easy-but-long`).

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

/-! ## Contractions and their action on states -/



/-- Operators act additively on states. -/
theorem applyOperatorToState_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) (u v : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState M (u + v) =
      _root_.MIPStarRE.QPBT.applyOperatorToState M u + _root_.MIPStarRE.QPBT.applyOperatorToState M v := by
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState]















/-- An operator `K` with `Kᴴ K ≤ 1` does not increase norms. -/
theorem norm_applyOperatorToState_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hK : Kᴴ * K ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState K v‖ ≤ ‖v‖ := by
  have h := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hK v
  have hv : (inner ℂ v v).re = ‖v‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_sq, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_one, hv] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h



/-- Orthogonal projections are contractions. -/
theorem conjTranspose_mul_le_one_of_isProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hP : _root_.LIDT.MIPStarRE.Quantum.IsProj P) : Pᴴ * P ≤ 1 := by
  have hstar : Pᴴ = P := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hP.isSelfAdjoint.star_eq
  rw [hstar, hP.isIdempotentElem.eq]
  exact sub_nonneg.mp hP.one_sub.nonneg

/-- Products of contractions are contractions. -/
theorem conjTranspose_mul_le_one_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hA : Aᴴ * A ≤ 1) (hB : Bᴴ * B ≤ 1) :
    (A * B)ᴴ * (A * B) ≤ 1 := by
  have h1 : (1 - Aᴴ * A).PosSemidef := Matrix.le_iff.mp hA
  have h2 := h1.conjTranspose_mul_mul_same B
  have h3 : Bᴴ * (1 - Aᴴ * A) * B = Bᴴ * B - (A * B)ᴴ * (A * B) := by
    rw [Matrix.conjTranspose_mul]
    noncomm_ring
  refine le_trans ?_ hB
  rw [Matrix.le_iff, ← h3]
  exact h2





/-- Left placement preserves contractions. -/
theorem conjTranspose_mul_le_one_leftTensor {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] {A : _root_.LIDT.MIPStarRE.Quantum.Op ιA} (hA : Aᴴ * A ≤ 1) :
    (_root_.MIPStarRE.QPBT.heteroKron A (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB))ᴴ * _root_.MIPStarRE.QPBT.heteroKron A (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB) ≤ 1 := by
  change (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) A)ᴴ * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) A ≤ 1
  rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_conjTranspose, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_le_one hA

/-- Right placement preserves contractions. -/
theorem conjTranspose_mul_le_one_rightTensor {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] {B : _root_.LIDT.MIPStarRE.Quantum.Op ιB} (hB : Bᴴ * B ≤ 1) :
    (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) B)ᴴ * _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) B ≤ 1 := by
  change (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) B)ᴴ * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) B ≤ 1
  rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_conjTranspose, _root_.LIDT.MIPStarRE.LDT.rightTensor_mul_rightTensor]
  exact _root_.LIDT.MIPStarRE.LDT.rightTensor_le_one hB

/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/









/-! ## Matrices of isometries -/





















/-! ## The ground projection -/



/-- Inflation is multiplicative. -/
theorem naimarkInflation_mul {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) M * _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) N =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) (M * N) := by
  ext p q
  simp only [Matrix.mul_apply, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_apply, Fintype.sum_prod_type,
    Fintype.sum_option]
  by_cases hp : p.2 = none <;> by_cases hq : q.2 = none <;> simp [hp, hq]

/-- Inflation commutes with the conjugate transpose. -/
theorem naimarkInflation_conjTranspose {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) M)ᴴ = _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) Mᴴ := by
  ext p q
  simp only [Matrix.conjTranspose_apply, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_apply]
  by_cases hp : p.2 = none <;> by_cases hq : q.2 = none <;> simp [hp, hq]

/-- The ground projection is an orthogonal projection. -/
theorem isProj_groundProjection (ι α : Type) [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] : _root_.LIDT.MIPStarRE.Quantum.IsProj (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ι α) := by
  constructor
  · change _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ι α * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ι α = _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ι α
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_mul, Matrix.mul_one]
  · change star (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ι α) = _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ι α
    rw [Matrix.star_eq_conjTranspose, _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_conjTranspose,
      Matrix.conjTranspose_one]





/-- The dilated state lies in the ground slice on Alice's side. -/
theorem applyOperatorToState_leftTensor_groundProjection (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) 1) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ) =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ := by
  have hfull : _root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιB α))
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ) = _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ := by
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection, _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_heteroKron_naimarkInflation,
      _root_.MIPStarRE.QPBT.heteroKron_one_one, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_one]
  conv_lhs => rw [← hfull]
  rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, _root_.MIPStarRE.QPBT.heteroKron_mul,
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isProj_groundProjection ιA α).isIdempotentElem.eq, Matrix.one_mul]
  exact hfull







/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





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









/-! ## Compressions of the dilated postprocessed effects -/

















/-! ## Transfer of the effect estimates -/















/-! ## Transfer of the anticommutator estimates -/

theorem solution (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB))
    (A B : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × Option α)) (Y : _root_.LIDT.MIPStarRE.Quantum.Op (ιB × Option α))
    (hA : Aᴴ * A ≤ 1) (hY : Yᴴ * Y ≤ 1) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * A * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α *
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * B * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) - A * B) 1)
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ ≤
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * B) 1)
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ +
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * A) 1)
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ +
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron B 1 - _root_.MIPStarRE.QPBT.heteroKron 1 Y) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ := by
  have hGG : _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α = _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α :=
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isProj_groundProjection ιA α).isIdempotentElem.eq
  have hGc : (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α)ᴴ * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α ≤ 1 :=
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_of_isProj (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isProj_groundProjection ιA α)
  have h1Gc : (1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α)ᴴ * (1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) ≤ 1 :=
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_of_isProj (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isProj_groundProjection ιA α).one_sub
  have hstep1 : _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * A *
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * B * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α)) 1)
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ) =
      _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * A * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * B) 1)
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ) := by
    have hassoc : _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * A * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α *
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * B * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) =
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * A * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * B * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) (B * _), hGG]
    rw [hassoc, show _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * A * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * B *
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιB × Option α)) =
        _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * A * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * B) 1 *
          _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) 1 by rw [_root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.mul_one],
      _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_leftTensor_groundProjection]
  have hdec : _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * A * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * B - A * B =
      -(_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * A * ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * B)) -
        ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * A) * B := by
    noncomm_ring
  have hfirst : ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * A *
      ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * B)) 1) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ ≤
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * B) 1)
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ := by
    rw [show _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * A * ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * B))
        (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιB × Option α)) =
        _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * A) 1 * _root_.MIPStarRE.QPBT.heteroKron ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * B) 1
        by rw [_root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.mul_one], _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
    exact _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_le
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_leftTensor (_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_mul hGc hA)) _
  have hsecond : ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * A) * B) 1)
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ ≤
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron B 1 - _root_.MIPStarRE.QPBT.heteroKron 1 Y) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ +
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * A) 1)
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ := by
    have hL : (_root_.MIPStarRE.QPBT.heteroKron ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * A) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιB × Option α)))ᴴ *
        _root_.MIPStarRE.QPBT.heteroKron ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * A) 1 ≤ 1 :=
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_leftTensor (_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_mul h1Gc hA)
    have hYc : (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × Option α)) Y)ᴴ * _root_.MIPStarRE.QPBT.heteroKron 1 Y ≤ 1 :=
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_rightTensor hY
    have hcomm : _root_.MIPStarRE.QPBT.heteroKron ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * A) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιB × Option α)) *
        _root_.MIPStarRE.QPBT.heteroKron 1 Y = _root_.MIPStarRE.QPBT.heteroKron 1 Y * _root_.MIPStarRE.QPBT.heteroKron ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * A) 1 := by
      rw [_root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_one]
    rw [show _root_.MIPStarRE.QPBT.heteroKron (((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * A) * B) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιB × Option α)) =
        _root_.MIPStarRE.QPBT.heteroKron ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * A) 1 * _root_.MIPStarRE.QPBT.heteroKron B 1
        by rw [_root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.mul_one], _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
    have hdecB : _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron B 1) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ) =
        _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron B 1 - _root_.MIPStarRE.QPBT.heteroKron 1 Y) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ) +
          _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 Y) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ) := by
      rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_sub_op, sub_add_cancel]
    rw [hdecB, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_add, ← _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul _ (_root_.MIPStarRE.QPBT.heteroKron 1 Y), hcomm,
      _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · exact _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_le hL _
    · exact _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_le hYc _
  calc ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * A * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α *
          (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * B * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) - A * B) 1)
          (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ =
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * A * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α *
          B - A * B) 1) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ := by
        rw [_root_.MIPStarRE.QPBT.heteroKron_sub_left, _root_.MIPStarRE.QPBT.heteroKron_sub_left, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_sub_op,
          _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_sub_op, hstep1]
    _ = ‖-_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * A *
          ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * B)) 1) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ) -
          _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * A) * B) 1)
            (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ := by
        rw [hdec, _root_.MIPStarRE.QPBT.heteroKron_sub_left, _root_.MIPStarRE.QPBT.heteroKron_neg_left, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_sub_op,
          _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_neg_op]
    _ ≤ ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α * A *
          ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * B)) 1) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ +
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) * A) * B) 1)
            (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_neg]
    _ ≤ _ := by linarith [hfirst, hsecond]
