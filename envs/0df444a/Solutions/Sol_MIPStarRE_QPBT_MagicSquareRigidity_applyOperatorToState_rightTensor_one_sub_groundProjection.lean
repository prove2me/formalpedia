-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_rightTensor_one_sub_groundProjection
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:23:38.982988+00:00
-- url     : https://prove2.me/submissions/501da978-0fd3-4330-ba05-36875993fd22

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_rightTensor_one_sub_groundProjection.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice

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
right factor.  This is the general form of `heteroKron_sub_right` below. -/
theorem kroneckerMap_sub_right {m n p q : Type*} (A : Matrix m n ℂ) (B C : Matrix p q ℂ) :
    Matrix.kroneckerMap (· * ·) A (B - C) =
      Matrix.kroneckerMap (· * ·) A B - Matrix.kroneckerMap (· * ·) A C := by
  ext p' q'
  simp [Matrix.kroneckerMap, mul_sub]



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







/-- The dilated state lies in the ground slice on Bob's side. -/
theorem applyOperatorToState_rightTensor_groundProjection (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιB α)) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ) =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ := by
  have hfull : _root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιA α) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιB α))
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ) = _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ := by
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection, _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_heteroKron_naimarkInflation,
      _root_.MIPStarRE.QPBT.heteroKron_one_one, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_one]
  conv_lhs => rw [← hfull]
  rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, _root_.MIPStarRE.QPBT.heteroKron_mul,
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isProj_groundProjection ιB α).isIdempotentElem.eq, Matrix.one_mul]
  exact hfull





/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





end

end MIPStarRE.QPBT.MagicSquareRigidity

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



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Contractions and their action on states -/



































/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/









/-! ## Matrices of isometries -/





















/-! ## The ground projection -/

theorem solution (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 (1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιB α))
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ) = 0 := by
  have h : _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × Option α)) (1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιB α) =
      1 - _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιB α) := by
    rw [_root_.MIPStarRE.QPBT.heteroKron_sub_right, _root_.MIPStarRE.QPBT.heteroKron_one_one]
  have hsub : _root_.MIPStarRE.QPBT.applyOperatorToState (1 - _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιB α))
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ) =
      _root_.MIPStarRE.QPBT.applyOperatorToState 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ) -
        _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ιB α))
          (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ) := by
    simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
  rw [h, hsub, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_one, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_rightTensor_groundProjection,
    sub_self]
