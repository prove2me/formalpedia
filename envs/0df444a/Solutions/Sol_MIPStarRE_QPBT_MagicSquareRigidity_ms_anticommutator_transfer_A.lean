-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.ms_anticommutator_transfer_A
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:41:35.483982+00:00
-- url     : https://prove2.me/submissions/9e2c3ee2-c7ed-43cf-9076-9f68f7fe8e82

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.ms_anticommutator_transfer_A.
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
import Definitions.Def_QPBT_QPBT_Games_CondLinear
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Basic
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Relations
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Transfer
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_conjTranspose_mul_le_one_of_obsOf
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_naimarkCompression_naimarkDilatedEffect
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_norm_intertwine_obs_le_A
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_norm_leftTensor_compressed_product_sub_le
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_norm_leftTensor_one_sub_groundProjection_mul_le
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_norm_product_transfer_le_A
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_rejection_mass_le_thirty_six_mul_total
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_sum_norm_sq_intertwining_le_reverse
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_total_rejection_mass_eq_one_sub_value
import Theorems.Thm_MIPStarRE_QPBT_outcome_event_weight_mono

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

/- Source helpers from QPBT/Games/Consistency.lean. -/
/-! # State-dependent consistency and strategy closeness

The definitions are the finite-dimensional forms of blueprint
`def:consistency` and `def:strategy-distance`,
from `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-288`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum















/-- The unit-alphabet operator distance equals its one-outcome family form from
blueprint `def:povm-distance`, paper
`06_nonlocal_games_and_mipstar.tex:258-271`. -/
theorem opDistSq_eq_opFamilyDistSq {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (M N : X → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opDistSq μ M N ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x (_ : Unit) => M x)
      (fun x (_ : Unit) => N x) ψ := rfl



end MIPStarRE.QPBT

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



/-- Conjugation by an isometry is conjugation by its matrix. -/
theorem conjIsometry_eq {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.conjIsometry φ M = _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * M * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ := rfl

/-- The matrix of an isometry acts on vectors as the isometry does. -/
theorem isometryMatrix_mulVec {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (x : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ *ᵥ WithLp.ofLp x = WithLp.ofLp (φ x) := by
  have h : Matrix.toEuclideanLin (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ) = φ.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply φ.toLinearMap
  have h' : Matrix.toEuclideanLin (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ) x = φ x := by rw [h]; rfl
  simpa using congrArg WithLp.ofLp h'

/-- The columns of the matrix of an isometry are the images of the basis
vectors. -/
theorem isometryMatrix_apply {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (k : ι') (i : ι) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ k i =
      φ ((EuclideanSpace.equiv ι ℂ).symm (Pi.single i 1)) k := by
  have h := congrFun (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_mulVec φ
    ((EuclideanSpace.equiv ι ℂ).symm (Pi.single i 1))) k
  rw [← h]
  simp [Matrix.mulVec, dotProduct, EuclideanSpace.equiv, eq_comm]

/-- The matrix of a composite isometry is the product of the two matrices. -/
theorem isometryMatrix_comp {ι κ ν : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (φ : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ν)
    (E : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix (φ.comp E) = _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix E := by
  ext k i
  have h := congrFun (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_mulVec φ
    (E ((EuclideanSpace.equiv ι ℂ).symm (Pi.single i 1)))) k
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_apply, Matrix.mul_apply]
  simp only [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_apply E]
  simpa [Matrix.mulVec, dotProduct] using h.symm

/-- Conjugating by a composite isometry is conjugating twice.  This is how the
ground embeddings of the dilation combine with the local isometries produced by
the self-testing argument of blueprint
`thm:ms-rigidity`. -/
theorem conjIsometry_comp {ι κ ν : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (φ : EuclideanSpace ℂ κ →ₗᵢ[ℂ] EuclideanSpace ℂ ν)
    (E : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.conjIsometry (φ.comp E) M = _root_.MIPStarRE.QPBT.conjIsometry φ (_root_.MIPStarRE.QPBT.conjIsometry E M) := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_eq, _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_eq, _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_eq, _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_comp]
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]







/-! ## Transfer of state-dependent bounds -/

/-- Conjugating an operator by the ground embedding inflates it: the result acts
as the original operator on the ground slice and annihilates the orthogonal
complement. -/
theorem conjIsometry_naimarkEmbedding {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.conjIsometry (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkEmbedding ι α) M = _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) M := by
  ext p q
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_eq]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_apply,
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkEmbedding_apply, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_apply, EuclideanSpace.equiv]
  by_cases hp : p.2 = none
  · by_cases hq : q.2 = none <;> simp [hp, hq, eq_comm]
  · simp [hp]

/-- Conjugating an operator by the ground embedding followed by a later local
isometry is conjugating its inflation by that isometry.  This is the form in
which the conclusions of a self-testing argument applied to the dilated strategy
are read back on the original strategy. -/
theorem conjIsometry_comp_naimarkEmbedding {ι α κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ (ι × Option α) →ₗᵢ[ℂ] EuclideanSpace ℂ κ) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.conjIsometry (φ.comp (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkEmbedding ι α)) M =
      _root_.MIPStarRE.QPBT.conjIsometry φ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) M) := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_comp, _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_naimarkEmbedding]

/-- Compressing one of Alice's dilated Magic Square effects to the ground slice
returns her original effect. -/
theorem naimarkCompression_msDilatedStrategy_A_effect (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame)
    (x : _root_.MIPStarRE.QPBT.MsType) (a : _root_.MIPStarRE.QPBT.MsAnswer) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression (α := _root_.MIPStarRE.QPBT.MsAnswer) (((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).A x).effect a) =
      (S.A x).effect a :=
  _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression_naimarkDilatedEffect (α := _root_.MIPStarRE.QPBT.MsAnswer) (S.A x) (_root_.MIPStarRE.QPBT.MsAnswer.bit 0) a











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







/-- The average over the one-point uniform distribution is the sum over the
outcomes. -/
theorem opFamilyDistSq_uniform_unit {γ ι : Type*} [Fintype γ] [Fintype ι]
    [DecidableEq ι] (M N : Unit → γ → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit) M N ψ =
      ∑ c : γ, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M () c - N () c) ψ‖ ^ 2 := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq _root_.LIDT.MIPStarRE.LDT.avgOver
  simp [_root_.LIDT.MIPStarRE.LDT.uniformDistribution, _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset_weight]

/-! ## Matrices of isometries -/





















/-! ## The ground projection -/









/-- Inflating the compression of an operator to the ground slice is compressing
it by the ground projection. -/
theorem naimarkInflation_naimarkCompression {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (P : _root_.LIDT.MIPStarRE.Quantum.Op (ι × Option α)) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression (α := α) P) =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ι α * P * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ι α := by
  ext p q
  simp only [Matrix.mul_apply, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_apply, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression_apply,
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection, Fintype.sum_prod_type, Fintype.sum_option, Matrix.one_apply]
  by_cases hp : p.2 = none <;> by_cases hq : q.2 = none <;> simp [hp, hq]

/-- Compression to the ground slice commutes with finite sums. -/
theorem naimarkCompression_finset_sum {ι α β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (s : Finset β) (M : β → _root_.LIDT.MIPStarRE.Quantum.Op (ι × Option α)) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression (α := α) (∑ b ∈ s, M b) =
      ∑ b ∈ s, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression (α := α) (M b) := by
  ext i j
  simp [Matrix.sum_apply]









/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





end

end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Relations.lean. -/
/-!
# Magic Square value-to-parity relations

This file extracts the elementary probability relations used at the start of
the Magic Square rigidity argument.  A strategy of value at least `1 - ε` has
total rejection mass at most `ε`.  Since the question distribution is
supported on at most 36 directed incidences, the rejection mass at each
incidence is at most `36 * ε`.  This controls malformed answers, consistency
of the two reported bits at every cell, and the parity product on each of the
six row or column constraints.

The arguments apply to arbitrary finite POVMs.  In particular, malformed
answers remain in the event masses when `msBitOrZero` and
`constraintBitOrZero` turn the common answer alphabet into binary outcomes.

## References

The Magic Square game is defined in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`
and blueprint `def:ms-game`.  These relations are the
probabilistic input to the rigidity result cited at paper lines 612-652 from
Coladangelo--Stark, Theorem 6.9.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## The directed incidence distribution -/









/-- A variable-to-constraint incidence belongs to the question support. -/
theorem ms_reverse_incidence_mem_support (i : Fin 6) (k : Fin 3) :
    (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k), .constraint i) ∈
      (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty).support := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Sym2.eq_swap]
  exact Finset.mem_image.mpr ⟨(i, k), Finset.mem_univ _, rfl⟩



/-! ## Rejection mass from the game value -/



















/-- Value at least `1 - ε` implies total rejection mass at most `ε`. -/
theorem total_rejection_mass_le (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) : _root_.MIPStarRE.QPBT.MagicSquareRigidity.totalRejectionMass S ≤ ε := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.total_rejection_mass_eq_one_sub_value]
  linarith





/-- A supported conditioned rejection mass is at most `36 * ε`. -/
theorem rejection_mass_le (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) {xy : _root_.MIPStarRE.QPBT.MsType × _root_.MIPStarRE.QPBT.MsType}
    (hxy : xy ∈ (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty).support) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S xy.1 xy.2 ≤ 36 * ε := by
  calc
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S xy.1 xy.2 ≤ 36 * _root_.MIPStarRE.QPBT.MagicSquareRigidity.totalRejectionMass S :=
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejection_mass_le_thirty_six_mul_total S hxy
    _ ≤ 36 * ε :=
      mul_le_mul_of_nonneg_left (_root_.MIPStarRE.QPBT.MagicSquareRigidity.total_rejection_mass_le S ε hwin) (by norm_num)

/-- An event which always rejects has mass at most the conditioned rejection mass. -/
theorem outcome_event_weight_le_rejection_mass (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (x y : _root_.MIPStarRE.QPBT.MsType)
    (E : _root_.MIPStarRE.QPBT.MsAnswer → _root_.MIPStarRE.QPBT.MsAnswer → Prop) [DecidableRel E]
    (hE : ∀ a b, E a b → _root_.MIPStarRE.QPBT.msWinPredicate x y a b = false) :
    _root_.MIPStarRE.QPBT.outcomeEventWeight S x y E ≤ _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S x y := by
  unfold _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass
  letI : DecidableRel (fun a b : _root_.MIPStarRE.QPBT.MsAnswer => _root_.MIPStarRE.QPBT.msWinPredicate x y a b = false) :=
    fun _ _ => inferInstance
  exact _root_.MIPStarRE.QPBT.outcome_event_weight_mono S x y E _ hE

/-! ## Malformed answers and cell consistency -/



















/-- The three cells in any fixed row or column are distinct. -/
theorem constraint_vars_injective (i : Fin 6) : Function.Injective (_root_.MIPStarRE.QPBT.msConstraintVars i) := by
  intro k l hkl
  apply Fin.ext
  unfold _root_.MIPStarRE.QPBT.msConstraintVars at hkl
  split at hkl <;> simp only [Fin.mk.injEq] at hkl ⊢ <;> omega

/-- Every Magic Square variable is incident to a row constraint. -/
theorem every_variable_is_incident (j : Fin 9) :
    ∃ i : Fin 6, ∃ k : Fin 3, _root_.MIPStarRE.QPBT.msConstraintVars i k = j := by
  let i : Fin 6 := ⟨j.val / 3, by omega⟩
  let k : Fin 3 := ⟨j.val % 3, Nat.mod_lt _ (by omega)⟩
  refine ⟨i, k, ?_⟩
  apply Fin.ext
  simp only [_root_.MIPStarRE.QPBT.msConstraintVars, i, k]
  rw [if_pos (by omega)]
  omega



























private theorem reverse_cell_mismatch_rejects (i : Fin 6) (k : Fin 3)
    (a b : _root_.MIPStarRE.QPBT.MsAnswer) (hmismatch : _root_.MIPStarRE.QPBT.msBitOrZero a ≠ _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k b) :
    _root_.MIPStarRE.QPBT.msWinPredicate (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) (.constraint i) a b = false := by
  cases a with
  | triple α => rfl
  | bit γ =>
      cases b with
      | bit γb => rfl
      | triple β =>
          simp only [_root_.MIPStarRE.QPBT.msBitOrZero, _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero] at hmismatch
          rw [_root_.MIPStarRE.QPBT.msWinPredicate, decide_eq_false_iff_not]
          intro haccept
          rcases haccept.2 with ⟨l, hl, hbit⟩
          have hlk : l = k := _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraint_vars_injective i hl
          subst l
          exact hmismatch hbit.symm



/-- Every reverse directed incidence has cell-mismatch mass at most `36 * ε`. -/
theorem reverse_cell_mismatch_mass_le (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k : Fin 3) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.reverseCellMismatchMass S i k ≤ 36 * ε := by
  unfold _root_.MIPStarRE.QPBT.MagicSquareRigidity.reverseCellMismatchMass
  calc
    _root_.MIPStarRE.QPBT.outcomeEventWeight S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) (.constraint i)
        (fun a b => _root_.MIPStarRE.QPBT.msBitOrZero a ≠ _root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k b) ≤
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) (.constraint i) :=
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.outcome_event_weight_le_rejection_mass S _ _ _ (reverse_cell_mismatch_rejects i k)
    _ ≤ 36 * ε :=
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejection_mass_le S ε hwin (_root_.MIPStarRE.QPBT.MagicSquareRigidity.ms_reverse_incidence_mem_support i k)

/-! ## Row and column parity products -/





































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

/-- Compressing one of Alice's dilated postprocessed effects returns her original
postprocessed effect. -/
theorem naimarkCompression_dilatedEffectA (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (x : _root_.MIPStarRE.QPBT.MsType)
    (f : _root_.MIPStarRE.QPBT.MsAnswer → ZMod 2) (b : ZMod 2) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectA S x f b) = ((S.A x).postprocess f).effect b := by
  have h := (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression_finset_sum (Finset.univ.filter fun a : _root_.MIPStarRE.QPBT.MsAnswer => f a = b)
    fun a => ((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).A x).effect a).trans
    (Finset.sum_congr rfl fun a _ => _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression_msDilatedStrategy_A_effect S x a)
  exact h



/-- The inflation of Alice's original postprocessed effect is the ground
compression `Π P Π` of her dilated one. -/
theorem naimarkInflation_postprocess_A (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (x : _root_.MIPStarRE.QPBT.MsType)
    (f : _root_.MIPStarRE.QPBT.MsAnswer → ZMod 2) (b : ZMod 2) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := _root_.MIPStarRE.QPBT.MsAnswer) (((S.A x).postprocess f).effect b) =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA _root_.MIPStarRE.QPBT.MsAnswer * _root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectA S x f b *
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA _root_.MIPStarRE.QPBT.MsAnswer := by
  rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression_dilatedEffectA, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_naimarkCompression]











/-! ## Transfer of the effect estimates -/















/-! ## Transfer of the anticommutator estimates -/

/-- Inflation respects differences. -/
theorem naimarkInflation_sub {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) (M - N) =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) M - _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) N := by
  ext p q
  by_cases h : p.2 = none ∧ q.2 = none <;> simp [h]

/-- The action on states respects differences of operators. -/
theorem applyOperatorToState_sub_op {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : _root_.LIDT.MIPStarRE.Quantum.Op ι) (v : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (M - N) v =
      _root_.MIPStarRE.QPBT.applyOperatorToState M v - _root_.MIPStarRE.QPBT.applyOperatorToState N v := by
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState]



/-- The one-outcome distance under the one-point uniform distribution. -/
theorem opDistSq_uniform_unit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Unit → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit) M N ψ =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M () - N ()) ψ‖ ^ 2 := by
  rw [_root_.MIPStarRE.QPBT.opDistSq_eq_opFamilyDistSq, _root_.MIPStarRE.QPBT.MagicSquareRigidity.opFamilyDistSq_uniform_unit]
  simp





/-- The inflation of Alice's original observable is the ground compression of
her dilated observable. -/
theorem naimarkInflation_obs_A (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (x : _root_.MIPStarRE.QPBT.MsType) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := _root_.MIPStarRE.QPBT.MsAnswer) (_root_.MIPStarRE.QPBT.obsOf ((S.A x).postprocess _root_.MIPStarRE.QPBT.msBitOrZero)) =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA _root_.MIPStarRE.QPBT.MsAnswer * _root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S x * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA _root_.MIPStarRE.QPBT.MsAnswer := by
  change _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := _root_.MIPStarRE.QPBT.MsAnswer) (((S.A x).postprocess _root_.MIPStarRE.QPBT.msBitOrZero).effect 0 -
    ((S.A x).postprocess _root_.MIPStarRE.QPBT.msBitOrZero).effect 1) =
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA _root_.MIPStarRE.QPBT.MsAnswer *
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectA S x _root_.MIPStarRE.QPBT.msBitOrZero 0 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectA S x _root_.MIPStarRE.QPBT.msBitOrZero 1) *
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA _root_.MIPStarRE.QPBT.MsAnswer
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_sub, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_postprocess_A, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_postprocess_A,
    Matrix.mul_sub, Matrix.sub_mul]

/-- Alice's dilated observables are contractions. -/
theorem conjTranspose_mul_le_one_dilatedObsA (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (x : _root_.MIPStarRE.QPBT.MsType) :
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S x)ᴴ * _root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S x ≤ 1 :=
  _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_of_obsOf _

/-- Bob's dilated observables are contractions. -/
theorem conjTranspose_mul_le_one_dilatedObsB (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (y : _root_.MIPStarRE.QPBT.MsType)
    (f : _root_.MIPStarRE.QPBT.MsAnswer → ZMod 2) :
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsB S y f)ᴴ * _root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsB S y f ≤ 1 :=
  _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_of_obsOf _

/-- The leakage of Alice's dilated observable out of the ground slice is bounded
by the two intertwining defects of its effects. -/
theorem norm_leak_obs_le_A (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (i : Fin 6) (k : Fin 3) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA _root_.MIPStarRE.QPBT.MsAnswer) *
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k))) 1) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ)‖ ≤
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectA S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) _root_.MIPStarRE.QPBT.msBitOrZero 0) 1 -
          _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectB S (.constraint i) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k) 0))
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ)‖ +
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectA S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) _root_.MIPStarRE.QPBT.msBitOrZero 1) 1 -
          _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectB S (.constraint i) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k) 1))
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ)‖ := by
  change ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron ((1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA _root_.MIPStarRE.QPBT.MsAnswer) *
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectA S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) _root_.MIPStarRE.QPBT.msBitOrZero 0 -
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedEffectA S (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k)) _root_.MIPStarRE.QPBT.msBitOrZero 1)) 1)
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ)‖ ≤ _
  rw [Matrix.mul_sub, _root_.MIPStarRE.QPBT.heteroKron_sub_left, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_sub_op]
  refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
  · exact _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_leftTensor_one_sub_groundProjection_mul_le _root_.MIPStarRE.QPBT.MsAnswer S.ψ _ _
  · exact _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_leftTensor_one_sub_groundProjection_mul_le _root_.MIPStarRE.QPBT.MsAnswer S.ψ _ _







/-- The square of a two-term leakage sum is controlled by the cell-mismatch
mass. -/
theorem sq_add_le_of_sum_sq_le (ℓ : ZMod 2 → ℝ) (m ε : ℝ)
    (hL : ∑ b, ℓ b ^ 2 ≤ 2 * m) (hm : m ≤ 36 * ε) :
    (ℓ 0 + ℓ 1) ^ 2 ≤ 144 * ε := by
  have h2 : ∑ b : Fin 2, ℓ b ^ 2 ≤ 2 * m := hL
  rw [Fin.sum_univ_two] at h2
  have h3 : ℓ 0 ^ 2 + ℓ 1 ^ 2 ≤ 2 * m := h2
  nlinarith [sq_nonneg (ℓ 0 - ℓ 1)]

/-- The final arithmetic of the anticommutator transfer. -/
theorem anticommutator_arith {o a x z η ε : ℝ} (ho : 0 ≤ o)
    (h : o ≤ a + (x + 2 * z + 2 * η) + (z + 2 * x + 2 * η))
    (hx : x ^ 2 ≤ 144 * ε) (hz : z ^ 2 ≤ 144 * ε) :
    o ^ 2 ≤ 3 * a ^ 2 + 15552 * ε + 48 * η ^ 2 := by
  have h1 : o ^ 2 ≤ (a + 3 * (x + z) + 4 * η) ^ 2 :=
    pow_le_pow_left₀ ho (by linarith) 2
  have h2 : (a + 3 * (x + z) + 4 * η) ^ 2 ≤
      3 * a ^ 2 + 3 * (3 * (x + z)) ^ 2 + 3 * (4 * η) ^ 2 := by
    nlinarith [sq_nonneg (a - 3 * (x + z)), sq_nonneg (3 * (x + z) - 4 * η),
      sq_nonneg (a - 4 * η)]
  have h3 : (x + z) ^ 2 ≤ 2 * x ^ 2 + 2 * z ^ 2 := by nlinarith [sq_nonneg (x - z)]
  nlinarith [h1, h2, h3, hx, hz]



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

theorem solution {κA κB : Type} [Fintype κA] [DecidableEq κA]
    [Fintype κB] [DecidableEq κB] (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame)
    (φA : EuclideanSpace ℂ (S.ιA × Option _root_.MIPStarRE.QPBT.MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ (S.ιB × Option _root_.MIPStarRE.QPBT.MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ξ : EuclideanSpace ℂ (κA × κB)) (ε η : ℝ)
    (hwin : 1 - ε ≤ S.value)
    (hξ : ‖_root_.MIPStarRE.QPBT.isometryTensor φA φB (_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).ψ - ξ‖ ≤ η) :
    _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun _ => _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry (φA.comp (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkEmbedding S.ιA _root_.MIPStarRE.QPBT.MsAnswer))
            (_root_.MIPStarRE.QPBT.obsOf ((S.A (.var 0)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))) 1 *
          _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry (φA.comp (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkEmbedding S.ιA _root_.MIPStarRE.QPBT.MsAnswer))
            (_root_.MIPStarRE.QPBT.obsOf ((S.A (.var 4)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))) 1)
        (fun _ => -(_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry (φA.comp (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkEmbedding S.ιA _root_.MIPStarRE.QPBT.MsAnswer))
            (_root_.MIPStarRE.QPBT.obsOf ((S.A (.var 4)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))) 1 *
          _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry (φA.comp (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkEmbedding S.ιA _root_.MIPStarRE.QPBT.MsAnswer))
            (_root_.MIPStarRE.QPBT.obsOf ((S.A (.var 0)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))) 1)) ξ ≤
      3 * _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun _ => _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry φA
            (_root_.MIPStarRE.QPBT.obsOf (((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).A (.var 0)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))) 1 *
          _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry φA
            (_root_.MIPStarRE.QPBT.obsOf (((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).A (.var 4)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))) 1)
        (fun _ => -(_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry φA
            (_root_.MIPStarRE.QPBT.obsOf (((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).A (.var 4)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))) 1 *
          _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry φA
            (_root_.MIPStarRE.QPBT.obsOf (((_root_.MIPStarRE.QPBT.MagicSquareRigidity.msDilatedStrategy S).A (.var 0)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))) 1)) ξ +
      15552 * ε + 48 * η ^ 2 := by
  obtain ⟨i0, k0, h0⟩ := _root_.MIPStarRE.QPBT.MagicSquareRigidity.every_variable_is_incident 0
  obtain ⟨i4, k4, h4⟩ := _root_.MIPStarRE.QPBT.MagicSquareRigidity.every_variable_is_incident 4
  have hξ' : ‖_root_.MIPStarRE.QPBT.isometryTensor φA φB (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ) - ξ‖ ≤ η := hξ
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.opDistSq_uniform_unit, _root_.MIPStarRE.QPBT.MagicSquareRigidity.opDistSq_uniform_unit, _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_comp_naimarkEmbedding,
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_comp_naimarkEmbedding, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_obs_A, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_obs_A]
  change ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry φA (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA _root_.MIPStarRE.QPBT.MsAnswer *
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 0) * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA _root_.MIPStarRE.QPBT.MsAnswer)) 1 *
      _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry φA (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA _root_.MIPStarRE.QPBT.MsAnswer *
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 4) * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA _root_.MIPStarRE.QPBT.MsAnswer)) 1 -
      -(_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry φA (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA _root_.MIPStarRE.QPBT.MsAnswer *
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 4) * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA _root_.MIPStarRE.QPBT.MsAnswer)) 1 *
      _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry φA (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA _root_.MIPStarRE.QPBT.MsAnswer *
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 0) * _root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA _root_.MIPStarRE.QPBT.MsAnswer)) 1)) ξ‖ ^ 2 ≤
    3 * ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry φA (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 0))) 1 *
      _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry φA (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 4))) 1 -
      -(_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry φA (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 4))) 1 *
      _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry φA (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 0))) 1)) ξ‖ ^ 2 +
    15552 * ε + 48 * η ^ 2
  have hXc := _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_dilatedObsA S (.var 0)
  have hZc := _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_dilatedObsA S (.var 4)
  have hYXc := _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_dilatedObsB S (.constraint i0) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k0)
  have hYZc := _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_dilatedObsB S (.constraint i4) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k4)
  -- leakage and intertwining of the two observables
  have hleakX := _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_leak_obs_le_A S i0 k0
  have hintX := _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_intertwine_obs_le_A S i0 k0
  have hleakZ := _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_leak_obs_le_A S i4 k4
  have hintZ := _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_intertwine_obs_le_A S i4 k4
  have hsqX := _root_.MIPStarRE.QPBT.MagicSquareRigidity.sq_add_le_of_sum_sq_le _ _ ε (_root_.MIPStarRE.QPBT.MagicSquareRigidity.sum_norm_sq_intertwining_le_reverse S i0 k0)
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.reverse_cell_mismatch_mass_le S ε hwin i0 k0)
  have hsqZ := _root_.MIPStarRE.QPBT.MagicSquareRigidity.sq_add_le_of_sum_sq_le _ _ ε (_root_.MIPStarRE.QPBT.MagicSquareRigidity.sum_norm_sq_intertwining_le_reverse S i4 k4)
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.reverse_cell_mismatch_mass_le S ε hwin i4 k4)
  rw [h0] at hleakX hintX hsqX
  rw [h4] at hleakZ hintZ hsqZ
  -- product transfers
  have hXZ := _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_product_transfer_le_A S φA φB ξ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 0))
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 4)) hXc hZc
  have hZX := _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_product_transfer_le_A S φA φB ξ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 4))
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 0)) hZc hXc
  have hdXZ := _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_leftTensor_compressed_product_sub_le _root_.MIPStarRE.QPBT.MsAnswer S.ψ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 0))
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 4)) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsB S (.constraint i4) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k4)) hXc hYZc
  have hdZX := _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_leftTensor_compressed_product_sub_le _root_.MIPStarRE.QPBT.MsAnswer S.ψ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 4))
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 0)) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsB S (.constraint i0) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.constraintBitOrZero k0)) hZc hYXc
  -- the anticommutator on the target state
  have hsplit : ∀ (Xo Zo Xd Zd : _root_.LIDT.MIPStarRE.Quantum.Op (κA × κB)),
      _root_.MIPStarRE.QPBT.applyOperatorToState (Xo * Zo - -(Zo * Xo)) ξ =
        _root_.MIPStarRE.QPBT.applyOperatorToState (Xd * Zd - -(Zd * Xd)) ξ +
          _root_.MIPStarRE.QPBT.applyOperatorToState (Xo * Zo - Xd * Zd) ξ +
          _root_.MIPStarRE.QPBT.applyOperatorToState (Zo * Xo - Zd * Xd) ξ := by
    intro Xo Zo Xd Zd
    rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_add_op, ← _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_add_op]
    congr 1
    abel
  rw [hsplit _ _ (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry φA (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 0))) 1)
    (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry φA (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 4))) 1)]
  refine _root_.MIPStarRE.QPBT.MagicSquareRigidity.anticommutator_arith (norm_nonneg _) ?_ hsqX hsqZ
  refine le_trans (norm_add_le _ _) (le_trans (add_le_add_left (norm_add_le _ _) _) ?_)
  linarith [hXZ, hZX, hdXZ, hdZX, hleakX, hintX, hleakZ, hintZ, hξ']
