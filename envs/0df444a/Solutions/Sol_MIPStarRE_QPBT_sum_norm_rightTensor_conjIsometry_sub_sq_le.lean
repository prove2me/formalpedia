-- Prove2me | solution 1 for MIPStarRE.QPBT.sum_norm_rightTensor_conjIsometry_sub_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:49:50.954474+00:00
-- url     : https://prove2.me/submissions/bcf8ed31-c7dd-42b7-ace0-075461c71f54

-- Generated proof for MIPStarRE.QPBT.sum_norm_rightTensor_conjIsometry_sub_sq_le.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_isometryMatrix_conjTranspose_mul
import Theorems.Thm_MIPStarRE_QPBT_sum_norm_mul_projection_sub_sq_le

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





/-- The two-sided isometry image of a bipartite state, written through the
Kronecker product of the two isometry matrices. -/
theorem isometryTensor_apply_eq {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (p : κA × κB) :
    _root_.MIPStarRE.QPBT.isometryTensor φA φB ψ p =
      ∑ q : ιA × ιB,
        Matrix.kronecker (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φA) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φB) p q * ψ q := by
  simp [_root_.MIPStarRE.QPBT.isometryTensor, Matrix.kronecker, Fintype.sum_prod_type, _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_apply,
    EuclideanSpace.equiv, mul_assoc]





/-! ## Transfer of state-dependent bounds -/

















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











/-- Applying a product of rectangular matrices is successive application. -/
theorem toEuclideanLin_mul_apply {m n o : Type*} [Fintype n] [Fintype o]
    [DecidableEq n] [DecidableEq o]
    (A : Matrix m n ℂ) (B : Matrix n o ℂ) (v : EuclideanSpace ℂ o) :
    Matrix.toEuclideanLin (A * B) v =
      Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]























/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/









/-! ## Matrices of isometries -/







/-- Conjugation by an isometry is multiplicative. -/
theorem conjIsometry_mul {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') (A B : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.conjIsometry φ A * _root_.MIPStarRE.QPBT.conjIsometry φ B = _root_.MIPStarRE.QPBT.conjIsometry φ (A * B) := by
  simp only [_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_eq, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ),
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_conjTranspose_mul, Matrix.one_mul]



/-- The two-sided isometry image of a state is the action of the Kronecker
product of the two isometry matrices. -/
theorem isometryTensor_eq_toEuclideanLin {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.isometryTensor φA φB ψ =
      Matrix.toEuclideanLin
        (Matrix.kronecker (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φA) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φB)) ψ := by
  ext p
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_apply_eq]
  simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]







/-- A right-placed conjugated operator acts on the transported state as the
right-placed original operator acts on the original state. -/
theorem applyOperatorToState_rightTensor_conjIsometry {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (Y : _root_.LIDT.MIPStarRE.Quantum.Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.conjIsometry φB Y)) (_root_.MIPStarRE.QPBT.isometryTensor φA φB ψ) =
      _root_.MIPStarRE.QPBT.isometryTensor φA φB (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 Y) ψ) := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_eq_toEuclideanLin, _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_eq_toEuclideanLin]
  unfold _root_.MIPStarRE.QPBT.applyOperatorToState
  rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.toEuclideanLin_mul_apply, ← _root_.MIPStarRE.QPBT.MagicSquareRigidity.toEuclideanLin_mul_apply]
  refine congrArg (fun M => Matrix.toEuclideanLin M ψ) ?_
  unfold _root_.MIPStarRE.QPBT.heteroKron Matrix.kronecker
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_eq, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_assoc, _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_conjTranspose_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one]

/-! ## The ground projection -/





















/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





end

end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/Soundness/RangeProjection.lean. -/
/-!
# Range projections in Pauli soundness

Inserting an orthogonal projection into a measurement comparison costs at most
twice the squared distance to a vector fixed by that projection. Summing over
the measurement outcomes introduces no factor depending on their number.

## References

These are formalization-only auxiliary estimates for the final proof of
blueprint `thm:pauli`. The range projection is omitted at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`;
the corrected calculation is given in `docs/paper-gaps/qpbt_extraction-transfer.tex`.
They do not construct the extraction data or prove Pauli soundness.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open DistanceCalculus MagicSquareRigidity

/-- The identity conjugated by an isometry is its orthogonal range projection. -/
private theorem conjIsometry_one_isProj {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (phi : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) :
    _root_.LIDT.MIPStarRE.Quantum.IsProj (_root_.MIPStarRE.QPBT.conjIsometry phi 1) := by
  constructor
  · change _root_.MIPStarRE.QPBT.conjIsometry phi 1 * _root_.MIPStarRE.QPBT.conjIsometry phi 1 = _root_.MIPStarRE.QPBT.conjIsometry phi 1
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_mul, Matrix.one_mul]
  · change star (_root_.MIPStarRE.QPBT.conjIsometry phi 1) = _root_.MIPStarRE.QPBT.conjIsometry phi 1
    simp [_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_eq, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]

/-- Intertwining identifies isometry conjugation with insertion of its range projection. -/
private theorem mul_conjIsometry_one_eq {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (phi : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) (N : _root_.LIDT.MIPStarRE.Quantum.Op κ)
    (hintertwine : N * _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix phi = _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix phi * M) :
    N * _root_.MIPStarRE.QPBT.conjIsometry phi 1 = _root_.MIPStarRE.QPBT.conjIsometry phi M := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_eq, Matrix.mul_one, ← Matrix.mul_assoc, hintertwine]
  rfl









end MIPStarRE.QPBT

/-!
# Range projections in Pauli soundness

Inserting an orthogonal projection into a measurement comparison costs at most
twice the squared distance to a vector fixed by that projection. Summing over
the measurement outcomes introduces no factor depending on their number.

## References

These are formalization-only auxiliary estimates for the final proof of
blueprint `thm:pauli`. The range projection is omitted at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1864-1875`;
the corrected calculation is given in `docs/paper-gaps/qpbt_extraction-transfer.tex`.
They do not construct the extraction data or prove Pauli soundness.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus MIPStarRE.QPBT.MagicSquareRigidity

theorem solution {α ιA ιB κA κB : Type}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (phiA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (phiB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (M : α → _root_.LIDT.MIPStarRE.Quantum.Op ιB) (N : _root_.LIDT.MIPStarRE.Quantum.Measurement α κB)
    (T : α → _root_.LIDT.MIPStarRE.Quantum.Op (κA × κB))
    (hintertwine : ∀ a : α,
      N.effect a * _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix phiB = _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix phiB * M a)
    (psi : EuclideanSpace ℂ (ιA × ιB)) (delta : EuclideanSpace ℂ (κA × κB)) :
    ∑ a : α, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.conjIsometry phiB (M a)) - T a) delta‖ ^ 2 ≤
      2 * (∑ a : α, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 (N.effect a) - T a) delta‖ ^ 2) +
        2 * ‖delta - _root_.MIPStarRE.QPBT.isometryTensor phiA phiB psi‖ ^ 2 := by
  let Q : _root_.LIDT.MIPStarRE.Quantum.Op (κA × κB) := _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.conjIsometry phiB 1)
  have hQ : _root_.LIDT.MIPStarRE.Quantum.IsProj Q := by
    constructor
    · change Q * Q = Q
      simp only [Q, _root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.one_mul,
        (conjIsometry_one_isProj phiB).isIdempotentElem.eq]
    · change star Q = Q
      simp only [Q, Matrix.star_eq_conjTranspose, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker,
        Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        (conjIsometry_one_isProj phiB).isSelfAdjoint.isHermitian.eq]
  have hfix : _root_.MIPStarRE.QPBT.applyOperatorToState Q (_root_.MIPStarRE.QPBT.isometryTensor phiA phiB psi) =
      _root_.MIPStarRE.QPBT.isometryTensor phiA phiB psi := by
    dsimp only [Q]
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_rightTensor_conjIsometry, _root_.MIPStarRE.QPBT.heteroKron_one_one,
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_one]
  have hcompression (a : α) : (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement N).effect a * Q =
      _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.conjIsometry phiB (M a)) := by
    change _root_.MIPStarRE.QPBT.heteroKron 1 (N.effect a) * _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.conjIsometry phiB 1) = _
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.one_mul,
      mul_conjIsometry_one_eq phiB (M a) (N.effect a) (hintertwine a)]
  have hbound := _root_.MIPStarRE.QPBT.sum_norm_mul_projection_sub_sq_le (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement N) T Q hQ
    (_root_.MIPStarRE.QPBT.isometryTensor phiA phiB psi) delta hfix
  simp only [hcompression] at hbound
  simpa only [_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] using hbound
