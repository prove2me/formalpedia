-- Prove2me | solution 1 for MIPStarRE.QPBT.raw_pauli_operator_distanceB_le_completed
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:53:53.082081+00:00
-- url     : https://prove2.me/submissions/888fe94d-2f64-4d9a-8cb8-f1409c163e1e

-- Generated proof for MIPStarRE.QPBT.raw_pauli_operator_distanceB_le_completed.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_conjTranspose_mul_le_one_conjIsometry
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_isometryMatrix_conjTranspose_mul
import Theorems.Thm_MIPStarRE_QPBT_completedPauliEffect_eq_raw_add_wrongForm
import Theorems.Thm_MIPStarRE_QPBT_wrongFormPauliMass_bob_le_error

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
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

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











/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
is additive in the right factor. -/
theorem heteroKron_add_right {ιA ιB : Type*} (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B C : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron A (B + C) = _root_.MIPStarRE.QPBT.heteroKron A B + _root_.MIPStarRE.QPBT.heteroKron A C := by
  ext p q
  simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, mul_add]









/- The Euclidean linear map is the shared action used by the value and distance
functionals.  Keeping it at the Euclidean-space level avoids accidentally
using the function-space supremum norm of `Matrix.mulVec`. -/








































end MIPStarRE.QPBT

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
4.14): every effect of a complete measurement is bounded by the identity. -/
theorem measurement_effect_le_one {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (a : α) :
    M.effect a ≤ 1 := by
  calc
    M.effect a ≤ ∑ b : α, M.effect b :=
      Finset.single_le_sum (fun b _ => M.pos b) (Finset.mem_univ a)
    _ = 1 := M.sum_eq_one

















































end MIPStarRE.QPBT.DistanceCalculus

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







/-- An operator `K` with `Kᴴ K ≤ 1` does not increase norms. -/
theorem norm_applyOperatorToState_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hK : Kᴴ * K ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState K v‖ ≤ ‖v‖ := by
  have h := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hK v
  have hv : (inner ℂ v v).re = ‖v‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_sq, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_one, hv] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h







/-- Effects of a measurement are contractions. -/
theorem conjTranspose_mul_le_one_of_effect {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (a : α) :
    (M.effect a)ᴴ * M.effect a ≤ 1 := by
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
  exact le_trans (_root_.LIDT.MIPStarRE.Quantum.sq_le_self (M.pos a) (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one M a))
    (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one M a)





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

/-- The Kronecker product of two matrix isometries is a matrix isometry. -/
theorem kronecker_isometryMatrix_conjTranspose_mul {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB) :
    (Matrix.kronecker (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φA) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φB))ᴴ *
      Matrix.kronecker (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φA) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φB) = 1 := by
  unfold Matrix.kronecker
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_conjTranspose_mul, _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_conjTranspose_mul,
    Matrix.one_kronecker_one]

/-- The two-sided isometry image preserves norms. -/
theorem norm_isometryTensor {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖_root_.MIPStarRE.QPBT.isometryTensor φA φB ψ‖ = ‖ψ‖ := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_eq_toEuclideanLin]
  exact _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_toEuclideanLin_of_conjTranspose_mul_eq_one
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.kronecker_isometryMatrix_conjTranspose_mul φA φB) ψ



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

/- Source helpers from QPBT/Test/Soundness/RawOperatorTransferCore.lean. -/
/-!
# Transfer from completed to raw Pauli effects

The extraction proof uses the complete Pauli-register measurement obtained by
folding malformed answers into outcome zero. The source theorem instead
compares the raw effects attached to answers of the form `.pauliOutcome u`.
This module bounds the malformed-answer mass by rejection on the two oriented
point/Pauli edges and transfers the completed-family estimates to the raw
families without adding a hypothesis to the source theorem.

## References

Paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1431-1445`,
and its proof at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section





open DistanceCalculus







private theorem raw_transfer_liftedBEffect_eq_tensor {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {G : _root_.MIPStarRE.QPBT.Game}
    (S : _root_.MIPStarRE.QPBT.Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × _root_.MIPStarRE.QPBT.PauliRegister P)) (M : _root_.LIDT.MIPStarRE.Quantum.Op S.ιB) :
    _root_.MIPStarRE.QPBT.liftedBEffect S (ιA' := ιA') φB M =
      _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιA' × _root_.MIPStarRE.QPBT.PauliRegister P)) (_root_.MIPStarRE.QPBT.conjIsometry φB M) := by
  ext i j
  simp [_root_.MIPStarRE.QPBT.liftedBEffect, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.one_apply]



private theorem raw_transfer_liftedBEffect_add {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {G : _root_.MIPStarRE.QPBT.Game}
    (S : _root_.MIPStarRE.QPBT.Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × _root_.MIPStarRE.QPBT.PauliRegister P)) (A B : _root_.LIDT.MIPStarRE.Quantum.Op S.ιB) :
    _root_.MIPStarRE.QPBT.liftedBEffect S (ιA' := ιA') φB (A + B) =
      _root_.MIPStarRE.QPBT.liftedBEffect S φB A + _root_.MIPStarRE.QPBT.liftedBEffect S φB B := by
  rw [raw_transfer_liftedBEffect_eq_tensor, raw_transfer_liftedBEffect_eq_tensor,
    raw_transfer_liftedBEffect_eq_tensor, ← _root_.MIPStarRE.QPBT.heteroKron_add_right]
  congr 1
  simp [_root_.MIPStarRE.QPBT.conjIsometry, Matrix.mul_add, Matrix.add_mul]



























private theorem wrongFormEffect_eq_validity_effect {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliAnswer P) ι)
    (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.ProjectiveSetting.wrongFormEffect (.pauli W) M =
      (M.postprocess (_root_.MIPStarRE.QPBT.validPauliAnswer (.pauli W))).effect false := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.wrongFormEffect, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]



private theorem wrongFormEffect_ideal_norm_bob_le {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P)) (w : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P S)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (δ r : ℝ)
    (hstate : ‖_root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB S.ψ - _root_.MIPStarRE.QPBT.idealState P w.aux‖ ≤ δ)
    (hmass : _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.ψ
        (_root_.MIPStarRE.QPBT.heteroKron 1
          (_root_.MIPStarRE.QPBT.ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (_root_.MIPStarRE.QPBT.pauliQuestion P W)))) ≤ r) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB
          (_root_.MIPStarRE.QPBT.ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (_root_.MIPStarRE.QPBT.pauliQuestion P W))))
        (_root_.MIPStarRE.QPBT.idealState P w.aux)‖ ^ 2 ≤ 2 * δ ^ 2 + 2 * r := by
  let M := S.B (_root_.MIPStarRE.QPBT.pauliQuestion P W)
  let E := _root_.MIPStarRE.QPBT.ProjectiveSetting.wrongFormEffect (.pauli W) M
  let Q := _root_.MIPStarRE.QPBT.liftedBEffect S (ιA' := w.ιA') w.φB E
  let theta := _root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB S.ψ
  let Delta := _root_.MIPStarRE.QPBT.idealState P w.aux
  let N := M.postprocess (_root_.MIPStarRE.QPBT.validPauliAnswer (.pauli W))
  have hE : E = N.effect false := by
    exact wrongFormEffect_eq_validity_effect M W
  have hEcontr : Eᴴ * E ≤ 1 := by
    rw [hE]
    exact _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_of_effect N false
  have hQcontr : Qᴴ * Q ≤ 1 := by
    dsimp only [Q]
    rw [raw_transfer_liftedBEffect_eq_tensor]
    exact _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_rightTensor
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry w.φB hEcontr)
  have htheta : ‖_root_.MIPStarRE.QPBT.applyOperatorToState Q theta‖ ^ 2 ≤ r := by
    dsimp only [Q, theta]
    rw [raw_transfer_liftedBEffect_eq_tensor,
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_rightTensor_conjIsometry,
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_isometryTensor]
    have hEpos : 0 ≤ E := by rw [hE]; exact N.pos false
    have hEle : E ≤ 1 := by rw [hE]; exact _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one N false
    have hKpos : 0 ≤ _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.ιA) E :=
      _root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg (by simp) hEpos
    have hKle : _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.ιA) E ≤ 1 := by
      rw [← Matrix.one_kronecker_one]
      exact _root_.LIDT.MIPStarRE.Quantum.kronecker_le_kronecker_right_one (by simp) hEle
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_sq]
    have hKH : (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.ιA) E)ᴴ = _root_.MIPStarRE.QPBT.heteroKron 1 E :=
      (Matrix.nonneg_iff_posSemidef.mp hKpos).isHermitian.eq
    rw [hKH]
    exact (_root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono (_root_.LIDT.MIPStarRE.Quantum.sq_le_self hKpos hKle) S.ψ).trans
      hmass
  have hdecomp : _root_.MIPStarRE.QPBT.applyOperatorToState Q Delta =
      _root_.MIPStarRE.QPBT.applyOperatorToState Q (Delta - theta) + _root_.MIPStarRE.QPBT.applyOperatorToState Q theta := by
    simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
  rw [hdecomp]
  have hfirst : ‖_root_.MIPStarRE.QPBT.applyOperatorToState Q (Delta - theta)‖ ≤ δ := by
    exact (_root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_le hQcontr _).trans (by
      rw [norm_sub_rev]
      exact hstate)
  have htri := norm_add_le (_root_.MIPStarRE.QPBT.applyOperatorToState Q (Delta - theta))
    (_root_.MIPStarRE.QPBT.applyOperatorToState Q theta)
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hfirstsq := pow_le_pow_left₀
    (norm_nonneg (_root_.MIPStarRE.QPBT.applyOperatorToState Q (Delta - theta))) hfirst 2
  nlinarith [sq_nonneg (‖_root_.MIPStarRE.QPBT.applyOperatorToState Q (Delta - theta)‖ -
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState Q theta‖)]





end

end MIPStarRE.QPBT

/-!
# Transfer from completed to raw Pauli effects

The extraction proof uses the complete Pauli-register measurement obtained by
folding malformed answers into outcome zero. The source theorem instead
compares the raw effects attached to answers of the form `.pauliOutcome u`.
This module bounds the malformed-answer mass by rejection on the two oriented
point/Pauli edges and transfers the completed-family estimates to the raw
families without adding a hypothesis to the source theorem.

## References

Paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1431-1445`,
and its proof at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum





open MIPStarRE.QPBT.WinImplications







open MIPStarRE.QPBT.DistanceCalculus

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δ : ℝ}
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P)) (hwin : 1 - ε ≤ S.value)
    (w : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P S)
    (hstate : ‖_root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB S.ψ - _root_.MIPStarRE.QPBT.idealState P w.aux‖ ≤ δ)
    (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.rawPauliOperatorDistanceB P S w W ≤
      2 * _root_.MIPStarRE.QPBT.pauliOperatorDistanceB P S w W + 4 * δ ^ 2 +
        4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
  let M : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliAnswer P) S.ιB := S.B (_root_.MIPStarRE.QPBT.pauliQuestion P W)
  let E := _root_.MIPStarRE.QPBT.ProjectiveSetting.wrongFormEffect (.pauli W) M
  let bad := ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB E)
    (_root_.MIPStarRE.QPBT.idealState P w.aux)‖ ^ 2
  have hmass := _root_.MIPStarRE.QPBT.wrongFormPauliMass_bob_le_error S hwin W
  have hbad : bad ≤ 2 * δ ^ 2 + 2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
    simpa only [bad, E, M, mul_assoc] using
      wrongFormEffect_ideal_norm_bob_le S w W δ _ hstate hmass
  have hpoint (u : _root_.MIPStarRE.QPBT.PauliRegister P) :
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB (M.effect (.pauliOutcome u)) -
            _root_.MIPStarRE.QPBT.pauliProjOnB'' P W u) (_root_.MIPStarRE.QPBT.idealState P w.aux)‖ ^ 2 ≤
        2 * ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB
              ((M.postprocess _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect u) -
            _root_.MIPStarRE.QPBT.pauliProjOnB'' P W u) (_root_.MIPStarRE.QPBT.idealState P w.aux)‖ ^ 2 +
          if u = 0 then 2 * bad else 0 := by
    by_cases hu : u = 0
    · subst u
      rw [if_pos rfl, _root_.MIPStarRE.QPBT.completedPauliEffect_eq_raw_add_wrongForm M W 0]
      simp only [ite_true]
      have hvec :
          _root_.MIPStarRE.QPBT.applyOperatorToState
              (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB (M.effect (.pauliOutcome 0)) -
                _root_.MIPStarRE.QPBT.pauliProjOnB'' P W 0) (_root_.MIPStarRE.QPBT.idealState P w.aux) =
            _root_.MIPStarRE.QPBT.applyOperatorToState
                (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB (M.effect (.pauliOutcome 0) + E) -
                  _root_.MIPStarRE.QPBT.pauliProjOnB'' P W 0) (_root_.MIPStarRE.QPBT.idealState P w.aux) -
              _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB E)
                (_root_.MIPStarRE.QPBT.idealState P w.aux) := by
        rw [raw_transfer_liftedBEffect_add]
        simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, map_sub, LinearMap.sub_apply, map_add,
          LinearMap.add_apply]
        abel
      rw [hvec]
      have htri := norm_sub_le
        (_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB (M.effect (.pauliOutcome 0) + E) -
            _root_.MIPStarRE.QPBT.pauliProjOnB'' P W 0) (_root_.MIPStarRE.QPBT.idealState P w.aux))
        (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB E) (_root_.MIPStarRE.QPBT.idealState P w.aux))
      have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
      dsimp only [bad]
      nlinarith [sq_nonneg
        (‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB (M.effect (.pauliOutcome 0) + E) -
            _root_.MIPStarRE.QPBT.pauliProjOnB'' P W 0) (_root_.MIPStarRE.QPBT.idealState P w.aux)‖ -
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB E) (_root_.MIPStarRE.QPBT.idealState P w.aux)‖)]
    · rw [if_neg hu, _root_.MIPStarRE.QPBT.completedPauliEffect_eq_raw_add_wrongForm M W u]
      simp only [hu, ite_false, add_zero]
      nlinarith [sq_nonneg
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB (M.effect (.pauliOutcome u)) -
            _root_.MIPStarRE.QPBT.pauliProjOnB'' P W u) (_root_.MIPStarRE.QPBT.idealState P w.aux)‖]
  unfold _root_.MIPStarRE.QPBT.rawPauliOperatorDistanceB _root_.MIPStarRE.QPBT.pauliOperatorDistanceB
  change (∑ u : _root_.MIPStarRE.QPBT.PauliRegister P,
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB (M.effect (.pauliOutcome u)) - _root_.MIPStarRE.QPBT.pauliProjOnB'' P W u)
        (_root_.MIPStarRE.QPBT.idealState P w.aux)‖ ^ 2) ≤
    2 * (∑ u : _root_.MIPStarRE.QPBT.PauliRegister P,
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB ((M.postprocess _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect u) -
          _root_.MIPStarRE.QPBT.pauliProjOnB'' P W u) (_root_.MIPStarRE.QPBT.idealState P w.aux)‖ ^ 2) +
      4 * δ ^ 2 + 4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε
  calc
    (∑ u : _root_.MIPStarRE.QPBT.PauliRegister P,
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB (M.effect (.pauliOutcome u)) -
            _root_.MIPStarRE.QPBT.pauliProjOnB'' P W u) (_root_.MIPStarRE.QPBT.idealState P w.aux)‖ ^ 2) ≤
        ∑ u : _root_.MIPStarRE.QPBT.PauliRegister P,
          (2 * ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB
                ((M.postprocess _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect u) -
              _root_.MIPStarRE.QPBT.pauliProjOnB'' P W u) (_root_.MIPStarRE.QPBT.idealState P w.aux)‖ ^ 2 +
            if u = 0 then 2 * bad else 0) :=
      Finset.sum_le_sum fun u _ => hpoint u
    _ = 2 * (∑ u : _root_.MIPStarRE.QPBT.PauliRegister P,
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB
                ((M.postprocess _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect u) -
              _root_.MIPStarRE.QPBT.pauliProjOnB'' P W u) (_root_.MIPStarRE.QPBT.idealState P w.aux)‖ ^ 2) + 2 * bad := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ 2 * (∑ u : _root_.MIPStarRE.QPBT.PauliRegister P,
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (_root_.MIPStarRE.QPBT.liftedBEffect S w.φB
                ((M.postprocess _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect u) -
              _root_.MIPStarRE.QPBT.pauliProjOnB'' P W u) (_root_.MIPStarRE.QPBT.idealState P w.aux)‖ ^ 2) +
          2 * (2 * δ ^ 2 + 2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε) := by
      linarith
    _ = _ := by
      ring
