-- Prove2me | solution 1 for MIPStarRE.QPBT.pauli_naimark_operator_distanceA_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:41:35.617229+00:00
-- url     : https://prove2.me/submissions/51329249-c70e-4aec-ac71-1b5b9d8e20ed

-- Generated proof for MIPStarRE.QPBT.pauli_naimark_operator_distanceA_le.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Games_MeasurementCompression
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Definitions.Def_QPBT_QPBT_Test_Soundness_NaimarkOperatorTransfer
import Definitions.Def_QPBT_QPBT_Test_Soundness_NaimarkReduction
import Definitions.Def_QPBT_QPBT_Upstream
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_isometryMatrix_conjTranspose_mul

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace LIDT.MIPStarRE.Quantum.Measurement
end LIDT.MIPStarRE.Quantum.Measurement
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.Measurement
end MIPStarRE.QPBT.Measurement

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

/-- The squared norm of `M ψ` is the quadratic form of `Mᴴ M`. -/
private theorem norm_applyOperatorToState_sq_eq {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState M ψ‖ ^ 2 =
      (inner ℂ ψ (_root_.MIPStarRE.QPBT.applyOperatorToState (Mᴴ * M) ψ)).re := by
  rw [@norm_sq_eq_re_inner ℂ]
  unfold _root_.MIPStarRE.QPBT.applyOperatorToState
  rw [_root_.LIDT.Matrix.toEuclideanLin_conjTranspose_mul_self]
  change (inner ℂ (Matrix.toEuclideanLin M ψ) (Matrix.toEuclideanLin M ψ)).re =
    (inner ℂ ψ ((Matrix.toEuclideanLin M).adjoint (Matrix.toEuclideanLin M ψ))).re
  rw [LinearMap.adjoint_inner_right]





/-- Finite-subset form of contraction by square-summable left multipliers. -/
private theorem finset_sum_norm_mul_apply_le {γ ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (s : Finset γ) (C : γ → _root_.LIDT.MIPStarRE.Quantum.Op ι) (D : _root_.LIDT.MIPStarRE.Quantum.Op ι) (v : EuclideanSpace ℂ ι)
    (hC : ∑ c ∈ s, (C c)ᴴ * C c ≤ 1) :
    ∑ c ∈ s, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (C c * D) v‖ ^ 2 ≤
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState D v‖ ^ 2 := by
  calc
    ∑ c ∈ s, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (C c * D) v‖ ^ 2 =
        ∑ c ∈ s,
          (inner ℂ (_root_.MIPStarRE.QPBT.applyOperatorToState D v)
            (_root_.MIPStarRE.QPBT.applyOperatorToState ((C c)ᴴ * C c)
              (_root_.MIPStarRE.QPBT.applyOperatorToState D v))).re := by
          apply Finset.sum_congr rfl
          intro c _
          rw [_root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
          exact norm_applyOperatorToState_sq_eq (C c) _
    _ = (inner ℂ (_root_.MIPStarRE.QPBT.applyOperatorToState D v)
          (_root_.MIPStarRE.QPBT.applyOperatorToState (∑ c ∈ s, (C c)ᴴ * C c)
            (_root_.MIPStarRE.QPBT.applyOperatorToState D v))).re := by
          simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
    _ ≤ (inner ℂ (_root_.MIPStarRE.QPBT.applyOperatorToState D v)
          (_root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (_root_.MIPStarRE.QPBT.applyOperatorToState D v))).re :=
      _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hC _
    _ = ‖_root_.MIPStarRE.QPBT.applyOperatorToState D v‖ ^ 2 := by
      simpa [_root_.MIPStarRE.QPBT.applyOperatorToState] using
        (norm_applyOperatorToState_sq_eq (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (_root_.MIPStarRE.QPBT.applyOperatorToState D v)).symm

/-- Formalization-only auxiliary lemma for Fact 4.20: a square-summable family
of left multipliers contracts total squared norm. -/
theorem sum_norm_mul_apply_le {γ ι : Type*}
    [Fintype γ] [Fintype ι] [DecidableEq ι]
    (C : γ → _root_.LIDT.MIPStarRE.Quantum.Op ι) (D : _root_.LIDT.MIPStarRE.Quantum.Op ι) (v : EuclideanSpace ℂ ι)
    (hC : ∑ c : γ, (C c)ᴴ * C c ≤ 1) :
    ∑ c : γ, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (C c * D) v‖ ^ 2 ≤
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState D v‖ ^ 2 := by
  simpa using finset_sum_norm_mul_apply_le Finset.univ C D v (by simpa using hC)































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

/- Source helpers from QPBT/Games/MeasurementCompression.lean. -/
/-!
# Ground-slice compression of measurements

This module restricts a POVM on a product space to one distinguished ancillary
coordinate. It also records that this restriction commutes with deterministic
outcome postprocessing, recovers a POVM from its one-measurement Naimark
dilation, and preserves consistency defects evaluated on the correspondingly
padded bipartite state.

The construction supports the pullback after the first paragraph of the proof
of paper `lem:qld-4-7`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1289`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace LIDT
namespace MIPStarRE.Quantum.Measurement





/-- Restricting a POVM to a fixed ancillary coordinate commutes with
deterministic relabeling of its outcomes. -/
theorem compressAt_postprocess
    {A B I κ : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] [Fintype κ] [DecidableEq κ]
    (k₀ : κ) (M : _root_.LIDT.MIPStarRE.Quantum.Measurement A (I × κ)) (f : A → B) :
    (M.postprocess f).compressAt k₀ = (M.compressAt k₀).postprocess f := by
  classical
  apply _root_.LIDT.MIPStarRE.Quantum.Measurement.ext
  intro b
  ext i j
  simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.compressAt_effect, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
    Matrix.submatrix_apply, Matrix.sum_apply]

end MIPStarRE.Quantum.Measurement
end LIDT

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

namespace Measurement

/-- Compressing the completed one-measurement Naimark dilation at its
distinguished `none` coordinate recovers the original POVM. -/
theorem compressAt_dilatedMeasurement
    {A I : Type} [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I]
    (a₀ : A) (M : _root_.LIDT.MIPStarRE.Quantum.Measurement A I) :
    (_root_.MIPStarRE.QPBT.dilatedMeasurement a₀ M).compressAt none = M := by
  apply _root_.LIDT.MIPStarRE.Quantum.Measurement.ext
  intro a
  ext i j
  exact _root_.MIPStarRE.QPBT.dilatedMeasurement_compression a₀ a M i j

end Measurement



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

/- Source helpers from QPBT/Games/DistanceTheorems.lean. -/
/-! # State-dependent distance calculus

This module records the consistency and state-dependent distance estimates used
throughout the quantum Pauli basis test. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

The operator-level inequalities they rest on live in
`MIPStarRE.QPBT.Games.DistanceTheorems.Calculus`.

## References

The source results run from blueprint `fact:agreement` through
`lem:close-strategies-have-close-values`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-461` and
`:531-540`. The observable conversion lemmas come from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:95-131`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus











/-- The squared effects of a POVM sum to at most the identity. This is the
formalization-only estimate `lem:sandwich-povm-square-sum` used in the
contractions underlying `lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem measurement_sum_adjoint_mul_le_one
    {α I : Type*} [Fintype α] [Fintype I] [DecidableEq I]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α I) :
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ 1 := by
  calc
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ ∑ a : α, M.effect a := by
      apply Finset.sum_le_sum
      intro a _
      rw [_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
      exact _root_.LIDT.MIPStarRE.Quantum.sq_le_self (M.pos a) (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one M a)
    _ = 1 := M.sum_eq_one























end MIPStarRE.QPBT

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





/-- Operators act additively on differences of states. -/
theorem applyOperatorToState_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) (u v : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState M (u - v) =
      _root_.MIPStarRE.QPBT.applyOperatorToState M u - _root_.MIPStarRE.QPBT.applyOperatorToState M v := by
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState]





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



/-- Orthogonal projections are contractions. -/
theorem conjTranspose_mul_le_one_of_isProj {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hP : _root_.LIDT.MIPStarRE.Quantum.IsProj P) : Pᴴ * P ≤ 1 := by
  have hstar : Pᴴ = P := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hP.isSelfAdjoint.star_eq
  rw [hstar, hP.isIdempotentElem.eq]
  exact sub_nonneg.mp hP.one_sub.nonneg











/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/









/-! ## Matrices of isometries -/



/-- The range projection `V Vᴴ` of a matrix isometry is at most the identity. -/
theorem isometryMatrix_mul_conjTranspose_le_one {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι']
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι') :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ ≤ 1 := by
  have hproj : _root_.LIDT.MIPStarRE.Quantum.IsProj (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ) := by
    constructor
    · change (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ) *
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ) = _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ,
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_conjTranspose_mul, Matrix.one_mul]
    · change star (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ) =
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul]
  exact sub_nonneg.mp hproj.one_sub.nonneg



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





/-- A left-placed conjugated operator acts on the transported state as the
left-placed original operator acts on the original state. -/
theorem applyOperatorToState_leftTensor_conjIsometry {ιA ιB κA κB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (X : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry φA X) 1) (_root_.MIPStarRE.QPBT.isometryTensor φA φB ψ) =
      _root_.MIPStarRE.QPBT.isometryTensor φA φB (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron X 1) ψ) := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_eq_toEuclideanLin, _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_eq_toEuclideanLin]
  unfold _root_.MIPStarRE.QPBT.applyOperatorToState
  rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.toEuclideanLin_mul_apply, ← _root_.MIPStarRE.QPBT.MagicSquareRigidity.toEuclideanLin_mul_apply]
  refine congrArg (fun M => Matrix.toEuclideanLin M ψ) ?_
  unfold _root_.MIPStarRE.QPBT.heteroKron Matrix.kronecker
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_eq, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_assoc, _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_conjTranspose_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one]



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

/- Source helpers from QPBT/Test/Soundness/NaimarkReduction.lean. -/
/-!
# Naimark reduction for Pauli-test strategies

An arbitrary Pauli-test strategy is dilated questionwise to a projective
strategy on two separately enlarged local spaces. The ground-slice embeddings
are fixed across questions. Compression recovers both original POVM families,
including the complete Pauli-answer postprocessing. Composing any isometry
witness on the dilation with the embeddings returns its state comparison to
the original spaces. Operator-family distance transfer is not asserted here.

## References

Paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`
(`thm:pauli`) and
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190,1862-1876`.
Blueprint `thm:pauli-naimark-reduction-support`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MagicSquareRigidity

noncomputable section











/-- The padded state is precisely the tensor image under the two fixed ground
embeddings; there is no identification of Alice's and Bob's local spaces. -/
theorem pauliNaimarkStrategy_state (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P)) :
    (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).ψ =
      _root_.MIPStarRE.QPBT.isometryTensor (_root_.MIPStarRE.QPBT.pauliNaimarkEmbeddingA P S) (_root_.MIPStarRE.QPBT.pauliNaimarkEmbeddingB P S) S.ψ := by
  change _root_.MIPStarRE.QPBT.padState none none S.ψ = _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState (_root_.MIPStarRE.QPBT.PauliAnswer P) S.ψ
  ext p
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState_apply]
  simp only [_root_.MIPStarRE.QPBT.padState, EuclideanSpace.equiv]
  by_cases hA : p.1.2 = none <;> by_cases hB : p.2.2 = none <;> simp [hA, hB]







/-- Compression commutes with the complete `pauliAnswerOrZero` postprocessing
of Alice's Pauli-question measurement, including wrong-form outcomes. -/
theorem pauliNaimarkStrategy_pauli_compressA (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P)) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    (((_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).A (_root_.MIPStarRE.QPBT.pauliQuestion P W)).postprocess
      _root_.MIPStarRE.QPBT.pauliAnswerOrZero).compressAt none =
        (S.A (_root_.MIPStarRE.QPBT.pauliQuestion P W)).postprocess _root_.MIPStarRE.QPBT.pauliAnswerOrZero := by
  change ((_root_.MIPStarRE.QPBT.dilatedMeasurement (default : _root_.MIPStarRE.QPBT.PauliAnswer P)
      (S.A (_root_.MIPStarRE.QPBT.pauliQuestion P W))).postprocess _root_.MIPStarRE.QPBT.pauliAnswerOrZero).compressAt none = _
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.compressAt_postprocess,
    _root_.MIPStarRE.QPBT.Measurement.compressAt_dilatedMeasurement]









end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Soundness/NaimarkOperatorTransfer.lean. -/
/-!
# Pauli operator transfer through Naimark compression

The questionwise Naimark dilation preserves the complete Pauli readout only
after ground-slice compression.  This module proves the corresponding
state-dependent transfer for both players.  The range projection is retained
on both sides of every dilated effect, and the opposite ideal Pauli family is
used on the EPR state to control the second range defect.

## References

This is a formalization-only support result for `thm:pauli`, whose source
statement is at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The projective reduction and the final isometry passage are at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190,1862-1876`.
The omitted range-projection calculation is documented in
`docs/paper-gaps/qpbt_extraction-transfer.tex` and issue Dengnifer/MIPStarRE-QPBT-bak#604.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MagicSquareRigidity DistanceCalculus

noncomputable section

private theorem liftedAEffect_eq_tensor {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φ : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × _root_.MIPStarRE.QPBT.PauliRegister P)) (M : _root_.LIDT.MIPStarRE.Quantum.Op S.ιA) :
    _root_.MIPStarRE.QPBT.liftedAEffect S (ιB' := ιB') φ M = _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.conjIsometry φ M) 1 := by
  ext i j
  simp [_root_.MIPStarRE.QPBT.liftedAEffect, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.one_apply]



private theorem naimark_isProj_conjIsometry {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    {Q : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hQ : _root_.LIDT.MIPStarRE.Quantum.IsProj Q) : _root_.LIDT.MIPStarRE.Quantum.IsProj (_root_.MIPStarRE.QPBT.conjIsometry φ Q) := by
  constructor
  · change _root_.MIPStarRE.QPBT.conjIsometry φ Q * _root_.MIPStarRE.QPBT.conjIsometry φ Q = _root_.MIPStarRE.QPBT.conjIsometry φ Q
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_mul, hQ.isIdempotentElem.eq]
  · change star (_root_.MIPStarRE.QPBT.conjIsometry φ Q) = _root_.MIPStarRE.QPBT.conjIsometry φ Q
    simp [_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_eq, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      hQ.isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc]

private theorem naimark_left_isProj {ι κ : Type} [Fintype ι]
    [Fintype κ] [DecidableEq κ] {Q : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hQ : _root_.LIDT.MIPStarRE.Quantum.IsProj Q) :
    _root_.LIDT.MIPStarRE.Quantum.IsProj (_root_.MIPStarRE.QPBT.heteroKron Q (1 : _root_.LIDT.MIPStarRE.Quantum.Op κ)) := by
  classical
  constructor
  · change _root_.MIPStarRE.QPBT.heteroKron Q 1 * _root_.MIPStarRE.QPBT.heteroKron Q 1 = _root_.MIPStarRE.QPBT.heteroKron Q 1
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, hQ.isIdempotentElem.eq, Matrix.one_mul]
  · change star (_root_.MIPStarRE.QPBT.heteroKron Q (1 : _root_.LIDT.MIPStarRE.Quantum.Op κ)) = _root_.MIPStarRE.QPBT.heteroKron Q 1
    simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      hQ.isSelfAdjoint.isHermitian.eq]



private theorem naimark_left_sum_adjoint_mul_le_one {α ι κ : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : α → _root_.LIDT.MIPStarRE.Quantum.Op ι) (hN : ∑ a, (N a)ᴴ * N a ≤ 1) :
    ∑ a, (_root_.MIPStarRE.QPBT.heteroKron (N a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op κ))ᴴ * _root_.MIPStarRE.QPBT.heteroKron (N a) 1 ≤ 1 := by
  change ∑ a, (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := κ) (N a))ᴴ *
    _root_.LIDT.MIPStarRE.LDT.leftTensor (N a) ≤ 1
  have h := _root_.LIDT.MIPStarRE.LDT.leftTensor_mono (ι₂ := κ) hN
  simpa only [← _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum,
    _root_.LIDT.MIPStarRE.LDT.leftTensor_one, _root_.LIDT.MIPStarRE.LDT.leftTensor_conjTranspose,
    _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor] using h



private theorem naimark_sum_conjIsometry_adjoint_mul_le_one {α ι κ : Type}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (N : α → _root_.LIDT.MIPStarRE.Quantum.Op ι) (hN : ∑ a, (N a)ᴴ * N a ≤ 1) :
    ∑ a, (_root_.MIPStarRE.QPBT.conjIsometry φ (N a))ᴴ * _root_.MIPStarRE.QPBT.conjIsometry φ (N a) ≤ 1 := by
  have heq (a : α) : (_root_.MIPStarRE.QPBT.conjIsometry φ (N a))ᴴ * _root_.MIPStarRE.QPBT.conjIsometry φ (N a) =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * ((N a)ᴴ * N a) * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ := by
    simp only [_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_eq, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ),
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_conjTranspose_mul, Matrix.one_mul]
  simp_rw [heq]
  have hsum : (∑ a, _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * ((N a)ᴴ * N a) *
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ) =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (∑ a, (N a)ᴴ * N a) * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
  rw [hsum]
  calc
    _ ≤ _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ * (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) * (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)ᴴ := by
      rw [Matrix.le_iff]
      convert (Matrix.le_iff.mp hN).mul_mul_conjTranspose_same (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φ)
        using 1; simp [Matrix.mul_sub, Matrix.sub_mul]
    _ ≤ 1 := by
      rw [Matrix.mul_one]
      exact _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_mul_conjTranspose_le_one φ

private theorem liftedA_sum_adjoint_mul_le_one {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {G : _root_.MIPStarRE.QPBT.Game}
    {α : Type} [Fintype α] (S : _root_.MIPStarRE.QPBT.Strategy G)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φ : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × _root_.MIPStarRE.QPBT.PauliRegister P))
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α S.ιA) :
    ∑ a, (_root_.MIPStarRE.QPBT.liftedAEffect S (ιB' := ιB') φ (M.effect a))ᴴ *
      _root_.MIPStarRE.QPBT.liftedAEffect S φ (M.effect a) ≤ 1 := by
  classical
  simp only [liftedAEffect_eq_tensor]
  exact naimark_left_sum_adjoint_mul_le_one _
    (naimark_sum_conjIsometry_adjoint_mul_le_one φ M.effect
      (_root_.MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one M))



private theorem naimark_norm_add_three_sq_le {ι : Type*} [Fintype ι]
    (x y z : EuclideanSpace ℂ ι) :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (show ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ from norm_add₃_le) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x‖ - ‖z‖),
    sq_nonneg (‖y‖ - ‖z‖)]

private theorem naimark_apply_sub_operator {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A B : _root_.LIDT.MIPStarRE.Quantum.Op ι) (v : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (A - B) v =
      _root_.MIPStarRE.QPBT.applyOperatorToState A v - _root_.MIPStarRE.QPBT.applyOperatorToState B v := by
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState]

private theorem sum_norm_compression_sub_sq_le {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (N T R : α → _root_.LIDT.MIPStarRE.Quantum.Op ι) (Q : _root_.LIDT.MIPStarRE.Quantum.Op ι) (hQ : _root_.LIDT.MIPStarRE.Quantum.IsProj Q)
    (hN : ∑ a, (N a)ᴴ * N a ≤ 1) (hR : ∑ a, (R a)ᴴ * R a ≤ 1)
    (theta delta : EuclideanSpace ℂ ι)
    (hfix : _root_.MIPStarRE.QPBT.applyOperatorToState Q theta = theta)
    (hmirror : ∀ a, _root_.MIPStarRE.QPBT.applyOperatorToState (T a) delta =
      _root_.MIPStarRE.QPBT.applyOperatorToState (R a) delta)
    (hcomm : ∀ a, Q * R a = R a * Q) :
    ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (Q * N a * Q - T a) delta‖ ^ 2 ≤
      3 * (∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (N a - T a) delta‖ ^ 2) +
        6 * ‖delta - theta‖ ^ 2 := by
  have hcontract (v : EuclideanSpace ℂ ι) :
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState Q v‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _)
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_le (_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_of_isProj hQ) v) 2
  have hvanish : _root_.MIPStarRE.QPBT.applyOperatorToState (1 - Q) theta = 0 := by
    simp [_root_.MIPStarRE.QPBT.applyOperatorToState, show Matrix.toEuclideanLin Q theta = theta from hfix]
  have hrange : ‖_root_.MIPStarRE.QPBT.applyOperatorToState (1 - Q) delta‖ ^ 2 ≤
      ‖delta - theta‖ ^ 2 := by
    have h := _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_le
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjTranspose_mul_le_one_of_isProj hQ.one_sub) (delta - theta)
    rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_sub, hvanish, sub_zero] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hn := (_root_.MIPStarRE.QPBT.DistanceCalculus.sum_norm_mul_apply_le N (1 - Q) delta hN).trans hrange
  have hr := (_root_.MIPStarRE.QPBT.DistanceCalculus.sum_norm_mul_apply_le R (1 - Q) delta hR).trans hrange
  have hpoint (a : α) :
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (Q * N a * Q - T a) delta‖ ^ 2 ≤
        3 * (‖_root_.MIPStarRE.QPBT.applyOperatorToState (N a - T a) delta‖ ^ 2 +
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState (N a * (1 - Q)) delta‖ ^ 2 +
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState (R a * (1 - Q)) delta‖ ^ 2) := by
    have hs : Q * N a * Q - T a =
        Q * (N a - T a) - Q * (N a * (1 - Q)) - (1 - Q) * T a := by
      noncomm_ring
    have hm : _root_.MIPStarRE.QPBT.applyOperatorToState ((1 - Q) * T a) delta =
        _root_.MIPStarRE.QPBT.applyOperatorToState (R a * (1 - Q)) delta := by
      rw [_root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, hmirror]
      rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
      congr 1
      rw [sub_mul, mul_sub, one_mul, mul_one, hcomm]
    rw [hs, naimark_apply_sub_operator, naimark_apply_sub_operator]
    rw [hm, _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul,
      sub_eq_add_neg, sub_eq_add_neg]
    have h := naimark_norm_add_three_sq_le
      (_root_.MIPStarRE.QPBT.applyOperatorToState Q (_root_.MIPStarRE.QPBT.applyOperatorToState (N a - T a) delta))
      (-_root_.MIPStarRE.QPBT.applyOperatorToState Q (_root_.MIPStarRE.QPBT.applyOperatorToState (N a * (1 - Q)) delta))
      (-_root_.MIPStarRE.QPBT.applyOperatorToState (R a * (1 - Q)) delta)
    simp only [norm_neg] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (hcontract _) (hcontract _)) le_rfl) (by norm_num))
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpoint a)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  nlinarith



private theorem pauliProjOnA_eq_tensor (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : _root_.MIPStarRE.QPBT.PauliKind) (h : _root_.MIPStarRE.QPBT.PauliRegister P) :
    _root_.MIPStarRE.QPBT.pauliProjOnA'' P (ιA' := ιA') (ιB' := ιB') W h =
      _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.pauliProj W h)) 1 := by
  ext i j
  simp [_root_.MIPStarRE.QPBT.pauliProjOnA'', _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.one_apply, ite_and]
  split_ifs <;> simp_all

private theorem pauliProjOnB_eq_tensor (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : _root_.MIPStarRE.QPBT.PauliKind) (h : _root_.MIPStarRE.QPBT.PauliRegister P) :
    _root_.MIPStarRE.QPBT.pauliProjOnB'' P (ιA' := ιA') (ιB' := ιB') W h =
      _root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.pauliProj W h)) := by
  ext i j
  simp [_root_.MIPStarRE.QPBT.pauliProjOnB'', _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.one_apply, ite_and]
  split_ifs <;> simp_all

private theorem idealState_transpose (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (aux : EuclideanSpace ℂ (ιA' × ιB')) (M : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron 1 M) 1) (_root_.MIPStarRE.QPBT.idealState P aux) =
      _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.heteroKron 1 Mᵀ)) (_root_.MIPStarRE.QPBT.idealState P aux) := by
  ext p
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.one_apply,
    _root_.MIPStarRE.QPBT.idealState, _root_.MIPStarRE.QPBT.eprState, Fintype.sum_prod_type, mul_comm]

private theorem idealState_pauli_mirror (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (aux : EuclideanSpace ℂ (ιA' × ιB')) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (h : _root_.MIPStarRE.QPBT.PauliRegister P) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.pauliProjOnA'' P W h) (_root_.MIPStarRE.QPBT.idealState P aux) =
      _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.pauliProjOnB'' P W h) (_root_.MIPStarRE.QPBT.idealState P aux) := by
  rw [pauliProjOnA_eq_tensor, pauliProjOnB_eq_tensor]
  simpa only [_root_.MIPStarRE.QPBT.pauliProj_transpose] using idealState_transpose P aux (_root_.MIPStarRE.QPBT.pauliProj W h)



private theorem pauliProjOnB_sum_adjoint_mul_le_one (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : _root_.MIPStarRE.QPBT.PauliKind) :
    ∑ h, (_root_.MIPStarRE.QPBT.pauliProjOnB'' P (ιA' := ιA') (ιB' := ιB') W h)ᴴ *
      _root_.MIPStarRE.QPBT.pauliProjOnB'' P W h ≤ 1 := by
  simp only [pauliProjOnB_eq_tensor]
  exact _root_.MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
    (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (idealPauliMeasurement P W)))

private theorem naimark_compressed_effect {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P)) (W : _root_.MIPStarRE.QPBT.PauliKind) (h : _root_.MIPStarRE.QPBT.PauliRegister P) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression
        ((((_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).A (_root_.MIPStarRE.QPBT.pauliQuestion P W)).postprocess
          _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect h) =
      (((S.A (_root_.MIPStarRE.QPBT.pauliQuestion P W)).postprocess _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect h) := by
  have heff := congrArg (fun M => M.effect h)
    (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy_pauli_compressA P S W)
  change _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression
      ((((_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).A (_root_.MIPStarRE.QPBT.pauliQuestion P W)).postprocess
        _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect h) = _
  exact heff



private theorem naimark_conjIsometry_compressed {ι α κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ (ι × Option α) →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (N : _root_.LIDT.MIPStarRE.Quantum.Op (ι × Option α)) :
    _root_.MIPStarRE.QPBT.conjIsometry (φ.comp (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkEmbedding ι α)) (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression N) =
      _root_.MIPStarRE.QPBT.conjIsometry φ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ι α) * _root_.MIPStarRE.QPBT.conjIsometry φ N *
        _root_.MIPStarRE.QPBT.conjIsometry φ (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection ι α) := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_comp_naimarkEmbedding, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_naimarkCompression,
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_mul, _root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_mul]

private theorem naimark_lifted_compression_alice
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P))
    (w : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S)) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (h : _root_.MIPStarRE.QPBT.PauliRegister P) :
    _root_.MIPStarRE.QPBT.liftedAEffect S (ιB' := w.ιB') (_root_.MIPStarRE.QPBT.pauliNaimarkWitness P S w).φA
        (((S.A (_root_.MIPStarRE.QPBT.pauliQuestion P W)).postprocess _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect h) =
      _root_.MIPStarRE.QPBT.liftedAEffect (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S) (ιB' := w.ιB') w.φA
          (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA (_root_.MIPStarRE.QPBT.PauliAnswer P)) *
        _root_.MIPStarRE.QPBT.liftedAEffect (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S) (ιB' := w.ιB') w.φA
          ((((_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).A (_root_.MIPStarRE.QPBT.pauliQuestion P W)).postprocess
            _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect h) *
        _root_.MIPStarRE.QPBT.liftedAEffect (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S) (ιB' := w.ιB') w.φA
          (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA (_root_.MIPStarRE.QPBT.PauliAnswer P)) := by
  have hc0 := naimark_conjIsometry_compressed w.φA
    ((((_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).A (_root_.MIPStarRE.QPBT.pauliQuestion P W)).postprocess
      _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect h)
  have hc' :
      _root_.MIPStarRE.QPBT.conjIsometry (w.φA.comp (_root_.MIPStarRE.QPBT.pauliNaimarkEmbeddingA P S))
          (((S.A (_root_.MIPStarRE.QPBT.pauliQuestion P W)).postprocess _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect h) =
        _root_.MIPStarRE.QPBT.conjIsometry w.φA (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA (_root_.MIPStarRE.QPBT.PauliAnswer P)) *
          _root_.MIPStarRE.QPBT.conjIsometry w.φA
            ((((_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).A (_root_.MIPStarRE.QPBT.pauliQuestion P W)).postprocess
              _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect h) *
          _root_.MIPStarRE.QPBT.conjIsometry w.φA (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA (_root_.MIPStarRE.QPBT.PauliAnswer P)) := by
    calc
      _ = _root_.MIPStarRE.QPBT.conjIsometry (w.φA.comp (_root_.MIPStarRE.QPBT.pauliNaimarkEmbeddingA P S))
          (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkCompression
            ((((_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).A (_root_.MIPStarRE.QPBT.pauliQuestion P W)).postprocess
              _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect h)) := by
            rw [naimark_compressed_effect S W h]
      _ = _ := hc0
  have hc := hc'
  have hh := congrArg (fun M => _root_.MIPStarRE.QPBT.heteroKron M (1 : _root_.LIDT.MIPStarRE.Quantum.Op (w.ιB' × _root_.MIPStarRE.QPBT.PauliRegister P))) hc
  calc
    _ = _root_.MIPStarRE.QPBT.heteroKron
        (_root_.MIPStarRE.QPBT.conjIsometry (_root_.MIPStarRE.QPBT.pauliNaimarkWitness P S w).φA
          (((S.A (_root_.MIPStarRE.QPBT.pauliQuestion P W)).postprocess _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect h))
        (1 : _root_.LIDT.MIPStarRE.Quantum.Op ((_root_.MIPStarRE.QPBT.pauliNaimarkWitness P S w).ιB' × _root_.MIPStarRE.QPBT.PauliRegister P)) := by
          apply liftedAEffect_eq_tensor
    _ = _ := by
      simp only [_root_.MIPStarRE.QPBT.pauliNaimarkWitness, _root_.MIPStarRE.QPBT.pauliNaimarkEmbeddingA,
        liftedAEffect_eq_tensor, _root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.one_mul]
      convert hh using 1
      simp [_root_.MIPStarRE.QPBT.pauliNaimarkEmbeddingA]







end

end MIPStarRE.QPBT

/-!
# Pauli operator transfer through Naimark compression

The questionwise Naimark dilation preserves the complete Pauli readout only
after ground-slice compression.  This module proves the corresponding
state-dependent transfer for both players.  The range projection is retained
on both sides of every dilated effect, and the opposite ideal Pauli family is
used on the EPR state to control the second range defect.

## References

This is a formalization-only support result for `thm:pauli`, whose source
statement is at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The projective reduction and the final isometry passage are at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190,1862-1876`.
The omitted range-projection calculation is documented in
`docs/paper-gaps/qpbt_extraction-transfer.tex` and issue Dengnifer/MIPStarRE-QPBT-bak#604.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.MagicSquareRigidity MIPStarRE.QPBT.DistanceCalculus

set_option maxHeartbeats 800000 in
-- Finite-register matrix algebra and nested finite sums make this proof
-- expensive to elaborate.

theorem solution
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P))
    (w : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S)) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.pauliOperatorDistanceA P S (_root_.MIPStarRE.QPBT.pauliNaimarkWitness P S w) W ≤
      3 * _root_.MIPStarRE.QPBT.pauliOperatorDistanceA P (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S) w W +
        6 * ‖_root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).ψ -
          _root_.MIPStarRE.QPBT.idealState P w.aux‖ ^ 2 := by
  let Q := _root_.MIPStarRE.QPBT.liftedAEffect (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S) (ιB' := w.ιB') w.φA
    (_root_.MIPStarRE.QPBT.MagicSquareRigidity.groundProjection S.ιA (_root_.MIPStarRE.QPBT.PauliAnswer P))
  have hQ : _root_.LIDT.MIPStarRE.Quantum.IsProj Q := by
    dsimp only [Q]
    rw [liftedAEffect_eq_tensor]
    exact naimark_left_isProj (naimark_isProj_conjIsometry w.φA
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isProj_groundProjection S.ιA (_root_.MIPStarRE.QPBT.PauliAnswer P)))
  have hfix : _root_.MIPStarRE.QPBT.applyOperatorToState Q
      (_root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).ψ) =
        _root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).ψ := by
    dsimp only [Q]
    rw [liftedAEffect_eq_tensor, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_leftTensor_conjIsometry]
    have hp : _root_.MIPStarRE.QPBT.padState (none : Option (_root_.MIPStarRE.QPBT.PauliAnswer P))
        (none : Option (_root_.MIPStarRE.QPBT.PauliAnswer P)) S.ψ =
          _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState (_root_.MIPStarRE.QPBT.PauliAnswer P) S.ψ :=
      _root_.MIPStarRE.QPBT.pauliNaimarkStrategy_state P S
    rw [hp]
    erw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_leftTensor_groundProjection (_root_.MIPStarRE.QPBT.PauliAnswer P) S.ψ]
  have hcomm (h : _root_.MIPStarRE.QPBT.PauliRegister P) : Q * _root_.MIPStarRE.QPBT.pauliProjOnB'' P W h =
      _root_.MIPStarRE.QPBT.pauliProjOnB'' P W h * Q := by
    dsimp only [Q]
    rw [liftedAEffect_eq_tensor, pauliProjOnB_eq_tensor]
    simp only [_root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  have hb := sum_norm_compression_sub_sq_le
    (fun h => _root_.MIPStarRE.QPBT.liftedAEffect (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S) (ιB' := w.ιB') w.φA
      ((((_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).A (_root_.MIPStarRE.QPBT.pauliQuestion P W)).postprocess
        _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect h))
    (_root_.MIPStarRE.QPBT.pauliProjOnA'' P W) (_root_.MIPStarRE.QPBT.pauliProjOnB'' P W) Q hQ
    (liftedA_sum_adjoint_mul_le_one _ w.φA _)
    (pauliProjOnB_sum_adjoint_mul_le_one P W)
    (_root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).ψ)
    (_root_.MIPStarRE.QPBT.idealState P w.aux) hfix (idealState_pauli_mirror P w.aux W) hcomm
  have hb' :
      ∑ h, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (Q * _root_.MIPStarRE.QPBT.liftedAEffect (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S) (ιB' := w.ιB') w.φA
              ((((_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).A (_root_.MIPStarRE.QPBT.pauliQuestion P W)).postprocess
                _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect h) * Q - _root_.MIPStarRE.QPBT.pauliProjOnA'' P W h)
          (_root_.MIPStarRE.QPBT.idealState P w.aux)‖ ^ 2 ≤
        3 * _root_.MIPStarRE.QPBT.pauliOperatorDistanceA P (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S) w W +
          6 * ‖_root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB (_root_.MIPStarRE.QPBT.pauliNaimarkStrategy P S).ψ -
            _root_.MIPStarRE.QPBT.idealState P w.aux‖ ^ 2 := by
    simpa only [_root_.MIPStarRE.QPBT.pauliOperatorDistanceA, norm_sub_rev] using hb
  unfold _root_.MIPStarRE.QPBT.pauliOperatorDistanceA
  apply le_of_eq_of_le ?_ hb'
  apply Finset.sum_congr rfl
  intro h _
  have hcomp := naimark_lifted_compression_alice P S w W h
  dsimp only [_root_.MIPStarRE.QPBT.pauliNaimarkWitness] at hcomp ⊢
  have hsub := congrArg
    (fun M : _root_.LIDT.MIPStarRE.Quantum.Op ((w.ιA' × _root_.MIPStarRE.QPBT.PauliRegister P) × (w.ιB' × _root_.MIPStarRE.QPBT.PauliRegister P)) =>
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M - _root_.MIPStarRE.QPBT.pauliProjOnA'' P W h) (_root_.MIPStarRE.QPBT.idealState P w.aux)‖ ^ 2) hcomp
  convert hsub using 1
