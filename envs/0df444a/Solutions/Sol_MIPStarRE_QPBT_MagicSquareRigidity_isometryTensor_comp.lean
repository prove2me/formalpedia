-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_comp
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:11:49.287006+00:00
-- url     : https://prove2.me/submissions/677c74a5-5952-4b24-8df1-543e57d1a769

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_comp.
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
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
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



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective



/-! ## Orthogonality inside a subnormalized family of projections -/







/-! ## The ground slice of an enlarged local space -/



























/-! ## The dilated projective measurement -/

























/-! ## The dilated state -/













/-! ## The dilated Magic Square strategy -/













/-! ## Preservation of the value-to-parity layer -/



































/-! ## Composition of the dilation with later local isometries -/

theorem solution {ιA ιB κA κB νA νB : Type}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    [Fintype νA] [DecidableEq νA] [Fintype νB] [DecidableEq νB]
    (φA : EuclideanSpace ℂ κA →ₗᵢ[ℂ] EuclideanSpace ℂ νA)
    (φB : EuclideanSpace ℂ κB →ₗᵢ[ℂ] EuclideanSpace ℂ νB)
    (EA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (EB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.isometryTensor (φA.comp EA) (φB.comp EB) ψ =
      _root_.MIPStarRE.QPBT.isometryTensor φA φB (_root_.MIPStarRE.QPBT.isometryTensor EA EB ψ) := by
  ext p
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_apply_eq, _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_apply_eq]
  simp only [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_apply_eq, _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_comp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hk : (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φA * _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix EA).kronecker
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φB * _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix EB) =
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φA).kronecker (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix φB) *
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix EA).kronecker (_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix EB) :=
    Matrix.mul_kronecker_mul _ _ _ _
  rw [hk, Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring
