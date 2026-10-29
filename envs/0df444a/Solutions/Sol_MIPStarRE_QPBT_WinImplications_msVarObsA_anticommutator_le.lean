-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.msVarObsA_anticommutator_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:58:14.39453+00:00
-- url     : https://prove2.me/submissions/e126bad6-f2fd-44a1-a85e-1f07ebbab885

-- Generated proof for MIPStarRE.QPBT.WinImplications.msVarObsA_anticommutator_le.
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
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Basic
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_CellRelations
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Dilation
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Reflections
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Transfer
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_msVarObsA_anticommute
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_ms_anticommutator_transfer_A
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_signObs_eq_obsOf_postprocess
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_applyOperatorToState_heteroKron_naimarkInflation_one

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









/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
is additive in the left factor. -/
theorem heteroKron_add_left {ιA ιB : Type*} (A B : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (C : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron (A + B) C = _root_.MIPStarRE.QPBT.heteroKron A C + _root_.MIPStarRE.QPBT.heteroKron B C := by
  ext p q
  simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, add_mul]











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



/-- Inflation is multiplicative. -/
theorem naimarkInflation_mul {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) M * _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) N =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) (M * N) := by
  ext p q
  simp only [Matrix.mul_apply, _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_apply, Fintype.sum_prod_type,
    Fintype.sum_option]
  by_cases hp : p.2 = none <;> by_cases hq : q.2 = none <;> simp [hp, hq]

















/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





end

end MIPStarRE.QPBT.MagicSquareRigidity

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

/-- The matrix of the identity isometry is the identity matrix.
Formalization-only support for `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:266-288`. -/
theorem isometryMatrix_id {ι : Type} [Fintype ι] [DecidableEq ι] :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix
      (LinearIsometry.id (R := ℂ) (E := EuclideanSpace ℂ ι)) = 1 := by
  ext k i
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryMatrix_apply]
  simp [Matrix.one_apply, EuclideanSpace.equiv]

/-- Conjugation by the identity isometry is the identity. Formalization-only
support for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem conjIsometry_id {ι : Type} [Fintype ι] [DecidableEq ι] (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.conjIsometry (LinearIsometry.id (R := ℂ) (E := EuclideanSpace ℂ ι)) M = M := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_eq, _root_.MIPStarRE.QPBT.WinImplications.isometryMatrix_id]
  simp

/-- The two-sided identity isometry fixes every bipartite state.
Formalization-only support for `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:266-288`. -/
theorem isometryTensor_id {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.isometryTensor (LinearIsometry.id (R := ℂ) (E := EuclideanSpace ℂ ιA))
      (LinearIsometry.id (R := ℂ) (E := EuclideanSpace ℂ ιB)) ψ = ψ := by
  ext p
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_apply_eq, _root_.MIPStarRE.QPBT.WinImplications.isometryMatrix_id,
    _root_.MIPStarRE.QPBT.WinImplications.isometryMatrix_id]
  rw [show Matrix.kronecker (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB) = 1 from
    Matrix.one_kronecker_one]
  simp [Matrix.one_apply]

/-- Inflation to the ground slice is additive. Formalization-only support for
`thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem naimarkInflation_add {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) M +
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) N =
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) (M + N) := by
  ext p q
  by_cases h : p.2 = none ∧ q.2 = none <;> simp [h]





/-! ## The Magic Square anticommutation on the undilated strategy -/







/-- The state-dependent norm of an operator inflated on the first factor,
measured on the dilated state, is the norm of the original operator on the
original state. Formalization-only support for `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:266-288`. -/
theorem norm_heteroKron_naimarkInflation_one
    (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := α) M)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιB × Option α)))
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState α ψ)‖ =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron M (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB)) ψ‖ := by
  rw [_root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_heteroKron_naimarkInflation_one,
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState_norm]

/-- Alice's Magic Square variable reflections are the placed observables of her
totalized variable measurements on the dilated strategy. Formalization-only
support for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem msVarObsA_eq (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (j : Fin 9) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsA S j =
      _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var j))
        (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ιB × Option _root_.MIPStarRE.QPBT.MsAnswer)) := by
  rw [_root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsA,
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.signObs_eq_obsOf_postprocess]
  rfl



/-! ## Reflections and the product transfer -/











/-! ## From the Magic Square variables to the point observables -/









/-! ## The anticommuting half of the twisted commutation -/





















end WinImplications

end

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







/-- The one-outcome distance under the one-point uniform distribution. -/
theorem opDistSq_uniform_unit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Unit → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit) M N ψ =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M () - N ()) ψ‖ ^ 2 := by
  rw [_root_.MIPStarRE.QPBT.opDistSq_eq_opFamilyDistSq, _root_.MIPStarRE.QPBT.MagicSquareRigidity.opFamilyDistSq_uniform_unit]
  simp

























end

end MIPStarRE.QPBT.MagicSquareRigidity

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



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/

theorem solution (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (ε : ℝ) (hε : 0 ≤ ε)
    (hwin : 1 - ε ≤ S.value) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron
          (_root_.MIPStarRE.QPBT.obsOf ((S.A (.var 0)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero) *
              _root_.MIPStarRE.QPBT.obsOf ((S.A (.var 4)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero) +
            _root_.MIPStarRE.QPBT.obsOf ((S.A (.var 4)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero) *
              _root_.MIPStarRE.QPBT.obsOf ((S.A (.var 0)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.ιB))
        S.ψ‖ ^ 2 ≤ 1183680 * ε := by
  classical
  set xi : EuclideanSpace ℂ
      ((S.ιA × Option _root_.MIPStarRE.QPBT.MsAnswer) × (S.ιB × Option _root_.MIPStarRE.QPBT.MsAnswer)) :=
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ with hxidef
  have hxi : ‖_root_.MIPStarRE.QPBT.isometryTensor
      (LinearIsometry.id (R := ℂ)
        (E := EuclideanSpace ℂ (S.ιA × Option _root_.MIPStarRE.QPBT.MsAnswer)))
      (LinearIsometry.id (R := ℂ)
        (E := EuclideanSpace ℂ (S.ιB × Option _root_.MIPStarRE.QPBT.MsAnswer))) xi - xi‖ ≤ 0 := by
    rw [_root_.MIPStarRE.QPBT.WinImplications.isometryTensor_id, sub_self, norm_zero]
  have htrans := _root_.MIPStarRE.QPBT.MagicSquareRigidity.ms_anticommutator_transfer_A S
    (LinearIsometry.id (R := ℂ)
      (E := EuclideanSpace ℂ (S.ιA × Option _root_.MIPStarRE.QPBT.MsAnswer)))
    (LinearIsometry.id (R := ℂ)
      (E := EuclideanSpace ℂ (S.ιB × Option _root_.MIPStarRE.QPBT.MsAnswer))) xi ε 0 hwin hxi
  simp only [_root_.MIPStarRE.QPBT.MagicSquareRigidity.conjIsometry_comp_naimarkEmbedding,
    _root_.MIPStarRE.QPBT.WinImplications.conjIsometry_id, _root_.MIPStarRE.QPBT.MagicSquareRigidity.opDistSq_uniform_unit] at htrans
  rw [hxidef] at htrans
  have hL : _root_.MIPStarRE.QPBT.heteroKron
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := _root_.MIPStarRE.QPBT.MsAnswer)
          (_root_.MIPStarRE.QPBT.obsOf ((S.A (.var 0)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero)))
        (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ιB × Option _root_.MIPStarRE.QPBT.MsAnswer)) *
        _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := _root_.MIPStarRE.QPBT.MsAnswer)
          (_root_.MIPStarRE.QPBT.obsOf ((S.A (.var 4)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))) 1 -
      -(_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := _root_.MIPStarRE.QPBT.MsAnswer)
          (_root_.MIPStarRE.QPBT.obsOf ((S.A (.var 4)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))) 1 *
        _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := _root_.MIPStarRE.QPBT.MsAnswer)
          (_root_.MIPStarRE.QPBT.obsOf ((S.A (.var 0)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero))) 1) =
      _root_.MIPStarRE.QPBT.heteroKron
        (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation (α := _root_.MIPStarRE.QPBT.MsAnswer)
          (_root_.MIPStarRE.QPBT.obsOf ((S.A (.var 0)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero) *
              _root_.MIPStarRE.QPBT.obsOf ((S.A (.var 4)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero) +
            _root_.MIPStarRE.QPBT.obsOf ((S.A (.var 4)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero) *
              _root_.MIPStarRE.QPBT.obsOf ((S.A (.var 0)).postprocess _root_.MIPStarRE.QPBT.msBitOrZero)))
        (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ιB × Option _root_.MIPStarRE.QPBT.MsAnswer)) := by
    simp only [_root_.MIPStarRE.QPBT.heteroKron_mul, one_mul, sub_neg_eq_add,
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkInflation_mul, ← _root_.MIPStarRE.QPBT.heteroKron_add_left, _root_.MIPStarRE.QPBT.WinImplications.naimarkInflation_add]
  rw [hL, _root_.MIPStarRE.QPBT.WinImplications.norm_heteroKron_naimarkInflation_one] at htrans
  have hclose := _root_.MIPStarRE.QPBT.MagicSquareRigidity.msVarObsA_anticommute S ε hwin
  rw [_root_.MIPStarRE.QPBT.WinImplications.msVarObsA_eq, _root_.MIPStarRE.QPBT.WinImplications.msVarObsA_eq] at hclose
  have hnorm : ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 0))
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ιB × Option _root_.MIPStarRE.QPBT.MsAnswer)) *
        _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 4)) 1 -
        -(_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 4)) 1 *
          _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 0)) 1))
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ)‖ ≤
        624 * Real.sqrt ε := hclose
  have hsq : ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 0))
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op (S.ιB × Option _root_.MIPStarRE.QPBT.MsAnswer)) *
        _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 4)) 1 -
        -(_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 4)) 1 *
          _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.MagicSquareRigidity.dilatedObsA S (.var 0)) 1))
      (_root_.MIPStarRE.QPBT.MagicSquareRigidity.naimarkDilatedState _root_.MIPStarRE.QPBT.MsAnswer S.ψ)‖ ^ 2 ≤
        389376 * ε := by
    have hnn : (0 : ℝ) ≤ 624 * Real.sqrt ε := by positivity
    calc _ ≤ (624 * Real.sqrt ε) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) hnn).2 hnorm
      _ = 389376 * ε := by
          rw [mul_pow, Real.sq_sqrt hε]
          ring
  have h48 : (48 : ℝ) * 0 ^ 2 = 0 := by norm_num
  rw [h48, add_zero] at htrans
  refine le_trans htrans ?_
  linarith
