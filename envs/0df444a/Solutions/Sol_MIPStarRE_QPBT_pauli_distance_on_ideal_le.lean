-- Prove2me | solution 1 for MIPStarRE.QPBT.pauli_distance_on_ideal_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:52:45.10379+00:00
-- url     : https://prove2.me/submissions/f01af6de-e6cb-46fb-a1f6-3918804ed0d7

-- Generated proof for MIPStarRE.QPBT.pauli_distance_on_ideal_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_Decoding
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Extraction_EncodingSupport
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_defect_eq
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_distance_le_two_defect
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_SandwichProduct_avg_diagonal_postprocess_stateQForm_le
import Theorems.Thm_MIPStarRE_QPBT_abs_stateQForm_sub_le_of_contraction
import Theorems.Thm_MIPStarRE_QPBT_polyFunc_eval_collision_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Extraction/PauliComparison.lean. -/
/-!
# Total Pauli comparison on a normalized ideal state

The complete answer-summed distance is controlled by the evaluated overlap on
another normalized state, the Schwartz--Zippel collision probability, and the
distance between the states. This is the operator comparison used after the
swap and auxiliary-state construction.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1827-1858`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement

noncomputable section

/-- A symmetric operator acts identically on the two halves of the extracted
EPR pair, including arbitrary auxiliary registers in local player order. -/
theorem extracted_epr_actions_eq {I J V : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (aux : EuclideanSpace ℂ (I × J)) (T : _root_.LIDT.MIPStarRE.Quantum.Op V) (hT : Tᵀ = T) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op I) T) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (J × V)))
        (_root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor aux (_root_.MIPStarRE.QPBT.eprState V))) =
      _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (I × V)) (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op J) T))
        (_root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor aux (_root_.MIPStarRE.QPBT.eprState V))) := by
  ext p
  simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.one_apply, _root_.MIPStarRE.QPBT.reindexState, _root_.MIPStarRE.QPBT.vecTensor,
    _root_.MIPStarRE.QPBT.eprState, _root_.MIPStarRE.QPBT.prodShuffle, mul_ite, ite_mul, Prod.ext_iff, ite_and]
  rw [show T p.2.2 p.1.2 = T p.1.2 p.2.2 from congrFun (congrFun hT p.1.2) p.2.2]
  simp





end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Extraction/PolynomialCollision.lean. -/
/-!
# Real polynomial collision bounds

The existing Schwartz–Zippel estimate for bounded polynomial representatives
is expressed as a nonnegative rational cardinality ratio. This module converts
it to the real uniform average used by the sandwich support comparison and
specializes it to the polynomial outcomes of the Pauli basis test.

## References

* `references/qpbt-paper/04_preliminaries.tex`, `lem:schwartz-zippel`.
* Blueprint `lem:schwartz-zippel-individual` and the collision calculation
  preceding `eq:qld-nonencoding-mass` in `sec:separating`.
* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1492`,
  the consistency calculation in `lem:qld-construct-the-paulis` whose decoder
  substitution requires the blueprint's nonencoding-mass estimate.
* `docs/paper-gaps/qpbt_decoding-identity.tex`, for that substitution's scope.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.LDT.Preliminaries



/-- The collision hypothesis for the sandwich support comparison on QPBT
polynomial outcomes, with the field cardinality written as `P.q`.

This specializes `polyFunc_eval_collision_le` to the fixed field model and
`evalPoly`; it adds no assumptions to the admissible parameter domain of
blueprint `eq:qld-nonencoding-mass`. -/
theorem poly_eval_collision_le {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (first second : _root_.MIPStarRE.QPBT.Poly P) (hne : first ≠ second) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
      (fun point => if _root_.MIPStarRE.QPBT.evalPoly first point = _root_.MIPStarRE.QPBT.evalPoly second point then (1 : ℝ) else 0) ≤
        (P.m * P.d : ℝ) / P.q := by
  have hcard : Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) = P.q :=
    @_root_.LIDT.MIPStarRE.LDT.FieldModel.card P.q P.model.toFieldModel
  unfold _root_.MIPStarRE.QPBT.evalPoly
  conv_rhs => rw [← hcard]
  exact _root_.MIPStarRE.QPBT.polyFunc_eval_collision_le first second hne

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



























/-- The state quadratic form is additive over finite sums of operators. This is
the formalization-only identity `lem:distance-qform-finset-sum`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M b) := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]































































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/DistanceTheorems/TensorSupport.lean. -/
/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective





/-- Formalization-only auxiliary lemma for Fact 4.26: products of left and right
placements evaluate as a Kronecker product. -/
theorem placed_product_stateQForm_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A 1 * _root_.MIPStarRE.QPBT.heteroKron 1 B) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A B) := by
  congr 1
  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor A B































end MIPStarRE.QPBT.DistanceCalculus

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



















/-- An operator `K` with `Kᴴ K ≤ 1` does not increase norms. -/
theorem norm_applyOperatorToState_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hK : Kᴴ * K ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState K v‖ ≤ ‖v‖ := by
  have h := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hK v
  have hv : (inner ℂ v v).re = ‖v‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_sq, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_one, hv] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h















/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/









/-! ## Matrices of isometries -/





















/-! ## The ground projection -/





















/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





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





























end

end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Extraction/OverlapTransfer.lean. -/
/-!
# Transfer of the complete Pauli overlap between states

A selected sum of effects of a complete measurement is a positive contraction.
Applied to the product measurement, this bounds the complete overlap operator,
independently of the number of answers. Its expectation changes by at most twice
the distance between unit vectors. Schwartz--Zippel then removes unequal Pauli
encodings after the change of state.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1827-1858`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement

noncomputable section

/-- Any selected sum of effects of a complete measurement is a contraction.
The estimate applies to the whole sum and has no outcome-cardinality factor. -/
theorem norm_apply_measurement_sum_le {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (s : Finset α)
    (psi : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (∑ a ∈ s, M.effect a) psi‖ ≤ ‖psi‖ := by
  have hpos : 0 ≤ ∑ a ∈ s, M.effect a := Finset.sum_nonneg (fun a _ => M.pos a)
  have hle : ∑ a ∈ s, M.effect a ≤ 1 := by
    rw [← M.sum_eq_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun a _ _ => M.pos a)
  apply _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_le
  rw [(Matrix.nonneg_iff_posSemidef.mp hpos).isHermitian.eq]
  exact (_root_.LIDT.MIPStarRE.Quantum.sq_le_self hpos hle).trans hle



/-- The complete diagonal overlap of two local measurements is stable under a
change of unit state. The tensor factors can have different dimensions. -/
theorem abs_diagonal_overlap_state_sub_le {α I J : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : _root_.LIDT.MIPStarRE.Quantum.Measurement α I) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement α J)
    (psi phi : EuclideanSpace ℂ (I × J)) (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1) :
    |(∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm psi (_root_.MIPStarRE.QPBT.heteroKron (A.effect a) (B.effect a))) -
      ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm phi (_root_.MIPStarRE.QPBT.heteroKron (A.effect a) (B.effect a))| ≤
        2 * ‖psi - phi‖ := by
  let s := Finset.univ.filter (fun ab : α × α => ab.1 = ab.2)
  have heq : (∑ ab ∈ s, (_root_.MIPStarRE.QPBT.tensorMeasurement A B).effect ab) =
      ∑ a, _root_.MIPStarRE.QPBT.heteroKron (A.effect a) (B.effect a) := by
    simp [s, Finset.sum_filter, Fintype.sum_prod_type, _root_.MIPStarRE.QPBT.tensorMeasurement,
      _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne]
  have h := _root_.MIPStarRE.QPBT.abs_stateQForm_sub_le_of_contraction _
    (_root_.MIPStarRE.QPBT.norm_apply_measurement_sum_le (_root_.MIPStarRE.QPBT.tensorMeasurement A B) s) psi phi hpsi hphi
  rw [heq, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum] at h
  exact h

/-- Averaging evaluated overlaps does not increase the state-transfer cost.
This controls the complete overlap in paper `eq:qld-unitary-9`. -/
theorem evaluated_overlap_state_transfer {Y α R I J : Type*}
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype α] [DecidableEq α] [Fintype R] [DecidableEq R]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement α I) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement α J) (eval : α → Y → R)
    (psi phi : EuclideanSpace ℂ (I × J)) (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y => ∑ r, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm psi
      (_root_.MIPStarRE.QPBT.heteroKron ((A.postprocess (fun a => eval a y)).effect r)
        ((B.postprocess (fun a => eval a y)).effect r))) ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y => ∑ r, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm phi
        (_root_.MIPStarRE.QPBT.heteroKron ((A.postprocess (fun a => eval a y)).effect r)
          ((B.postprocess (fun a => eval a y)).effect r))) + 2 * ‖psi - phi‖ := by
  have h := _root_.LIDT.MIPStarRE.LDT.avgOver_mono (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) _ _ (fun y =>
    (le_abs_self _).trans (_root_.MIPStarRE.QPBT.abs_diagonal_overlap_state_sub_le
      (A.postprocess (fun a => eval a y)) (B.postprocess (fun a => eval a y))
      psi phi hpsi hphi))
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability _
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _)] at h
  linarith

/-- Two distinct Pauli answers have encodings agreeing on at most an `md/q`
fraction of points. Injectivity follows from the exact decoder identity. -/
theorem pauli_encoding_collision_le {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (h k : _root_.MIPStarRE.QPBT.PauliRegister P) (hne : h ≠ k) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
      (fun u => if _root_.MIPStarRE.QPBT.evalPoly (_root_.MIPStarRE.QPBT.encodingPoly h) u = _root_.MIPStarRE.QPBT.evalPoly (_root_.MIPStarRE.QPBT.encodingPoly k) u
        then (1 : ℝ) else 0) ≤ (P.m * P.d : ℝ) / P.q := by
  apply _root_.MIPStarRE.QPBT.poly_eval_collision_le
  intro heq
  apply hne
  have hd := congrArg (fun g : _root_.MIPStarRE.QPBT.Poly P => _root_.MIPStarRE.QPBT.decodeFq g) heq
  simpa only [_root_.MIPStarRE.QPBT.decodeFq_lowDegreeEncoding] using hd

/-- The unevaluated Pauli overlap on a unit comparison state is bounded below
by the evaluated overlap on another unit state, minus the collision and state
errors. This combines paper `eq:qld-unitary-8` with the transfer following
`eq:qld-unitary-9`, without any dimension or answer-count factor. -/
theorem pauli_overlap_transfer {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliRegister P) I) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliRegister P) J)
    (theta ideal : EuclideanSpace ℂ (I × J))
    (htheta : ‖theta‖ = 1) (hideal : ‖ideal‖ = 1) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun u =>
      ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm theta
        (_root_.MIPStarRE.QPBT.heteroKron ((A.postprocess (fun h => _root_.MIPStarRE.QPBT.evalPoly (_root_.MIPStarRE.QPBT.encodingPoly h) u)).effect a)
          ((B.postprocess (fun h => _root_.MIPStarRE.QPBT.evalPoly (_root_.MIPStarRE.QPBT.encodingPoly h) u)).effect a))) ≤
      (∑ h, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ideal (_root_.MIPStarRE.QPBT.heteroKron (A.effect h) (B.effect h))) +
        (P.m * P.d : ℝ) / P.q + 2 * ‖theta - ideal‖ := by
  have ht := _root_.MIPStarRE.QPBT.evaluated_overlap_state_transfer A B
    (fun h u => _root_.MIPStarRE.QPBT.evalPoly (_root_.MIPStarRE.QPBT.encodingPoly h) u) theta ideal htheta hideal
  have hc := _root_.MIPStarRE.QPBT.SandwichProduct.avg_diagonal_postprocess_stateQForm_le A B ideal
    (fun h u => _root_.MIPStarRE.QPBT.evalPoly (_root_.MIPStarRE.QPBT.encodingPoly h) u) ((P.m * P.d : ℝ) / P.q) hideal
    (by positivity) _root_.MIPStarRE.QPBT.pauli_encoding_collision_le
  exact ht.trans (add_le_add hc le_rfl)

end

end MIPStarRE.QPBT

/-!
# Total Pauli comparison on a normalized ideal state

The complete answer-summed distance is controlled by the evaluated overlap on
another normalized state, the Schwartz--Zippel collision probability, and the
distance between the states. This is the operator comparison used after the
swap and auxiliary-state construction.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1827-1858`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliRegister P) (I × _root_.MIPStarRE.QPBT.PauliRegister P)) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (aux : EuclideanSpace ℂ (I × J)) (haux : ‖aux‖ = 1)
    (theta : EuclideanSpace ℂ ((I × _root_.MIPStarRE.QPBT.PauliRegister P) × (J × _root_.MIPStarRE.QPBT.PauliRegister P)))
    (htheta : ‖theta‖ = 1) :
    let ideal := _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor aux (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)))
    let B := _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := J) (_root_.MIPStarRE.QPBT.pauliRegisterMeas (params := P) W)
    (∑ h : _root_.MIPStarRE.QPBT.PauliRegister P, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron (A.effect h - _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op I) (_root_.MIPStarRE.QPBT.pauliProj W h))
        (1 : _root_.LIDT.MIPStarRE.Quantum.Op (J × _root_.MIPStarRE.QPBT.PauliRegister P))) ideal‖ ^ 2) ≤
      2 * (1 - _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun u =>
        ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm theta
          (_root_.MIPStarRE.QPBT.heteroKron ((A.postprocess (fun h => _root_.MIPStarRE.QPBT.evalPoly (_root_.MIPStarRE.QPBT.encodingPoly h) u)).effect a)
            ((B.postprocess (fun h => _root_.MIPStarRE.QPBT.evalPoly (_root_.MIPStarRE.QPBT.encodingPoly h) u)).effect a)))) +
        2 * ((P.m * P.d : ℝ) / P.q) + 4 * ‖theta - ideal‖ := by
  dsimp only
  let ideal := _root_.MIPStarRE.QPBT.reindexState _root_.MIPStarRE.QPBT.prodShuffle (_root_.MIPStarRE.QPBT.vecTensor aux (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)))
  let B := _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := J) (_root_.MIPStarRE.QPBT.pauliRegisterMeas (params := P) W)
  have hideal : ‖ideal‖ = 1 := by
    rw [_root_.MIPStarRE.QPBT.reindexState_norm_eq, _root_.MIPStarRE.QPBT.vecTensor_norm_eq, haux, _root_.MIPStarRE.QPBT.eprState_norm, one_mul]
  have hdist := _root_.MIPStarRE.QPBT.DistanceCalculus.point_distance_le_two_defect
    (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := J × _root_.MIPStarRE.QPBT.PauliRegister P) A)
    (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := I × _root_.MIPStarRE.QPBT.PauliRegister P) B) ideal
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq, hideal, one_pow] at hdist
  have haction (h : _root_.MIPStarRE.QPBT.PauliRegister P) :
      _root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.heteroKron (A.effect h - _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op I) (_root_.MIPStarRE.QPBT.pauliProj W h))
            (1 : _root_.LIDT.MIPStarRE.Quantum.Op (J × _root_.MIPStarRE.QPBT.PauliRegister P))) ideal =
        _root_.MIPStarRE.QPBT.applyOperatorToState
          ((_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := J × _root_.MIPStarRE.QPBT.PauliRegister P) A).effect h -
            (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := I × _root_.MIPStarRE.QPBT.PauliRegister P) B).effect h) ideal := by
    change _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (A.effect h - _) _) ideal =
      _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (A.effect h) _ -
        _root_.MIPStarRE.QPBT.heteroKron _ (_root_.MIPStarRE.QPBT.heteroKron _ (_root_.MIPStarRE.QPBT.pauliProj W h))) ideal
    rw [_root_.MIPStarRE.QPBT.heteroKron_sub_left, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_sub_op,
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_sub_op,
      _root_.MIPStarRE.QPBT.extracted_epr_actions_eq aux _ (_root_.MIPStarRE.QPBT.pauliProj_transpose W h)]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (_root_.MIPStarRE.QPBT.PauliRegister P)))
    rfl (fun h _ => congrArg (fun v => ‖v‖ ^ 2) (haction h))
  rw [hsum]
  have hoverlap := _root_.MIPStarRE.QPBT.pauli_overlap_transfer A B theta ideal htheta hideal
  simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne,
    _root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq] at hdist
  exact hdist.trans (by dsimp [B] at hoverlap ⊢; linarith)
