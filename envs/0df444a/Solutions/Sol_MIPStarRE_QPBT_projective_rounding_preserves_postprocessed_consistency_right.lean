-- Prove2me | solution 1 for MIPStarRE.QPBT.projective_rounding_preserves_postprocessed_consistency_right
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:27:40.253196+00:00
-- url     : https://prove2.me/submissions/7e9182bd-392a-4923-9329-ff02d6a6c3d7

-- Generated proof for MIPStarRE.QPBT.projective_rounding_preserves_postprocessed_consistency_right.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_State
import Theorems.Thm_MIPStarRE_QPBT_projective_rounding_preserves_postprocessed_consistency_left

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
respects differences in the left factor. -/
theorem heteroKron_sub_left {ιA ιB : Type*} (A B : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (C : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron (A - B) C = _root_.MIPStarRE.QPBT.heteroKron A C - _root_.MIPStarRE.QPBT.heteroKron B C :=
  _root_.MIPStarRE.QPBT.kroneckerMap_sub_left A B C

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
4.14): the matrix-vector term in `consistencyDefect` is the state quadratic
form. -/
theorem consistency_term_eq_stateQForm {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm (M.mulVec ψ))).re =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  rfl



































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

/- Source helpers from QPBT/Games/DistanceTheorems/RoundingTransport.lean. -/
/-!
# Projective rounding through outcome postprocessing

Consistent complete POVMs on two possibly different local spaces have projective
roundings on those same spaces. Their consistency with an opposite-player POVM
survives every question-dependent outcome map, with error
`δ + sqrt (220 * δ^(1/4)) + 2 * sqrt (δ + η)` when the original consistency errors
are at most `δ` and `η`. The estimate is independent of both local dimensions and
the number of outcomes.

These are formalization-only auxiliary results for the compression and rounding
argument preceding the polynomial-support argument in `lem:qld-4-7`. They do not
construct the global polynomial-pair measurement.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:135-145`, `lem:ortho`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278-1288`,
  in the proof of `lem:qld-4-7`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:389-401`,
  `fact:triangle-for-simeq` and `fact:data-processing`
- Issue Dengnifer/MIPStarRE-QPBT-bak#278
- `audits/2026-09-06_rounding_transport.md`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section











/-- Tensor-factor exchange intertwines the two Kronecker-product actions. -/
private theorem applyOperatorToState_heteroKron_prodComm {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron B A) (_root_.MIPStarRE.QPBT.reindexState (Equiv.prodComm ιA ιB) ψ) =
      _root_.MIPStarRE.QPBT.reindexState (Equiv.prodComm ιA ιB) (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron A B) ψ) := by
  have hop : _root_.MIPStarRE.QPBT.heteroKron B A =
      (_root_.MIPStarRE.QPBT.heteroKron A B).submatrix (Equiv.prodComm ιB ιA) (Equiv.prodComm ιB ιA) := by
    ext i j
    exact mul_comm _ _
  apply (EuclideanSpace.equiv (ιB × ιA) ℂ).injective
  change _root_.MIPStarRE.QPBT.heteroKron B A *ᵥ (ψ.ofLp ∘ (Equiv.prodComm ιB ιA)) =
    (_root_.MIPStarRE.QPBT.heteroKron A B *ᵥ ψ.ofLp) ∘ (Equiv.prodComm ιB ιA)
  rw [hop, Matrix.submatrix_mulVec_equiv _ _ _ (Equiv.prodComm ιB ιA)]
  rfl

private theorem stateQForm_heteroKron_prodComm {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.reindexState (Equiv.prodComm ιA ιB) ψ) (_root_.MIPStarRE.QPBT.heteroKron B A) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A B) := by
  unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
  rw [applyOperatorToState_heteroKron_prodComm]
  exact congrArg Complex.re
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.prodComm ιA ιB)).inner_map_map
      ψ (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron A B) ψ))

/-- Formalization-only factor-exchange identity for `lem:ortho` and its
transport through postprocessing. The state is explicitly reindexed; neither
equal local spaces nor invariance of the state under exchange is assumed. -/
theorem consistencyDefect_prodComm {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron (B x a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 (A x a)) (_root_.MIPStarRE.QPBT.reindexState (Equiv.prodComm ιA ιB) ψ) =
      _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron (A x a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 (B x a)) ψ := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm, _root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq,
    stateQForm_heteroKron_prodComm]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  rw [Finset.sum_comm]
  simp only [eq_comm]

/-- Formalization-only distance identity for the Bob-side rounding in
`lem:ortho`: left placement on the exchanged state is right placement on the
original state. The two local coordinate types may be different. -/
theorem opFamilyDistSq_left_prodComm {X α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron (A x a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron (B x a) 1) (_root_.MIPStarRE.QPBT.reindexState (Equiv.prodComm ιA ιB) ψ) =
      _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 (A x a))
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 (B x a)) ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  simp_rw [← _root_.MIPStarRE.QPBT.heteroKron_sub_left, applyOperatorToState_heteroKron_prodComm,
    _root_.MIPStarRE.QPBT.reindexState_norm_eq, _root_.MIPStarRE.QPBT.heteroKron_sub_right]





end

end MIPStarRE.QPBT

/-!
# Projective rounding through outcome postprocessing

Consistent complete POVMs on two possibly different local spaces have projective
roundings on those same spaces. Their consistency with an opposite-player POVM
survives every question-dependent outcome map, with error
`δ + sqrt (220 * δ^(1/4)) + 2 * sqrt (δ + η)` when the original consistency errors
are at most `δ` and `η`. The estimate is independent of both local dimensions and
the number of outcomes.

These are formalization-only auxiliary results for the compression and rounding
argument preceding the polynomial-support argument in `lem:qld-4-7`. They do not
construct the global polynomial-pair measurement.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:135-145`, `lem:ortho`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278-1288`,
  in the proof of `lem:qld-4-7`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:389-401`,
  `fact:triangle-for-simeq` and `fact:data-processing`
- Issue Dengnifer/MIPStarRE-QPBT-bak#278
- `audits/2026-09-06_rounding_transport.md`
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution
    {ιA ιB α : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [DecidableEq α]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB) (δ : ℝ) (hδ : 0 ≤ δ)
    (hcons : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (A.effect a) 1)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron 1 (B.effect a)) ψ ≤ δ) :
    ∃ P : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB, _root_.MIPStarRE.QPBT.Measurement.IsProjective P ∧
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun _ a => _root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a))
        (fun _ a => _root_.MIPStarRE.QPBT.heteroKron 1 (B.effect a)) ψ ≤
          220 * Real.rpow δ (1 / 4 : ℝ) ∧
      ∀ {X β : Type*} [Fintype X] [DecidableEq X] [Fintype β] [DecidableEq β]
        (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X), μ.IsProbability → ∀ (f : X → α → β)
        (N : X → _root_.LIDT.MIPStarRE.Quantum.Measurement β ιA) (η : ℝ),
        _root_.MIPStarRE.QPBT.consistencyDefect μ
          (fun x b => _root_.MIPStarRE.QPBT.heteroKron ((N x).effect b) 1)
          (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 ((B.postprocess (f x)).effect b)) ψ ≤ η →
        _root_.MIPStarRE.QPBT.consistencyDefect μ
          (fun x b => _root_.MIPStarRE.QPBT.heteroKron ((N x).effect b) 1)
          (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 ((P.postprocess (f x)).effect b)) ψ ≤
            δ + Real.sqrt (220 * Real.rpow δ (1 / 4 : ℝ)) +
              2 * Real.sqrt (δ + η) := by
  have hψ' : ‖_root_.MIPStarRE.QPBT.reindexState (Equiv.prodComm ιA ιB) ψ‖ = 1 := by
    rw [_root_.MIPStarRE.QPBT.reindexState_norm_eq, hψ]
  have hcons' : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (B.effect a) 1)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron 1 (A.effect a))
      (_root_.MIPStarRE.QPBT.reindexState (Equiv.prodComm ιA ιB) ψ) ≤ δ := by
    rwa [_root_.MIPStarRE.QPBT.consistencyDefect_prodComm]
  obtain ⟨P, hP, hdist, htransport⟩ :=
    _root_.MIPStarRE.QPBT.projective_rounding_preserves_postprocessed_consistency_left
      (_root_.MIPStarRE.QPBT.reindexState (Equiv.prodComm ιA ιB) ψ) hψ' B A δ hδ hcons'
  rw [_root_.MIPStarRE.QPBT.opFamilyDistSq_left_prodComm] at hdist
  refine ⟨P, hP, hdist, ?_⟩
  intro X β _ _ _ _ μ hμ f N η hNB
  have hNB' : _root_.MIPStarRE.QPBT.consistencyDefect μ
      (fun x b => _root_.MIPStarRE.QPBT.heteroKron ((B.postprocess (f x)).effect b) 1)
      (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 ((N x).effect b))
      (_root_.MIPStarRE.QPBT.reindexState (Equiv.prodComm ιA ιB) ψ) ≤ η := by
    rwa [_root_.MIPStarRE.QPBT.consistencyDefect_prodComm]
  have hout := htransport μ hμ f N η hNB'
  rwa [_root_.MIPStarRE.QPBT.consistencyDefect_prodComm] at hout
