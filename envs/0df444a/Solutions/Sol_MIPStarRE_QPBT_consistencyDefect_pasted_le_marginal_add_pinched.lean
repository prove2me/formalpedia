-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_pasted_le_marginal_add_pinched
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:49:11.514561+00:00
-- url     : https://prove2.me/submissions/74d9a1f9-eb71-4083-9106-2d21d10e97d4

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_pasted_le_marginal_add_pinched.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_defect_eq
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_SandwichProduct_consistencyDefect_placed_eq_avg_point

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











/-- Formalization-only auxiliary lemma for `def:tensor-product-strategy`
(blueprint `def:tensor-product-strategy`): tensor placement
is additive in the right factor. -/
theorem heteroKron_add_right {ιA ιB : Type*} (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B C : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron A (B + C) = _root_.MIPStarRE.QPBT.heteroKron A B + _root_.MIPStarRE.QPBT.heteroKron A C := by
  ext p q
  simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, mul_add]



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



/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): the state quadratic form is additive in its operator. -/
theorem stateQForm_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M N : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M + N) = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M + _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ N := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]









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

/- Source helpers from QPBT/Games/Sandwich/Pasting/PinchedReduction.lean. -/
/-! # The pinched reduction of the pasting estimate

This module records step 1 of the proof of the adopted statement of
`lem:pasting`: the defect of the pasted family is at most the defect of the
second marginal comparison plus the pinched defect.

## References

`lem:pasting` in `blueprint/src/chapter/ch12_qpbt_games.tex:960-990`, with the
proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open DistanceCalculus

/-- Conjugating a positive operator by an effect of a measurement is positive.
Formalization-only auxiliary step for `lem:pasting`; the effects of a
measurement are self-adjoint, so the conjugation is a congruence. -/
private theorem conj_effect_nonneg {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι] (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (a : α) {N : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hN : 0 ≤ N) :
    0 ≤ M.effect a * N * M.effect a := by
  apply Matrix.nonneg_iff_posSemidef.mpr
  have hpos : ((M.effect a)ᴴ * N * M.effect a).PosSemidef :=
    (Matrix.nonneg_iff_posSemidef.mp hN).conjTranspose_mul_mul_same (M.effect a)
  rwa [_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian M a] at hpos

/-- The pinched first codeword family of `lem:pasting`: the coarse first
codeword effects conjugated by the fine second codeword effects. -/
private theorem pinched_sum_eq_one {Γ₂ R₁ ι : Type*} [Fintype Γ₂]
    [DecidableEq Γ₂] [Fintype R₁] [DecidableEq R₁] [Fintype ι] [DecidableEq ι]
    (G : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₂ ι) (P : _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι)
    (hG : _root_.MIPStarRE.QPBT.Measurement.IsProjective G) :
    (∑ a : R₁, ∑ g : Γ₂, G.effect g * P.effect a * G.effect g) = 1 := by
  classical
  rw [Finset.sum_comm]
  calc
    (∑ g : Γ₂, ∑ a : R₁, G.effect g * P.effect a * G.effect g) =
        ∑ g : Γ₂, G.effect g * (∑ a : R₁, P.effect a) * G.effect g := by
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ g : Γ₂, G.effect g := by
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [P.sum_eq_one, mul_one, (hG g).isIdempotentElem.eq]
    _ = 1 := G.sum_eq_one







end MIPStarRE.QPBT

/-! # The pinched reduction of the pasting estimate

This module records step 1 of the proof of the adopted statement of
`lem:pasting`: the defect of the pasted family is at most the defect of the
second marginal comparison plus the pinched defect.

## References

`lem:pasting` in `blueprint/src/chapter/ch12_qpbt_games.tex:960-990`, with the
proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus

theorem solution
    {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype Γ₁] [DecidableEq Γ₁]
    [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
    (D : _root_.LIDT.MIPStarRE.LDT.Distribution ((X × Y₁) × Y₂))
    (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₁ : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₁ ι) (G₂ : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₂ ι)
    (A : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement (R₁ × R₂) ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (hψ : ‖ψ‖ = 1)
    (hG₂ : ∀ x, _root_.MIPStarRE.QPBT.Measurement.IsProjective (G₂ x)) :
    _root_.MIPStarRE.QPBT.consistencyDefect D (fun q a => _root_.MIPStarRE.QPBT.heteroKron ((A q).effect a) 1)
        (fun q a => _root_.MIPStarRE.QPBT.heteroKron 1 (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
          if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
            _root_.MIPStarRE.QPBT.pastedMeasurement (fun g => (G₁ q.1.1).effect g)
              (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0)) ψ ≤
      _root_.MIPStarRE.QPBT.consistencyDefect D
        (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
        (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron 1 (((G₂ q.1.1).postprocess
          (fun g => eval₂ g q.2)).effect a₂)) ψ +
      _root_.MIPStarRE.QPBT.consistencyDefect D
        (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
        (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron 1 (∑ g : Γ₂, (G₂ q.1.1).effect g *
          ((G₁ q.1.1).postprocess (fun g' => eval₁ g' q.1.2)).effect a₁ *
          (G₂ q.1.1).effect g)) ψ := by
  classical
  set Pm : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι :=
    fun q => (G₁ q.1.1).postprocess (fun g => eval₁ g q.1.2) with hPm
  set Qm : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement R₂ ι :=
    fun q => (G₂ q.1.1).postprocess (fun g => eval₂ g q.2) with hQm
  set paste : ((X × Y₁) × Y₂) → (R₁ × R₂) → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun q a =>
    ∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
      if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
        _root_.MIPStarRE.QPBT.pastedMeasurement (fun g => (G₁ q.1.1).effect g)
          (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0 with hpaste
  set pinch : ((X × Y₁) × Y₂) → R₁ → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun q a₁ =>
    ∑ g : Γ₂, (G₂ q.1.1).effect g * (Pm q).effect a₁ * (G₂ q.1.1).effect g
    with hpinch
  -- the pasted family, restricted to a fixed pair, is a conjugated coarse effect
  have hpasteEq : ∀ (q : (X × Y₁) × Y₂) (a₁ : R₁) (a₂ : R₂),
      paste q (a₁, a₂) =
        ∑ g ∈ Finset.univ.filter (fun g => eval₂ g q.2 = a₂),
          (G₂ q.1.1).effect g * (Pm q).effect a₁ * (G₂ q.1.1).effect g := by
    intro q a₁ a₂
    simp only [hpaste, _root_.MIPStarRE.QPBT.pastedMeasurement, hPm, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun g₂ _ => ?_
    by_cases h2 : eval₂ g₂ q.2 = a₂
    · simp only [h2, if_true]
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun g₁ _ => ?_
      by_cases h1 : eval₁ g₁ q.1.2 = a₁ <;> simp [h1, Prod.ext_iff]
    · simp [h2, Prod.ext_iff]
  -- the pinched family is a measurement
  have hpinchPos : ∀ (q : (X × Y₁) × Y₂) (a₁ : R₁), 0 ≤ pinch q a₁ := by
    intro q a₁
    exact Finset.sum_nonneg fun g _ =>
      conj_effect_nonneg (G₂ q.1.1) g ((Pm q).pos a₁)
  have hpinchSum : ∀ q : (X × Y₁) × Y₂, (∑ a₁ : R₁, pinch q a₁) = 1 := by
    intro q
    exact pinched_sum_eq_one (G₂ q.1.1) (Pm q) (hG₂ q.1.1)
  have hpasteSum : ∀ q : (X × Y₁) × Y₂, (∑ a : R₁ × R₂, paste q a) = 1 := by
    intro q
    rw [Fintype.sum_prod_type]
    have h : ∀ a₁ : R₁, (∑ a₂ : R₂, paste q (a₁, a₂)) = pinch q a₁ := by
      intro a₁
      simp only [hpinch]
      rw [← Finset.sum_fiberwise Finset.univ (fun g => eval₂ g q.2)
        (fun g => (G₂ q.1.1).effect g * (Pm q).effect a₁ * (G₂ q.1.1).effect g)]
      exact Finset.sum_congr rfl fun a₂ _ => hpasteEq q a₁ a₂
    rw [Finset.sum_congr rfl fun a₁ (_ : a₁ ∈ Finset.univ) => h a₁]
    exact hpinchSum q
  have hpastePos : ∀ (q : (X × Y₁) × Y₂) (a : R₁ × R₂), 0 ≤ paste q a := by
    intro q a
    obtain ⟨a₁, a₂⟩ := a
    rw [hpasteEq q a₁ a₂]
    exact Finset.sum_nonneg fun g _ =>
      conj_effect_nonneg (G₂ q.1.1) g ((Pm q).pos a₁)
  -- the exact operator identity of the reduction
  have hdiff : ∀ (q : (X × Y₁) × Y₂) (a₁ : R₁) (a₂ : R₂),
      (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) + paste q (a₁, a₂) - ((Qm q).effect a₂ + pinch q a₁) =
        ∑ g ∈ Finset.univ.filter (fun g => ¬ eval₂ g q.2 = a₂),
          (G₂ q.1.1).effect g * (1 - (Pm q).effect a₁) * (G₂ q.1.1).effect g := by
    intro q a₁ a₂
    have hsplit1 : (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) =
        (∑ g ∈ Finset.univ.filter (fun g => eval₂ g q.2 = a₂), (G₂ q.1.1).effect g) +
        ∑ g ∈ Finset.univ.filter (fun g => ¬ eval₂ g q.2 = a₂), (G₂ q.1.1).effect g := by
      rw [Finset.sum_filter_add_sum_filter_not]
      exact ((G₂ q.1.1).sum_eq_one).symm
    have hQ : (Qm q).effect a₂ =
        ∑ g ∈ Finset.univ.filter (fun g => eval₂ g q.2 = a₂), (G₂ q.1.1).effect g := by
      simp only [hQm]
      exact _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect (G₂ q.1.1) (fun g => eval₂ g q.2) a₂
    have hpi : pinch q a₁ =
        (∑ g ∈ Finset.univ.filter (fun g => eval₂ g q.2 = a₂),
          (G₂ q.1.1).effect g * (Pm q).effect a₁ * (G₂ q.1.1).effect g) +
        ∑ g ∈ Finset.univ.filter (fun g => ¬ eval₂ g q.2 = a₂),
          (G₂ q.1.1).effect g * (Pm q).effect a₁ * (G₂ q.1.1).effect g := by
      simp only [hpinch]
      rw [Finset.sum_filter_add_sum_filter_not]
    have hrhs : (∑ g ∈ Finset.univ.filter (fun g => ¬ eval₂ g q.2 = a₂),
          (G₂ q.1.1).effect g * (1 - (Pm q).effect a₁) * (G₂ q.1.1).effect g) =
        (∑ g ∈ Finset.univ.filter (fun g => ¬ eval₂ g q.2 = a₂), (G₂ q.1.1).effect g) -
        ∑ g ∈ Finset.univ.filter (fun g => ¬ eval₂ g q.2 = a₂),
          (G₂ q.1.1).effect g * (Pm q).effect a₁ * (G₂ q.1.1).effect g := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      have hexp : (G₂ q.1.1).effect g * (1 - (Pm q).effect a₁) * (G₂ q.1.1).effect g =
          (G₂ q.1.1).effect g * (G₂ q.1.1).effect g -
            (G₂ q.1.1).effect g * (Pm q).effect a₁ * (G₂ q.1.1).effect g := by
        rw [mul_sub, sub_mul, mul_one]
      rw [hexp, (hG₂ q.1.1 g).isIdempotentElem.eq]
    rw [hpasteEq q a₁ a₂, hrhs, hQ, hpi]
    nth_rewrite 1 [hsplit1]
    abel
  -- the pointwise comparison of the quadratic forms
  have hmono : ∀ (q : (X × Y₁) × Y₂) (a₁ : R₁) (a₂ : R₂),
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect (a₁, a₂))
          ((Qm q).effect a₂ + pinch q a₁)) ≤
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect (a₁, a₂)) (1 + paste q (a₁, a₂))) := by
    intro q a₁ a₂
    refine _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono ?_ ψ
    refine Matrix.le_iff.mpr ?_
    rw [← _root_.MIPStarRE.QPBT.heteroKron_sub_right, hdiff q a₁ a₂]
    refine Matrix.nonneg_iff_posSemidef.mp
      (_root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg ((A q).pos (a₁, a₂)) ?_)
    refine Finset.sum_nonneg fun g _ => conj_effect_nonneg (G₂ q.1.1) g ?_
    exact Matrix.nonneg_iff_posSemidef.mpr
      (Matrix.le_iff.mp (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one (Pm q) a₁))
  -- assembly
  have hone : _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) = ‖ψ‖ ^ 2 := by
    have hid : _root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) ψ = ψ := by
      simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, hid]
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) ψ)
  have hA1 : ∀ (q : (X × Y₁) × Y₂) (a₁ : R₁),
      ((A q).postprocess Prod.fst).effect a₁ = ∑ a₂ : R₂, (A q).effect (a₁, a₂) := by
    intro q a₁
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter, Fintype.sum_prod_type]
    have hin : ∀ b₁ : R₁,
        (∑ b₂ : R₂, if (b₁, b₂).1 = a₁ then (A q).effect (b₁, b₂) else 0) =
          if b₁ = a₁ then ∑ b₂ : R₂, (A q).effect (b₁, b₂) else 0 := by
      intro b₁
      by_cases h : b₁ = a₁ <;> simp [h]
    rw [Finset.sum_congr rfl fun b₁ (_ : b₁ ∈ Finset.univ) => hin b₁, Finset.sum_ite_eq']
    simp
  have hA2 : ∀ (q : (X × Y₁) × Y₂) (a₂ : R₂),
      ((A q).postprocess Prod.snd).effect a₂ = ∑ a₁ : R₁, (A q).effect (a₁, a₂) := by
    intro q a₂
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b₁ _ => by simp
  let pasteM : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement (R₁ × R₂) ι := fun q =>
    _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne (paste q) (hpastePos q) (hpasteSum q)
  let pinchM : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι := fun q =>
    _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne (pinch q) (hpinchPos q) (hpinchSum q)
  have hL := _root_.MIPStarRE.QPBT.SandwichProduct.consistencyDefect_placed_eq_avg_point D A pasteM ψ
  simp only [pasteM, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] at hL
  have hR1 := _root_.MIPStarRE.QPBT.SandwichProduct.consistencyDefect_placed_eq_avg_point D
    (fun q => (A q).postprocess Prod.snd) Qm ψ
  have hR2 := _root_.MIPStarRE.QPBT.SandwichProduct.consistencyDefect_placed_eq_avg_point D
    (fun q => (A q).postprocess Prod.fst) pinchM ψ
  simp only [pinchM, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] at hR2
  have hmain : _root_.MIPStarRE.QPBT.consistencyDefect D (fun q a => _root_.MIPStarRE.QPBT.heteroKron ((A q).effect a) 1)
      (fun q a => _root_.MIPStarRE.QPBT.heteroKron 1 (paste q a)) ψ ≤
      _root_.MIPStarRE.QPBT.consistencyDefect D
        (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
        (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron 1 ((Qm q).effect a₂)) ψ +
      _root_.MIPStarRE.QPBT.consistencyDefect D
        (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
        (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron 1 (pinch q a₁)) ψ := by
    rw [hL, hR1, hR2, ← _root_.LIDT.MIPStarRE.LDT.avgOver_add]
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun q => ?_
    have e0 := _root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ι) (A q))
      (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := ι) (pasteM q)) ψ
    simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement, pasteM,
      _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] at e0
    simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq] at e0
    have e1 := _root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq
      (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ι) ((A q).postprocess Prod.snd))
      (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := ι) (Qm q)) ψ
    simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement,
      _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] at e1
    simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq] at e1
    have e2 := _root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq
      (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ι) ((A q).postprocess Prod.fst))
      (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := ι) (pinchM q)) ψ
    simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement, pinchM,
      _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] at e2
    simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq] at e2
    rw [e0, e1, e2, hψ, one_pow]
    have hunit : (∑ a : R₁ × R₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect a) 1)) = 1 := by
      rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum, ← _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left, (A q).sum_eq_one,
        _root_.MIPStarRE.QPBT.heteroKron_one_one, hone, hψ, one_pow]
    have hpair : ∀ F : R₁ → R₂ → _root_.LIDT.MIPStarRE.Quantum.Op ι,
        (∑ a : R₁ × R₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect a) (F a.1 a.2))) =
          ∑ a₁ : R₁, ∑ a₂ : R₂,
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect (a₁, a₂)) (F a₁ a₂)) := by
      intro F
      rw [Fintype.sum_prod_type]
    have hs1 : (∑ a₂ : R₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.snd).effect a₂) ((Qm q).effect a₂))) =
        ∑ a₁ : R₁, ∑ a₂ : R₂,
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect (a₁, a₂)) ((Qm q).effect a₂)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a₂ _ => ?_
      rw [hA2 q a₂, _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
    have hs2 : (∑ a₁ : R₁, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.fst).effect a₁) (pinch q a₁))) =
        ∑ a₁ : R₁, ∑ a₂ : R₂,
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect (a₁, a₂)) (pinch q a₁)) := by
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [hA1 q a₁, _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
    have hterm : ∀ (a₁ : R₁) (a₂ : R₂),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect (a₁, a₂)) ((Qm q).effect a₂)) +
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect (a₁, a₂)) (pinch q a₁)) ≤
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect (a₁, a₂)) 1) +
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect (a₁, a₂)) (paste q (a₁, a₂))) := by
      intro a₁ a₂
      have hl := hmono q a₁ a₂
      rw [_root_.MIPStarRE.QPBT.heteroKron_add_right, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_add, _root_.MIPStarRE.QPBT.heteroKron_add_right,
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_add] at hl
      exact hl
    have hsum : (∑ a₁ : R₁, ∑ a₂ : R₂,
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect (a₁, a₂)) ((Qm q).effect a₂))) +
        (∑ a₁ : R₁, ∑ a₂ : R₂,
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect (a₁, a₂)) (pinch q a₁))) ≤
        (∑ a₁ : R₁, ∑ a₂ : R₂,
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect (a₁, a₂)) 1)) +
        (∑ a₁ : R₁, ∑ a₂ : R₂,
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect (a₁, a₂)) (paste q (a₁, a₂)))) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun a₁ _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun a₂ _ => hterm a₁ a₂
    rw [hs1, hs2]
    rw [hpair (fun _ _ => 1)] at hunit
    rw [hpair (fun a₁ a₂ => paste q (a₁, a₂))]
    linarith
  exact hmain
