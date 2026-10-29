-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_pinched_le_marginal_add_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:45:51.90737+00:00
-- url     : https://prove2.me/submissions/c20e6331-62d0-4b46-b661-0a945705732c

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_pinched_le_marginal_add_sqrt.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_consistencyDefect_eq_one_sub_overlap
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono

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
namespace MIPStarRE.QPBT.SandwichProduct
end MIPStarRE.QPBT.SandwichProduct

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

















/-- The state quadratic form is additive over finite sums of operators. This is
the formalization-only identity `lem:distance-qform-finset-sum`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M b) := by
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

/- Source helpers from QPBT/Games/Sandwich/Defs.lean. -/
/-! # Definitions for sandwiched measurements

This module defines the palindromic operator products and the conditional
collision predicate used by the sandwich and pasting lemmas.

## References

Blueprint `lem:ld-sandwich` and `lem:pasting`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-525`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open DistanceCalculus












/-! ### Tensor placements of measurements

The operator families compared in `lem:pasting` are placed on one factor of a
bipartite space. The two constructions below present such a placed family as a
measurement, so that the consistency calculus applies to it verbatim. -/









/-- The left placement of a projective measurement is projective.
Formalization support for `lem:pasting`, blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem Measurement.isProjective_leftPlacement {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (_root_.MIPStarRE.QPBT.Measurement.leftPlacement (ιB := ιB) M) := by
  intro a
  constructor
  · show _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1 * _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1 =
      _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, (hM a).isIdempotentElem.eq, mul_one]
  · show (_root_.MIPStarRE.QPBT.heteroKron (M.effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB))ᴴ = _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1
    unfold _root_.MIPStarRE.QPBT.heteroKron Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian M a,
      Matrix.conjTranspose_one]
















end MIPStarRE.QPBT

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



/-- The Cauchy--Schwarz step of `lem:pasting` at a fixed question: the gap
between the overlap of a projective measurement with a first codeword family
and its overlap with the pinching of that family by a projective family on the
same factor is at most the square root of the summed commutator mass of the two
families. This is step 2 of the proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`; blueprint
`ch12_qpbt_games.tex:960-990`. -/
private theorem abs_pinch_overlap_gap_le_sqrt {R₁ Γ₂ ι : Type*}
    [Fintype R₁] [DecidableEq R₁] [Fintype Γ₂] [DecidableEq Γ₂]
    [Fintype ι] [DecidableEq ι]
    (A P : _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι) (G : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₂ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (hψ : ‖ψ‖ = 1)
    (hA : _root_.MIPStarRE.QPBT.Measurement.IsProjective A)
    (hG : _root_.MIPStarRE.QPBT.Measurement.IsProjective G) :
    |∑ a : R₁, (_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect a) (P.effect a)) -
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect a)
          (∑ g : Γ₂, G.effect g * P.effect a * G.effect g)))| ≤
      Real.sqrt (∑ a : R₁, ∑ g : Γ₂,
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2) := by
  classical
  -- the two inlined identities of the distance calculus; see issue Dengnifer/MIPStarRE-QPBT-bak#204
  have happ : ∀ (M N : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) (v : EuclideanSpace ℂ (ι × ι)),
      _root_.MIPStarRE.QPBT.applyOperatorToState (M * N) v =
        _root_.MIPStarRE.QPBT.applyOperatorToState M (_root_.MIPStarRE.QPBT.applyOperatorToState N v) := by
    intro M N v
    unfold _root_.MIPStarRE.QPBT.applyOperatorToState
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
  have hqf : ∀ M N : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι), _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M * N) =
      (inner ℂ (_root_.MIPStarRE.QPBT.applyOperatorToState Mᴴ ψ) (_root_.MIPStarRE.QPBT.applyOperatorToState N ψ)).re := by
    intro M N
    have hadj : (Matrix.toEuclideanLin M).adjoint = Matrix.toEuclideanLin Mᴴ := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    have h1 : (inner ℂ ((Matrix.toEuclideanLin M).adjoint ψ)
        (_root_.MIPStarRE.QPBT.applyOperatorToState N ψ) : ℂ) =
        inner ℂ ψ (Matrix.toEuclideanLin M (_root_.MIPStarRE.QPBT.applyOperatorToState N ψ)) :=
      LinearMap.adjoint_inner_left _ _ _
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, happ]
    rw [show _root_.MIPStarRE.QPBT.applyOperatorToState Mᴴ ψ = (Matrix.toEuclideanLin M).adjoint ψ by
      rw [hadj]; rfl]
    rw [h1]
    rfl
  have hct : ∀ (M N : _root_.LIDT.MIPStarRE.Quantum.Op ι), (_root_.MIPStarRE.QPBT.heteroKron M N)ᴴ = _root_.MIPStarRE.QPBT.heteroKron Mᴴ Nᴴ := by
    intro M N
    unfold _root_.MIPStarRE.QPBT.heteroKron
    exact Matrix.conjTranspose_kronecker M N
  have hqsub : ∀ M N : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι),
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M - N) = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M - _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ N := by
    intro M N
    simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
  -- the commutator rearrangement of the pinching defect
  have hterm : ∀ a : R₁, P.effect a -
      (∑ g : Γ₂, G.effect g * P.effect a * G.effect g) =
      ∑ g : Γ₂, (P.effect a * G.effect g - G.effect g * P.effect a) * G.effect g := by
    intro a
    have h1 : (∑ g : Γ₂, P.effect a * G.effect g) = P.effect a := by
      rw [← Finset.mul_sum, G.sum_eq_one, mul_one]
    calc P.effect a - ∑ g : Γ₂, G.effect g * P.effect a * G.effect g
        = (∑ g : Γ₂, P.effect a * G.effect g) -
            ∑ g : Γ₂, G.effect g * P.effect a * G.effect g := by rw [h1]
      _ = ∑ g : Γ₂, (P.effect a * G.effect g - G.effect g * P.effect a * G.effect g) := by
            rw [← Finset.sum_sub_distrib]
      _ = ∑ g : Γ₂, (P.effect a * G.effect g - G.effect g * P.effect a) * G.effect g := by
            refine Finset.sum_congr rfl fun g _ => ?_
            rw [sub_mul, mul_assoc (P.effect a), (hG g).isIdempotentElem.eq]
  -- the summand as a product of two placed operators
  have hfac : ∀ (a : R₁) (g : Γ₂),
      _root_.MIPStarRE.QPBT.heteroKron (A.effect a)
          ((P.effect a * G.effect g - G.effect g * P.effect a) * G.effect g) =
        _root_.MIPStarRE.QPBT.heteroKron (A.effect a) (P.effect a * G.effect g - G.effect g * P.effect a) *
          _root_.MIPStarRE.QPBT.heteroKron (A.effect a) (G.effect g) := by
    intro a g
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, (hA a).isIdempotentElem.eq]
  -- the two mass estimates
  have hone1 : _root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) ψ = ψ := by
    simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
  let M : _root_.LIDT.MIPStarRE.Quantum.Measurement (R₁ × Γ₂) (ι × ι) :=
    _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne
      (fun p => _root_.MIPStarRE.QPBT.heteroKron (A.effect p.1) (G.effect p.2))
      (fun p => _root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg (A.pos p.1) (G.pos p.2))
      (by
        rw [Fintype.sum_prod_type]
        rw [show (∑ a : R₁, ∑ g : Γ₂, _root_.MIPStarRE.QPBT.heteroKron (A.effect a) (G.effect g)) =
            ∑ a : R₁, _root_.MIPStarRE.QPBT.heteroKron (A.effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) from
          Finset.sum_congr rfl fun a _ => by
            rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right, G.sum_eq_one]]
        rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left, A.sum_eq_one, _root_.MIPStarRE.QPBT.heteroKron_one_one])
  have hmass : (∑ p : R₁ × Γ₂,
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (A.effect p.1) (G.effect p.2)) ψ‖ ^ 2) ≤ 1 := by
    have h := _root_.MIPStarRE.QPBT.DistanceCalculus.sum_norm_mul_apply_le (fun p : R₁ × Γ₂ => M.effect p) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) ψ
      (_root_.MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one M)
    simp only [M, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne, mul_one] at h
    rw [hone1, hψ, one_pow] at h
    exact h
  have hcontract : ∀ (a : R₁) (g : Γ₂),
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (A.effect a)
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2 ≤
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2 := by
    intro a g
    have hpr : _root_.LIDT.MIPStarRE.Quantum.IsProj (_root_.MIPStarRE.QPBT.heteroKron (A.effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)) :=
      _root_.MIPStarRE.QPBT.Measurement.isProjective_leftPlacement (ιB := ι) A hA a
    have hle : (_root_.MIPStarRE.QPBT.heteroKron (A.effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))ᴴ *
        _root_.MIPStarRE.QPBT.heteroKron (A.effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ≤ 1 := by
      rw [hpr.isSelfAdjoint.isHermitian.eq, hpr.isIdempotentElem.eq]
      exact _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one (_root_.MIPStarRE.QPBT.Measurement.leftPlacement (ιB := ι) A) a
    have hsplit : _root_.MIPStarRE.QPBT.heteroKron (A.effect a)
        (P.effect a * G.effect g - G.effect g * P.effect a) =
        _root_.MIPStarRE.QPBT.heteroKron (A.effect a) 1 *
          _root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * G.effect g - G.effect g * P.effect a) := by
      rw [_root_.MIPStarRE.QPBT.heteroKron_mul, mul_one, one_mul]
    rw [hsplit]
    have h := _root_.MIPStarRE.QPBT.DistanceCalculus.sum_norm_mul_apply_le
      (fun _ : Unit => _root_.MIPStarRE.QPBT.heteroKron (A.effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
      (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * G.effect g - G.effect g * P.effect a)) ψ
      (by simpa using hle)
    simpa using h
  have hXH : ∀ (a : R₁) (g : Γ₂),
      (_root_.MIPStarRE.QPBT.heteroKron (A.effect a) (P.effect a * G.effect g - G.effect g * P.effect a))ᴴ =
        - _root_.MIPStarRE.QPBT.heteroKron (A.effect a)
          (P.effect a * G.effect g - G.effect g * P.effect a) := by
    intro a g
    rw [hct, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian A a, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian P a, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian G g,
      ← _root_.MIPStarRE.QPBT.heteroKron_neg_right]
    congr 1
    abel
  have hnormXH : ∀ (a : R₁) (g : Γ₂),
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (A.effect a)
          (P.effect a * G.effect g - G.effect g * P.effect a))ᴴ ψ‖ =
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (A.effect a)
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ := by
    intro a g
    rw [hXH a g, show _root_.MIPStarRE.QPBT.applyOperatorToState (-(_root_.MIPStarRE.QPBT.heteroKron (A.effect a)
        (P.effect a * G.effect g - G.effect g * P.effect a))) ψ =
        -_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (A.effect a)
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ by
      simp [_root_.MIPStarRE.QPBT.applyOperatorToState], norm_neg]
  -- the pointwise expansion of the gap
  have hexpand : (∑ a : R₁, (_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect a) (P.effect a)) -
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect a)
        (∑ g : Γ₂, G.effect g * P.effect a * G.effect g)))) =
      ∑ p : R₁ × Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect p.1)
        ((P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1) *
          G.effect p.2)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hqsub, ← _root_.MIPStarRE.QPBT.heteroKron_sub_right, hterm a, _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
  set u : R₁ × Γ₂ → EuclideanSpace ℂ (ι × ι) := fun p =>
    _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (A.effect p.1)
      (P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1)) ψ with hu
  set v : R₁ × Γ₂ → EuclideanSpace ℂ (ι × ι) := fun p =>
    _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (A.effect p.1) (G.effect p.2)) ψ with hv
  have hpoint : ∀ p : R₁ × Γ₂,
      |stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect p.1)
        ((P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1) *
          G.effect p.2))| ≤ ‖u p‖ * ‖v p‖ := by
    intro p
    rw [hfac p.1 p.2, hqf]
    refine le_trans (Complex.abs_re_le_norm _) ?_
    refine le_trans (norm_inner_le_norm _ _) ?_
    rw [hu, hv, hnormXH p.1 p.2]
  rw [hexpand]
  have hsum2 : (∑ a : R₁, ∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1
      (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2) =
      ∑ p : R₁ × Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1
        (P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1)) ψ‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
  rw [hsum2]
  calc |∑ p : R₁ × Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect p.1)
          ((P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1) *
            G.effect p.2))| ≤
        ∑ p : R₁ × Γ₂, |stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect p.1)
          ((P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1) *
            G.effect p.2))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : R₁ × Γ₂, ‖u p‖ * ‖v p‖ := Finset.sum_le_sum fun p _ => hpoint p
    _ ≤ Real.sqrt (∑ p : R₁ × Γ₂, ‖u p‖ ^ 2) *
          Real.sqrt (∑ p : R₁ × Γ₂, ‖v p‖ ^ 2) := by
        simpa using Real.sum_mul_le_sqrt_mul_sqrt
          (Finset.univ : Finset (R₁ × Γ₂)) (fun p => ‖u p‖) (fun p => ‖v p‖)
    _ ≤ Real.sqrt (∑ p : R₁ × Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1
          (P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1)) ψ‖ ^ 2) * 1 := by
        refine mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        · exact Real.sqrt_le_sqrt
            (Finset.sum_le_sum fun p _ => hcontract p.1 p.2)
        · rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
          exact Real.sqrt_le_sqrt hmass
    _ = Real.sqrt (∑ p : R₁ × Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1
          (P.effect p.1 * G.effect p.2 - G.effect p.2 * P.effect p.1)) ψ‖ ^ 2) := by
        rw [mul_one]



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
    {X Y₁ Y₂ R₁ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
    (D : _root_.LIDT.MIPStarRE.LDT.Distribution ((X × Y₁) × Y₂)) (G₂ : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₂ ι)
    (P A : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (K : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1)
    (hA : ∀ q, _root_.MIPStarRE.QPBT.Measurement.IsProjective (A q))
    (hG₂ : ∀ x, _root_.MIPStarRE.QPBT.Measurement.IsProjective (G₂ x))
    (hK : _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => ∑ a : R₁, ∑ g : Γ₂,
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect a * (G₂ q.1.1).effect g -
        (G₂ q.1.1).effect g * (P q).effect a)) ψ‖ ^ 2) ≤ K) :
    _root_.MIPStarRE.QPBT.consistencyDefect D (fun q a => _root_.MIPStarRE.QPBT.heteroKron ((A q).effect a) 1)
        (fun q a => _root_.MIPStarRE.QPBT.heteroKron 1 (∑ g : Γ₂, (G₂ q.1.1).effect g * (P q).effect a *
          (G₂ q.1.1).effect g)) ψ ≤
      _root_.MIPStarRE.QPBT.consistencyDefect D (fun q a => _root_.MIPStarRE.QPBT.heteroKron ((A q).effect a) 1)
        (fun q a => _root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect a)) ψ + Real.sqrt K := by
  classical
  let pinchM : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι := fun q =>
    _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne
      (fun a => ∑ g : Γ₂, (G₂ q.1.1).effect g * (P q).effect a * (G₂ q.1.1).effect g)
      (fun a => Finset.sum_nonneg fun g _ =>
        conj_effect_nonneg (G₂ q.1.1) g ((P q).pos a))
      (pinched_sum_eq_one (G₂ q.1.1) (P q) (hG₂ q.1.1))
  have e1 := _root_.MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap D
    (fun q => _root_.MIPStarRE.QPBT.Measurement.leftPlacement (ιB := ι) (A q))
    (fun q => _root_.MIPStarRE.QPBT.Measurement.rightPlacement (ιA := ι) (pinchM q)) ψ hD hψ
  have e2 := _root_.MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap D
    (fun q => _root_.MIPStarRE.QPBT.Measurement.leftPlacement (ιB := ι) (A q))
    (fun q => _root_.MIPStarRE.QPBT.Measurement.rightPlacement (ιA := ι) (P q)) ψ hD hψ
  simp only [_root_.MIPStarRE.QPBT.Measurement.leftPlacement_effect, _root_.MIPStarRE.QPBT.Measurement.rightPlacement_effect,
    pinchM, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] at e1 e2
  simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq] at e1 e2
  rw [e1, e2]
  set OP : ((X × Y₁) × Y₂) → ℝ := fun q =>
    ∑ a : R₁, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect a) ((P q).effect a)) with hOP
  set OQ : ((X × Y₁) × Y₂) → ℝ := fun q =>
    ∑ a : R₁, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect a)
      (∑ g : Γ₂, (G₂ q.1.1).effect g * (P q).effect a * (G₂ q.1.1).effect g)) with hOQ
  set CM : ((X × Y₁) × Y₂) → ℝ := fun q => ∑ a : R₁, ∑ g : Γ₂,
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect a * (G₂ q.1.1).effect g -
      (G₂ q.1.1).effect g * (P q).effect a)) ψ‖ ^ 2 with hCM
  have hf : ∀ q, |OP q - OQ q| ≤ Real.sqrt (CM q) := by
    intro q
    have hpt := abs_pinch_overlap_gap_le_sqrt (A q) (P q) (G₂ q.1.1) ψ hψ
      (hA q) (hG₂ q.1.1)
    rw [hOP, hOQ, hCM]
    rw [show (∑ a : R₁, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect a) ((P q).effect a))) -
        ∑ a : R₁, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect a)
          (∑ g : Γ₂, (G₂ q.1.1).effect g * (P q).effect a * (G₂ q.1.1).effect g)) =
        ∑ a : R₁, (_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect a) ((P q).effect a)) -
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A q).effect a)
            (∑ g : Γ₂, (G₂ q.1.1).effect g * (P q).effect a *
              (G₂ q.1.1).effect g))) by rw [Finset.sum_sub_distrib]]
    exact hpt
  have hg : ∀ q, 0 ≤ CM q := by
    intro q
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun g _ => sq_nonneg _
  have hjensen : |avgOver D (fun q => OP q - OQ q)| ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver D CM) :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise D
      (fun q => OP q - OQ q) CM hf hg (by rw [hD.weight_sum_eq_one])
  have hfinal : _root_.LIDT.MIPStarRE.LDT.avgOver D OP - _root_.LIDT.MIPStarRE.LDT.avgOver D OQ ≤ Real.sqrt K := by
    rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_sub]
    refine le_trans (le_abs_self _) (le_trans hjensen ?_)
    exact Real.sqrt_le_sqrt hK
  linarith
