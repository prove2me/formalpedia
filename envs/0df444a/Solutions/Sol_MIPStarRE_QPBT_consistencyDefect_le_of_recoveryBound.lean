-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_le_of_recoveryBound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:49:11.586668+00:00
-- url     : https://prove2.me/submissions/4abda5ee-1e53-4460-92e0-d3769da2a7ec

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_le_of_recoveryBound.
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
import Mathlib
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
namespace MIPStarRE.QPBT.RecoveryInternal
end MIPStarRE.QPBT.RecoveryInternal
namespace MIPStarRE.QPBT.SandwichProduct
end MIPStarRE.QPBT.SandwichProduct

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

/-- A positive semidefinite operator has nonnegative state quadratic form. This
is the formalization-only order fact `lem:distance-qform-nonnegative`, used for
the nonnegative overlap terms in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) {M : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hM : 0 ≤ M) :
    0 ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  calc
    0 = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ 0 := by simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
    _ ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hM ψ







/-- The quadratic form of the identity is the squared vector norm. -/
theorem stateQForm_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) = ‖ψ‖ ^ 2 := by
  have hone : _root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ψ = ψ := by
    simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, hone]
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) ψ)





















































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

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/RecoveryDefect.lean. -/
/-!
# Transporting a consistency relation along the recovery step

The recovery step of `lem:ld-combining-recovery` replaces a relation between a
point measurement of the original strategy read through a combination and a
measurement of the combined game read at a point of the combined space by a
relation between the point measurement itself and the same measurement read
through the recovered polynomial tuple.  This module isolates the consistency
calculus of that replacement, in a form which does not mention the low-degree
game.

Both relations are diagonal overlaps of the same pair of measurements placed on
opposite tensor factors, and the two relabellings differ only on the event that
the recovered outcome disagrees with the outcome of the point measurement while
the two relabellings agree.  The probability of that event, averaged over the
auxiliary sample, is bounded at each question by a quantity depending only on
the outcome of the second measurement; since the first measurement is complete,
the total Born weight of an outcome of the second measurement does not depend on
the question, and the bound may therefore be averaged over the question against
that weight.

The two conclusions of `lem:ld-soundness` transported here place the point
measurement on opposite tensor factors, so the calculus is recorded twice, once
for each placement; the two statements share the averaging estimate, which is
insensitive to the placement.

## Main statements

* `consistencyDefect_le_of_recoveryBound` — the transport of a consistency
  relation along a relabelling which is correct off a rare event, with the
  point measurement on the first tensor factor.
* `consistencyDefect_le_of_recoveryBound_right` — the same transport with the
  point measurement on the second tensor factor.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1503`
* `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-288`
* `blueprint/src/chapter/ch13_qpbt_test.tex:617-680`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open DistanceCalculus
open SandwichProduct

noncomputable section

namespace RecoveryInternal

/-! ## Pair expansions of the diagonal overlap -/

/-- The diagonal overlap of a measurement against a relabelled measurement on the
opposite factor is the sum over pairs of outcomes with matching labels. -/
private theorem diagonalRight_pair_sum {β Γ ιA ιB : Type*}
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement β ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (f : Γ → β) :
    (∑ b : β, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
      (_root_.MIPStarRE.QPBT.heteroKron (A.effect b) ((B.postprocess f).effect b))) =
      ∑ b : β, ∑ g : Γ, if f g = b then
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect b) (B.effect g)) else 0 := by
  classical
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
    _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum, Finset.sum_filter]



/-- The diagonal overlap of two relabelled measurements on opposite factors is
the sum over pairs of outcomes with matching labels. -/
private theorem diagonalPair_pair_sum {β Γ R ιA ιB : Type*}
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement β ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (e : β → R) (f : Γ → R) :
    (∑ r : R, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
      (_root_.MIPStarRE.QPBT.heteroKron ((A.postprocess e).effect r) ((B.postprocess f).effect r))) =
      ∑ b : β, ∑ g : Γ, if e b = f g then
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect b) (B.effect g)) else 0 := by
  classical
  have hterm (r : R) : _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
      (_root_.MIPStarRE.QPBT.heteroKron ((A.postprocess e).effect r) ((B.postprocess f).effect r)) =
      ∑ b : β, ∑ g : Γ, if e b = r ∧ f g = r then
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect b) (B.effect g)) else 0 := by
    rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
      _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
      _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : e b = r
    · rw [if_pos hb, _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum,
        Finset.sum_filter]
      refine Finset.sum_congr rfl fun g _ => ?_
      by_cases hg : f g = r <;> simp [hb, hg]
    · simp [hb]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hbg : e b = f g
  · rw [hbg]
    simp
  · refine Eq.trans (Finset.sum_eq_zero fun r _ => ?_) (by simp [hbg])
    simp only [ite_eq_right_iff]
    intro hpair
    exact (hbg (hpair.1.trans hpair.2.symm)).elim



/-! ## The averaging estimate -/

set_option maxHeartbeats 1600000 in
/-- The averaging estimate underlying the recovery transport, stated for the
Born weights alone.  The weights `w x b g` of a pair of outcomes have fiber
sums `W g` independent of the question `x`, and the two diagonal overlaps
differ only on the discrepancy event, whose conditional probability is bounded
by `F x g`; averaging that bound against the fiber weights gives `η`. -/
private theorem recovery_avg_le {X Y β Γ R : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype R] [DecidableEq R]
    (w : X → β → Γ → ℝ) (W : Γ → ℝ)
    (f : X → Γ → β) (e₁ : X → Y → β → R) (f₁ : X → Y → Γ → R)
    (F : X → Γ → ℝ) (η : ℝ)
    (hwnonneg : ∀ x b g, 0 ≤ w x b g) (hWnonneg : ∀ g, 0 ≤ W g)
    (hfiber : ∀ x g, (∑ b : β, w x b g) = W g) (hWsum : (∑ g : Γ, W g) = 1)
    (hFbound : ∀ x b g, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y)
      (fun y => if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) ≤ F x g)
    (hFavg : ∀ g, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) (fun x => F x g) ≤ η) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) (fun x =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y =>
          ∑ b : β, ∑ g : Γ, if e₁ x y b = f₁ x y g then w x b g else 0)) ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
        (fun x => ∑ b : β, ∑ g : Γ, if f x g = b then w x b g else 0) + η := by
  classical
  have hstep : ∀ x : X,
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y =>
          ∑ b : β, ∑ g : Γ, if e₁ x y b = f₁ x y g then w x b g else 0) ≤
        (∑ b : β, ∑ g : Γ, if f x g = b then w x b g else 0) +
          ∑ g : Γ, W g * F x g := by
    intro x
    have hexp : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y =>
        ∑ b : β, ∑ g : Γ, if e₁ x y b = f₁ x y g then w x b g else 0) =
        ∑ b : β, ∑ g : Γ, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y)
          (fun y => if e₁ x y b = f₁ x y g then w x b g else 0) := by
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sum]
      exact Finset.sum_congr rfl fun b _ => _root_.LIDT.MIPStarRE.LDT.avgOver_sum _ _
    rw [hexp]
    have hterm : ∀ b : β, ∀ g : Γ,
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y)
          (fun y => if e₁ x y b = f₁ x y g then w x b g else 0) ≤
          (if f x g = b then w x b g else 0) + w x b g * F x g := by
      intro b g
      have hsplit : ∀ y : Y,
          (if e₁ x y b = f₁ x y g then w x b g else 0) ≤
            (if f x g = b then w x b g else 0) +
              (if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) *
                w x b g := by
        intro y
        by_cases hy : e₁ x y b = f₁ x y g
        · by_cases hb : f x g = b
          · rw [if_pos hy, if_pos hb, if_neg, zero_mul, add_zero]
            rintro ⟨hne, -⟩
            exact hne hb
          · rw [if_pos hy, if_neg hb, if_pos ⟨hb, hy⟩, one_mul, zero_add]
        · rw [if_neg hy]
          have h1 : (0 : ℝ) ≤ if f x g = b then w x b g else 0 := by
            split_ifs
            · exact hwnonneg x b g
            · exact le_rfl
          have h2 : (0 : ℝ) ≤
              (if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) *
                w x b g := by
            have : (0 : ℝ) ≤
                if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0 := by
              split_ifs
              · exact zero_le_one
              · exact le_rfl
            exact mul_nonneg this (hwnonneg x b g)
          linarith
      refine le_trans (_root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ hsplit) ?_
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const, _root_.LIDT.MIPStarRE.LDT.avgOver_mul_const]
      have hcomm : w x b g * F x g = F x g * w x b g := mul_comm _ _
      linarith [mul_le_mul_of_nonneg_right (hFbound x b g) (hwnonneg x b g)]
    refine le_trans (Finset.sum_le_sum fun b _ =>
      Finset.sum_le_sum fun g _ => hterm b g) ?_
    have hsum : (∑ b : β, ∑ g : Γ,
        ((if f x g = b then w x b g else 0) + w x b g * F x g)) =
        (∑ b : β, ∑ g : Γ, if f x g = b then w x b g else 0) +
          ∑ g : Γ, (∑ b : β, w x b g) * F x g := by
      calc (∑ b : β, ∑ g : Γ,
            ((if f x g = b then w x b g else 0) + w x b g * F x g))
          = ∑ b : β, ((∑ g : Γ, if f x g = b then w x b g else 0) +
              ∑ g : Γ, w x b g * F x g) :=
            Finset.sum_congr rfl fun b _ => Finset.sum_add_distrib
        _ = (∑ b : β, ∑ g : Γ, if f x g = b then w x b g else 0) +
              ∑ b : β, ∑ g : Γ, w x b g * F x g := Finset.sum_add_distrib
        _ = (∑ b : β, ∑ g : Γ, if f x g = b then w x b g else 0) +
              ∑ g : Γ, (∑ b : β, w x b g) * F x g := by
            congr 1
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun g _ => (Finset.sum_mul _ _ _).symm
    have hW2 : (∑ g : Γ, (∑ b : β, w x b g) * F x g) =
        ∑ g : Γ, W g * F x g :=
      Finset.sum_congr rfl fun g _ => by rw [hfiber x g]
    rw [hsum, hW2]
  refine le_trans (_root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ hstep) ?_
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add]
  have hswap : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
      (fun x => ∑ g : Γ, W g * F x g) =
      ∑ g : Γ, W g * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) (fun x => F x g) := by
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sum]
    exact Finset.sum_congr rfl fun g _ => _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul _ _ _
  have hfinal : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
      (fun x => ∑ g : Γ, W g * F x g) ≤ η := by
    rw [hswap]
    calc
      (∑ g : Γ, W g * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) (fun x => F x g)) ≤
          ∑ g : Γ, W g * η :=
        Finset.sum_le_sum fun g _ =>
          mul_le_mul_of_nonneg_left (hFavg g) (hWnonneg g)
      _ = η := by rw [← Finset.sum_mul, hWsum, one_mul]
  linarith

end RecoveryInternal

/-! ## The transport of a consistency relation -/

open RecoveryInternal





end

end MIPStarRE.QPBT

/-!
# Transporting a consistency relation along the recovery step

The recovery step of `lem:ld-combining-recovery` replaces a relation between a
point measurement of the original strategy read through a combination and a
measurement of the combined game read at a point of the combined space by a
relation between the point measurement itself and the same measurement read
through the recovered polynomial tuple.  This module isolates the consistency
calculus of that replacement, in a form which does not mention the low-degree
game.

Both relations are diagonal overlaps of the same pair of measurements placed on
opposite tensor factors, and the two relabellings differ only on the event that
the recovered outcome disagrees with the outcome of the point measurement while
the two relabellings agree.  The probability of that event, averaged over the
auxiliary sample, is bounded at each question by a quantity depending only on
the outcome of the second measurement; since the first measurement is complete,
the total Born weight of an outcome of the second measurement does not depend on
the question, and the bound may therefore be averaged over the question against
that weight.

The two conclusions of `lem:ld-soundness` transported here place the point
measurement on opposite tensor factors, so the calculus is recorded twice, once
for each placement; the two statements share the averaging estimate, which is
insensitive to the placement.

## Main statements

* `consistencyDefect_le_of_recoveryBound` — the transport of a consistency
  relation along a relabelling which is correct off a rare event, with the
  point measurement on the first tensor factor.
* `consistencyDefect_le_of_recoveryBound_right` — the same transport with the
  point measurement on the second tensor factor.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1503`
* `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-288`
* `blueprint/src/chapter/ch13_qpbt_test.tex:617-680`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus
open MIPStarRE.QPBT.SandwichProduct



open MIPStarRE.QPBT.RecoveryInternal

/-! ## Pair expansions of the diagonal overlap -/









/-! ## The averaging estimate -/





/-! ## The transport of a consistency relation -/

open MIPStarRE.QPBT.RecoveryInternal

set_option maxHeartbeats 1600000 in

theorem solution
    {X Y β Γ R ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement β ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (f : X → Γ → β) (e₁ : X → Y → β → R) (f₁ : X → Y → Γ → R)
    (F : X → Γ → ℝ) (η : ℝ)
    (hFbound : ∀ x b g, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y)
      (fun y => if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) ≤ F x g)
    (hFavg : ∀ g, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) (fun x => F x g) ≤ η) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
        (fun x b => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect b) 1)
        (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 ((B.postprocess (f x)).effect b)) ψ ≤
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (X × Y))
        (fun z r => _root_.MIPStarRE.QPBT.heteroKron (((A z.1).postprocess (e₁ z.1 z.2)).effect r) 1)
        (fun z r => _root_.MIPStarRE.QPBT.heteroKron 1 ((B.postprocess (f₁ z.1 z.2)).effect r)) ψ + η := by
  classical
  set w : X → β → Γ → ℝ := fun x b g =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((A x).effect b) (B.effect g)) with hwdef
  have hwnonneg : ∀ x b g, 0 ≤ w x b g := fun x b g =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg ψ (_root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg ((A x).pos b) (B.pos g))
  set W : Γ → ℝ := fun g => _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B.effect g))
    with hWdef
  have hWnonneg : ∀ g, 0 ≤ W g := fun g =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg ψ (_root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg
      (Matrix.PosSemidef.one.nonneg : (0 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) ≤ 1) (B.pos g))
  have hfiber : ∀ x g, (∑ b : β, w x b g) = W g := by
    intro x g
    rw [hwdef, hWdef]
    simp only
    rw [← (A x).sum_eq_one, _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
  have hWsum : (∑ g : Γ, W g) = 1 := by
    rw [hWdef]
    simp only
    rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum, ← _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right, B.sum_eq_one,
      _root_.MIPStarRE.QPBT.heteroKron_one_one, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_one, hψ, one_pow]
  -- the two diagonal overlaps
  set AgrG : X → ℝ := fun x =>
    ∑ b : β, ∑ g : Γ, if f x g = b then w x b g else 0 with hAgrG
  set AgrH : X → Y → ℝ := fun x y =>
    ∑ b : β, ∑ g : Γ, if e₁ x y b = f₁ x y g then w x b g else 0 with hAgrH
  have hgoal : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
      (fun x b => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect b) 1)
      (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 ((B.postprocess (f x)).effect b)) ψ =
      1 - _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) AgrG := by
    rw [_root_.MIPStarRE.QPBT.SandwichProduct.consistencyDefect_placed_eq_avg_point (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) A
      (fun x => B.postprocess (f x))]
    have hpoint : ∀ x : X,
        (∑ b : β, ∑ b' : β, if b = b' then 0 else _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
          (_root_.MIPStarRE.QPBT.heteroKron ((A x).effect b) ((B.postprocess (f x)).effect b'))) =
          1 - AgrG x := by
      intro x
      have h := _root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ιB) (A x))
        (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := ιA) (B.postprocess (f x))) ψ
      simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement,
        _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] at h
      simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq] at h
      rw [h, hψ, one_pow, hAgrG]
      simp only
      rw [diagonalRight_pair_sum (A x) B ψ (f x)]
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ hpoint, _root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const]
  have hhyp : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (X × Y))
      (fun z r => _root_.MIPStarRE.QPBT.heteroKron (((A z.1).postprocess (e₁ z.1 z.2)).effect r) 1)
      (fun z r => _root_.MIPStarRE.QPBT.heteroKron 1 ((B.postprocess (f₁ z.1 z.2)).effect r)) ψ =
      1 - _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
        (fun x => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (AgrH x)) := by
    rw [_root_.MIPStarRE.QPBT.SandwichProduct.consistencyDefect_placed_eq_avg_point (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (X × Y))
      (fun z => (A z.1).postprocess (e₁ z.1 z.2))
      (fun z => B.postprocess (f₁ z.1 z.2))]
    have hpoint : ∀ z : X × Y,
        (∑ r : R, ∑ r' : R, if r = r' then 0 else _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
          (_root_.MIPStarRE.QPBT.heteroKron (((A z.1).postprocess (e₁ z.1 z.2)).effect r)
            ((B.postprocess (f₁ z.1 z.2)).effect r'))) =
          1 - AgrH z.1 z.2 := by
      intro z
      have h := _root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq
        (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ιB) ((A z.1).postprocess (e₁ z.1 z.2)))
        (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := ιA) (B.postprocess (f₁ z.1 z.2))) ψ
      simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement,
        _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] at h
      simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq] at h
      rw [h, hψ, one_pow, hAgrH]
      simp only
      rw [diagonalPair_pair_sum (A z.1) B ψ (e₁ z.1 z.2) (f₁ z.1 z.2)]
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ hpoint, _root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const,
      _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (fun x y => AgrH x y)]
  rw [hgoal, hhyp]
  have hkey : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
      (fun x => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (AgrH x)) ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) AgrG + η := by
    rw [hAgrG, hAgrH]
    exact recovery_avg_le w W f e₁ f₁ F η hwnonneg hWnonneg hfiber hWsum
      hFbound hFavg
  linarith
