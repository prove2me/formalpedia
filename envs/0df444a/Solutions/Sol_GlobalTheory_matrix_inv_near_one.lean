-- Prove2me | solution 1 for GlobalTheory.matrix_inv_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:19:58.891409+00:00
-- url     : https://prove2.me/submissions/a451d561-9e61-4ece-a796-2c6fdc64d5b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricMatrixInvNearOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n]
    [DecidableEq n] (X Z : Matrix n n E) (t : ℝ), 0 ≤ t → t < 1 → Z * X = 1 →
    (∀ i j, ‖(X - 1) i j‖ ≤ t) → ∀ i j, ‖(Z - 1) i j‖ ≤ t := by
  intro E _ _ n _ _ X Z t ht0 ht1 hZX hX i j
  have key : Z - 1 = -((X - 1) + (Z - 1) * (X - 1)) := by
    have h : (Z - 1) * (X - 1) = Z * X - Z - X + 1 := by noncomm_ring
    rw [h, hZX]; abel
  haveI : Nonempty (n × n) := ⟨(i, j)⟩
  obtain ⟨⟨i0, j0⟩, hmax⟩ := Finite.exists_max (fun p : n × n => ‖(Z - 1) p.1 p.2‖)
  set s := ‖(Z - 1) i0 j0‖ with hs
  have hbound : ∀ a b, ‖(Z - 1) a b‖ ≤ max t (s * t) := by
    intro a b
    have hprod : ‖((Z - 1) * (X - 1)) a b‖ ≤ s * t := by
      rw [Matrix.mul_apply]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
        (mul_nonneg (norm_nonneg _) ht0) fun k _ => ?_
      rw [norm_mul]
      exact mul_le_mul (hmax (a, k)) (hX k b) (norm_nonneg _) (norm_nonneg _)
    rw [key, Matrix.neg_apply, norm_neg, Matrix.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hX a b) hprod)
  have hs0 : 0 ≤ s := norm_nonneg _
  have hst : s ≤ t := by
    by_contra hlt
    push_neg at hlt
    have h1 := hbound i0 j0
    rw [← hs] at h1
    rcases le_max_iff.mp h1 with h | h
    · linarith
    · nlinarith
  exact (hmax (i, j)).trans hst
end GlobalTheory
