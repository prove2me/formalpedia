-- Prove2me | solution 1 for Kyprianou.Ch04.cutoffPredictableIntegrandSquareBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:13:55.827419+00:00
-- url     : https://prove2.me/submissions/db350b60-4544-4c8b-8797-abaaa38e0d89

import Mathlib
open Set
set_option autoImplicit false

/-- The pointwise disjoint-band quadratic bound underlying the compensated L² estimate. -/
theorem solution (g : ℝ → ℝ) (K ε η x y z : ℝ)
    (_hK : 0 ≤ K) (hηε : η < ε)
    (hb : ∀ u, |g u| ≤ K)
    (hg : Differentiable ℝ g) (hd : ∀ u, |deriv g u| ≤ K) :
    (({w : ℝ | η < |w| ∧ |w| < 1}).indicator
        (fun w => w * g x) z -
      ({w : ℝ | ε < |w| ∧ |w| < 1}).indicator
        (fun w => w * g y) z) ^ 2 ≤
    K ^ 2 * (({w : ℝ | η < |w| ∧ |w| ≤ ε ∧ |w| < 1}).indicator
        (fun w => w ^ 2) z +
      ({w : ℝ | ε < |w| ∧ |w| < 1}).indicator
        (fun w => w ^ 2 * (x - y) ^ 2) z) := by
  classical
  have hl : |g x - g y| ≤ K * |x - y| := by
    simpa only [Real.norm_eq_abs] using
      (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun u _ => hg u) (fun u _ => by simpa only [Real.norm_eq_abs] using hd u)
        (Set.mem_univ y) (Set.mem_univ x)
  by_cases hlarge : ε < |z| ∧ |z| < 1
  · have hsmall : η < |z| ∧ |z| < 1 := ⟨hηε.trans hlarge.1, hlarge.2⟩
    have hband : ¬ (η < |z| ∧ |z| ≤ ε ∧ |z| < 1) :=
      fun h => (not_le_of_gt hlarge.1) h.2.1
    simp only [Set.indicator, mem_ofPred_eq, if_pos hlarge, if_pos hsmall, if_neg hband, zero_add]
    have hsq : (g x - g y) ^ 2 ≤ K ^ 2 * (x - y) ^ 2 := by
      calc
        (g x - g y) ^ 2 = |g x - g y| ^ 2 := (sq_abs _).symm
        _ ≤ (K * |x - y|) ^ 2 := by gcongr
        _ = K ^ 2 * (x - y) ^ 2 := by rw [mul_pow, sq_abs]
    calc
      (z * g x - z * g y) ^ 2 = z ^ 2 * (g x - g y) ^ 2 := by ring
      _ ≤ z ^ 2 * (K ^ 2 * (x - y) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg z)
      _ = K ^ 2 * (z ^ 2 * (x - y) ^ 2) := by ring
  · by_cases hsmall : η < |z| ∧ |z| < 1
    · have hband : η < |z| ∧ |z| ≤ ε ∧ |z| < 1 :=
        ⟨hsmall.1, le_of_not_gt (fun h => hlarge ⟨h, hsmall.2⟩), hsmall.2⟩
      simp only [Set.indicator, mem_ofPred_eq, if_neg hlarge, if_pos hsmall, if_pos hband,
        sub_zero, add_zero]
      have hsq : (g x) ^ 2 ≤ K ^ 2 := by
        calc
          (g x) ^ 2 = |g x| ^ 2 := (sq_abs _).symm
          _ ≤ K ^ 2 := by gcongr; exact hb x
      calc
        (z * g x) ^ 2 = z ^ 2 * (g x) ^ 2 := by ring
        _ ≤ z ^ 2 * K ^ 2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg z)
        _ = K ^ 2 * z ^ 2 := by ring
    · have hband : ¬ (η < |z| ∧ |z| ≤ ε ∧ |z| < 1) :=
        fun h => hsmall ⟨h.1, h.2.2⟩
      simp [Set.indicator, hlarge, hsmall, hband]
