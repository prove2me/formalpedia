-- Prove2me | solution 1 for MatousekLP.SmallestBall.unique_smallest_ball_iff
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T05:05:11.166107+00:00
-- url     : https://prove2.me/submissions/a5533923-80e0-4d54-849a-cb95936bd512

import Definitions.Def_MatousekLP_SmallestBall_Basic
import Mathlib

open scoped RealInnerProductSpace
open MatousekLP.SmallestBall

theorem solution {d k : ℕ} (s : Fin k → EuclideanSpace ℝ (Fin d))
    (sstar : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : 0 ≤ r)
    (hbd : ∀ j, dist (s j) sstar = r) :
    IsUniqueSmallestEnclosingBall (Set.range s) sstar r ↔
      ∀ u : EuclideanSpace ℝ (Fin d), ∃ j : Fin k, ⟪u, s j - sstar⟫ ≤ 0 := by
  -- squared distance from `s j` to a shifted centre
  have hsq : ∀ (j : Fin k) (u : EuclideanSpace ℝ (Fin d)),
      ‖s j - (sstar + u)‖ ^ 2 = r ^ 2 - 2 * ⟪u, s j - sstar⟫ + ‖u‖ ^ 2 := by
    intro j u
    have h1 : s j - (sstar + u) = (s j - sstar) - u := by abel
    rw [h1, norm_sub_sq_real, ← dist_eq_norm, hbd j, real_inner_comm]
  constructor
  · rintro ⟨-, -, hmin⟩ u
    by_contra hall
    push_neg at hall
    by_cases hk : Nonempty (Fin k)
    · -- `u ≠ 0`, and a small shift of the centre along `u` still encloses all points
      obtain ⟨j₀⟩ := hk
      have hu : u ≠ 0 := by
        rintro rfl; have := hall j₀; simp at this
      have hu2 : 0 < ‖u‖ ^ 2 := by positivity
      obtain ⟨j₁, -, hj₁⟩ := Finset.univ.exists_min_image (fun j => ⟪u, s j - sstar⟫)
        ⟨j₀, Finset.mem_univ _⟩
      set ε := ⟪u, s j₁ - sstar⟫ / ‖u‖ ^ 2
      have hε : 0 < ε := div_pos (hall j₁) hu2
      have hcover : Set.range s ⊆ Metric.closedBall (sstar + ε • u) r := by
        rintro _ ⟨j, rfl⟩
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h2 := hsq j (ε • u)
        rw [real_inner_smul_left, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h2
        have hj := hj₁ j (Finset.mem_univ _)
        have hεu : ε * ‖u‖ ^ 2 = ⟪u, s j₁ - sstar⟫ := div_mul_cancel₀ _ hu2.ne'
        have hle : ‖s j - (sstar + ε • u)‖ ^ 2 ≤ r ^ 2 := by
          rw [h2]; nlinarith [hall j]
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero).mp hle
      have := (hmin _ _ hcover).2 le_rfl
      have hεu0 : ε • u = 0 := by simpa using this
      exact hu ((smul_eq_zero.mp hεu0).resolve_left hε.ne')
    · -- no points: every radius encloses the empty set
      have hempty : Set.range s ⊆ Metric.closedBall sstar (-1) := by
        rintro _ ⟨j, rfl⟩; exact absurd ⟨j⟩ hk
      linarith [(hmin sstar (-1) hempty).1]
  · intro hcond
    refine ⟨hr, ?_, fun c' r' hcov => ?_⟩
    · rintro _ ⟨j, rfl⟩; rw [Metric.mem_closedBall, hbd j]
    · obtain ⟨j, hj⟩ := hcond (c' - sstar)
      have h2 := hsq j (c' - sstar)
      rw [show sstar + (c' - sstar) = c' by abel] at h2
      have hdist : ‖s j - c'‖ ≤ r' := by
        have := hcov ⟨j, rfl⟩; rwa [Metric.mem_closedBall, dist_eq_norm] at this
      have hr'0 : 0 ≤ r' := (norm_nonneg _).trans hdist
      have hsq' : ‖s j - c'‖ ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
      have hge : r ^ 2 + ‖c' - sstar‖ ^ 2 ≤ r' ^ 2 := by nlinarith
      refine ⟨?_, fun hle => ?_⟩
      · nlinarith [sq_nonneg ‖c' - sstar‖]
      · have : ‖c' - sstar‖ ^ 2 ≤ 0 := by nlinarith
        have : ‖c' - sstar‖ = 0 := by nlinarith [norm_nonneg (c' - sstar)]
        exact sub_eq_zero.mp (norm_eq_zero.mp this)
