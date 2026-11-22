-- Prove2me | solution 1 for MasulloRH.zeta_iterated_deriv_bound_right_half_strip
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T23:42:35.940369+00:00
-- url     : https://prove2.me/submissions/3a478f60-4507-47d2-a448-0da4418fe1a6

import Theorems.Thm_Zeta23_RvM_norm_riemannZeta_le_of_re_pos
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic

set_option autoImplicit false

open Complex Set Metric

namespace MasulloRH

private lemma quarter_ball_bounds {s z : ℂ}
    (hsre : (1 / 2 : ℝ) ≤ s.re) (hsim : (2 : ℝ) ≤ |s.im|)
    (hz : z ∈ closedBall s (1 / 4 : ℝ)) :
    (1 / 4 : ℝ) ≤ z.re ∧ 1 ≤ |z.im| ∧ ‖z‖ ≤ ‖s‖ + 1 / 4 := by
  have hd : ‖z - s‖ ≤ (1 / 4 : ℝ) := mem_closedBall_iff_norm.mp hz
  have hr : |z.re - s.re| ≤ (1 / 4 : ℝ) := by
    simpa only [sub_re] using (abs_re_le_norm (z - s)).trans hd
  have hi : |s.im - z.im| ≤ (1 / 4 : ℝ) := by
    simpa only [sub_im, abs_sub_comm] using (abs_im_le_norm (z - s)).trans hd
  have hit : |s.im| ≤ |s.im - z.im| + |z.im| := by
    simpa using abs_add_le (s.im - z.im) z.im
  refine ⟨by linarith [(abs_le.mp hr).1], by linarith, ?_⟩
  calc
    ‖z‖ = ‖(z - s) + s‖ := by congr 1; ring
    _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
    _ ≤ ‖s‖ + 1 / 4 := by linarith

private lemma zeta_quarter_ball_norm {s z : ℂ}
    (hsre : (1 / 2 : ℝ) ≤ s.re) (hsim : (2 : ℝ) ≤ |s.im|)
    (hz : z ∈ closedBall s (1 / 4 : ℝ)) :
    ‖riemannZeta z‖ ≤ 4 * (‖s‖ + 1) := by
  obtain ⟨hr, hi, hn⟩ := quarter_ball_bounds hsre hsim hz
  have hz1 : z ≠ 1 := by
    intro he
    simp only [he, one_im, abs_zero] at hi
    linarith
  have hp : (0 : ℝ) < z.re := by linarith
  have hnorm : (1 : ℝ) ≤ ‖1 - z‖ := by
    calc
      1 ≤ |z.im| := hi
      _ = |(1 - z).im| := by simp
      _ ≤ ‖1 - z‖ := abs_im_le_norm _
  have hinv : 1 / ‖1 - z‖ ≤ (1 : ℝ) := by
    exact (div_le_one (by positivity)).2 hnorm
  have hdiv : ‖z‖ / z.re ≤ 4 * (‖s‖ + 1 / 4) := by
    apply (div_le_iff₀ hp).2
    have hpos : 0 ≤ ‖s‖ + (1 / 4 : ℝ) := by positivity
    nlinarith
  have h := Zeta23.RvM.norm_riemannZeta_le_of_re_pos hp hz1
  linarith

/-- An explicit all-order Cauchy estimate on the right half-strip. This theorem
uses the classical Euler--Maclaurin zeta bound and imposes no zero-location premise. -/
theorem zeta_iterated_deriv_bound_right_half_strip (r : ℕ) (s : ℂ)
    (hsre : (1 / 2 : ℝ) ≤ s.re) (hsim : (2 : ℝ) ≤ |s.im|) :
    ‖iteratedDeriv r riemannZeta s‖ ≤
      (r.factorial : ℝ) * (4 * (‖s‖ + 1)) / (1 / 4 : ℝ) ^ r := by
  have hd : DiffContOnCl ℂ riemannZeta (ball s (1 / 4 : ℝ)) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    apply (differentiableAt_riemannZeta ?_).differentiableWithinAt
    intro he
    have hi := (quarter_ball_bounds hsre hsim (closure_ball_subset_closedBall hz)).2.1
    simp only [he, one_im, abs_zero] at hi
    linarith
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le r
    (by norm_num) hd (fun z hz => zeta_quarter_ball_norm hsre hsim
      (sphere_subset_closedBall hz))

/-- The derivative bound in the exact rectangle leaf has the explicit rational
witness `16 * (100003 + n)`, uniformly in the requested distance parameter `k`. -/
theorem unit_height_zeta_right_rectangle_deriv_bound (n k : ℕ) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let left : ℝ := 1 / 2 + margin
    let bottom : ℝ := (100000 : ℝ) + n + margin
    let top : ℝ := (100000 : ℝ) + n + 1
    ∀ s ∈ Complex.reProdIm (Set.Icc left 1) (Set.Icc bottom top),
      ‖deriv riemannZeta s‖ ≤ (16 : ℝ) * (100003 + n) := by
  dsimp
  intro s hs
  obtain ⟨⟨hrl, hru⟩, ⟨hil, hiu⟩⟩ := Complex.mem_reProdIm.mp hs
  have hm : (0 : ℝ) < 1 / ((k : ℝ) + 3) := by positivity
  have hr : (1 / 2 : ℝ) ≤ s.re := by linarith
  have hi : (2 : ℝ) ≤ s.im := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hiabs : (2 : ℝ) ≤ |s.im| := hi.trans (le_abs_self _)
  have hnorm : ‖s‖ ≤ (100002 : ℝ) + n := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = s.re + s.im := by rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      _ ≤ (100002 : ℝ) + n := by linarith
  have h := zeta_iterated_deriv_bound_right_half_strip 1 s hr hiabs
  norm_num [iteratedDeriv_one] at h
  nlinarith

end MasulloRH

theorem solution (r : ℕ) (s : ℂ)
    (hsre : (1 / 2 : ℝ) ≤ s.re) (hsim : (2 : ℝ) ≤ |s.im|) :
    ‖iteratedDeriv r riemannZeta s‖ ≤
      (r.factorial : ℝ) * (4 * (‖s‖ + 1)) / (1 / 4 : ℝ) ^ r := by
  exact MasulloRH.zeta_iterated_deriv_bound_right_half_strip r s hsre hsim

#print axioms solution
