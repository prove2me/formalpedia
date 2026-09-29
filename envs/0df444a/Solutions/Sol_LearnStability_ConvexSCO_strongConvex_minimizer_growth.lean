-- Prove2me | solution 1 for LearnStability.ConvexSCO.strongConvex_minimizer_growth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:52:31.428269+00:00
-- url     : https://prove2.me/submissions/bcd9e1dc-c999-4be3-9013-b3f190eb465c

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {Hset : Set E} {lam : ℝ} (hlam : 0 ≤ lam)
    {g : E → ℝ} (hg : StrongConvexOn Hset lam g) {h : E} (hh : h ∈ Hset)
    (hmin : ∀ h' ∈ Hset, g h ≤ g h') :
    ∀ h' ∈ Hset, lam / 2 * ‖h' - h‖ ^ 2 ≤ g h' - g h := by
  intro h' hh'
  obtain ⟨hconv, hsc⟩ := hg
  have hA : 0 ≤ lam / 2 * ‖h' - h‖ ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have := hmin h' hh'
    linarith
  · refine le_of_forall_pos_le_add ?_
    intro ε hε
    have hq : 0 < ε / (lam / 2 * ‖h' - h‖ ^ 2) := div_pos hε hApos
    have ht0 : 0 < min (1 / 2 : ℝ) (ε / (lam / 2 * ‖h' - h‖ ^ 2)) :=
      lt_min (by norm_num) hq
    have ht1 : min (1 / 2 : ℝ) (ε / (lam / 2 * ‖h' - h‖ ^ 2)) ≤ 1 / 2 := min_le_left _ _
    set t := min (1 / 2 : ℝ) (ε / (lam / 2 * ‖h' - h‖ ^ 2)) with htdef
    have hcomb : t • h' + (1 - t) • h ∈ Hset :=
      hconv hh' hh ht0.le (by linarith) (by ring)
    have hineq := hsc hh' hh ht0.le (by linarith : (0 : ℝ) ≤ 1 - t) (by ring)
    have hmn := hmin _ hcomb
    simp only [smul_eq_mul] at hineq
    have hne : (lam / 2 * ‖h' - h‖ ^ 2) ≠ 0 := ne_of_gt hApos
    have htA : t * (lam / 2 * ‖h' - h‖ ^ 2) ≤ ε := by
      have hm : t ≤ ε / (lam / 2 * ‖h' - h‖ ^ 2) := min_le_right _ _
      have hcancel : (ε / (lam / 2 * ‖h' - h‖ ^ 2)) * (lam / 2 * ‖h' - h‖ ^ 2) = ε :=
        div_mul_cancel₀ ε hne
      calc t * (lam / 2 * ‖h' - h‖ ^ 2)
          ≤ (ε / (lam / 2 * ‖h' - h‖ ^ 2)) * (lam / 2 * ‖h' - h‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hm hA
        _ = ε := hcancel
    have hstep : t * g h ≤ t * (g h' - (1 - t) * (lam / 2 * ‖h' - h‖ ^ 2)) := by
      nlinarith [hmn, hineq]
    have hdiv := le_of_mul_le_mul_left hstep ht0
    linarith [hdiv, htA]
