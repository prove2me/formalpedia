-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_clause_gain_concave
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:33:09.158188+00:00
-- url     : https://prove2.me/submissions/c87bce47-e39b-4992-9fe3-70a672f725bc

import Definitions.Def_KSATSingleFlip_Connect_SoftFieldClause
import Theorems.Thm_KSATSingleFlip_Connect_concave_test_perspective
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect Set

private theorem perspective_mix (ψ : ℝ → ℝ) (hψ : ConcaveOn ℝ (Icc 0 1) ψ)
    (x0 x1 y0 y1 a b : ℝ)
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hy0 : 0 ≤ y0) (hy1 : 0 ≤ y1)
    (hxs : 0 < x0+x1) (hys : 0 < y0+y1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a*softPerspective ψ x0 x1 + b*softPerspective ψ y0 y1 ≤
      softPerspective ψ (a*x0+b*y0) (a*x1+b*y1) := by
  have h := concave_test_perspective ψ hψ x0 x1 y0 y1 a b hx0 hx1 hy0 hy1 hxs hys ha hb hab
  have heq : a*x0+b*y0+(a*x1+b*y1) = a*(x0+x1)+b*(y0+y1) := by ring
  unfold softPerspective
  rw [heq]
  nlinarith

private theorem positive_case (ψ : ℝ → ℝ) (hψ : ConcaveOn ℝ (Icc 0 1) ψ)
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0) (v0 v1 : ℝ) (hv0 : 0 < v0) (hv1 : 0 < v1) :
    ConcaveOn ℝ (Icc 0 1) (softClauseGain ψ v0 v1) ∧
      softClauseGain ψ v0 v1 0 = 0 ∧ softClauseGain ψ v0 v1 1 = 0 := by
  constructor
  · refine ⟨convex_Icc 0 1, ?_⟩
    intro s hs t ht a b ha hb hab
    have hs0 : 0 ≤ 1-s := by linarith [hs.2]
    have ht0 : 0 ≤ 1-t := by linarith [ht.2]
    have h1 := perspective_mix ψ hψ ((1-s)*v0) v1 ((1-t)*v0) v1 a b
      (mul_nonneg hs0 (le_of_lt hv0)) (le_of_lt hv1) (mul_nonneg ht0 (le_of_lt hv0)) (le_of_lt hv1)
      (by positivity) (by positivity) ha hb hab
    have h2 := perspective_mix ψ hψ v0 ((1-s)*v1) v0 ((1-t)*v1) a b
      (le_of_lt hv0) (mul_nonneg hs0 (le_of_lt hv1)) (le_of_lt hv0) (mul_nonneg ht0 (le_of_lt hv1))
      (by positivity) (by positivity) ha hb hab
    have hlin0 : a*((1-s)*v0)+b*((1-t)*v0) = (1-(a*s+b*t))*v0 := by
      have hb' : b=1-a := by linarith
      subst b
      ring
    have hlin1 : a*((1-s)*v1)+b*((1-t)*v1) = (1-(a*s+b*t))*v1 := by
      have hb' : b=1-a := by linarith
      subst b
      ring
    have hv0' : a*v0+b*v0 = v0 := by nlinarith
    have hv1' : a*v1+b*v1 = v1 := by nlinarith
    rw [hlin0,hv1'] at h1
    rw [hv0',hlin1] at h2
    simp only [smul_eq_mul]
    unfold softClauseGain
    have hcancel : a*(1-s)+b*(1-t) = 1-(a*s+b*t) := by nlinarith
    have hcancel' := congrArg (fun x : ℝ => x*softPerspective ψ v0 v1) hcancel
    nlinarith [hcancel']
  · constructor
    · simp [softClauseGain]
    · have hz0 : softPerspective ψ 0 v1 = 0 := by
        unfold softPerspective
        simp [ne_of_gt hv1,hψ1]
      have hz1 : softPerspective ψ v0 0 = 0 := by
        unfold softPerspective
        simp [ne_of_gt hv0,hψ0]
      simp [softClauseGain,hz0,hz1]


theorem solution (ψ : ℝ → ℝ) (hψ : ConcaveOn ℝ (Icc 0 1) ψ)
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0) (v0 v1 : ℝ) (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1) :
    ConcaveOn ℝ (Icc 0 1) (softClauseGain ψ v0 v1) ∧
      softClauseGain ψ v0 v1 0 = 0 ∧ softClauseGain ψ v0 v1 1 = 0 := by
  have hzleft (v : ℝ) : softPerspective ψ 0 v = 0 := by
    by_cases hv : v=0
    · simp [softPerspective,hv]
    · simp [softPerspective,hv,hψ1]
  have hzright (v : ℝ) : softPerspective ψ v 0 = 0 := by
    simp [softPerspective,hψ0]
  by_cases h0 : v0=0
  · subst v0
    have hh : softClauseGain ψ 0 v1 = fun _ => 0 := by
      funext s
      simp [softClauseGain,hzleft,hzright]
    rw [hh]
    simp [concaveOn_const, convex_Icc]
  by_cases h1 : v1=0
  · subst v1
    have hh : softClauseGain ψ v0 0 = fun _ => 0 := by
      funext s
      simp [softClauseGain,hzleft,hzright]
    rw [hh]
    simp [concaveOn_const, convex_Icc]
  exact positive_case ψ hψ hψ0 hψ1 v0 v1 (lt_of_le_of_ne hv0 (Ne.symm h0)) (lt_of_le_of_ne hv1 (Ne.symm h1))
