-- Prove2me | solution 1 for MasulloRH.two_point_weighted_riesz_profile_discriminator
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T05:31:30.528604+00:00
-- url     : https://prove2.me/submissions/07f6f76f-d000-4857-ae5d-978a709c8b05

import Mathlib
open MeasureTheory
theorem solution (α : ℝ) (hα : 0 ≤ α) (h : ℝ → ℝ)
    (hc : Continuous h) (hcs : HasCompactSupport h) (hn : ∀ y, 0 ≤ h y)
    (hs : ∀ y ≤ 0, h y = 0) (hp : ∃ y, 0 < h y) :
    let w : ℝ → ℝ := fun x => Real.exp (2*α*|x|) * (1+x^2)^2
    w (-1) * (∫ y : ℝ, h y / w (-1-y)) <
      w 1 * (∫ y : ℝ, h y / w (1-y)) := by
  let w : ℝ → ℝ := fun x => Real.exp (2*α*|x|) * (1+x^2)^2
  change w (-1) * _ < w 1 * _
  have hw (x : ℝ) : 0 < w x := by dsimp [w]; positivity
  have hwc : Continuous w := by dsimp [w]; fun_prop
  let F : ℝ → ℝ → ℝ := fun a y => h y / w (a-y)
  have hFc (a : ℝ) : Continuous (F a) :=
    hc.div (hwc.comp (continuous_const.sub continuous_id)) (fun x => (hw _).ne')
  have hFi (a : ℝ) : Integrable (F a) := by
    apply (hFc a).integrable_of_hasCompactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at hcs ⊢
    exact hcs.mono (fun x hx => by change h x = 0 at hx; simp [F,hx])
  have hlt (y : ℝ) (hy : 0 < y) : w (1-y) < w (-1-y) := by
    have hsq : (1-y)^2 < (-1-y)^2 := by nlinarith
    have ha : |1-y| ≤ |-1-y| := by
      rw [abs_of_neg (show (-1-y:ℝ) < 0 by linarith)]
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha (show 0 ≤ 2*α by positivity))
    exact (mul_le_mul_of_nonneg_right he (sq_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_left (by have hp : 0 < ((-1-y)^2-(1-y)^2) * (2+(1-y)^2+(-1-y)^2) := mul_pos (sub_pos.mpr hsq) (by positivity); nlinarith only [hp] : (1+(1-y)^2)^2 < (1+(-1-y)^2)^2) (Real.exp_pos _))
  have hFlt (y : ℝ) (hy : 0 < h y) : F (-1) y < F 1 y := by
    have hy0 : 0 < y := by by_contra! e; rw [hs y e] at hy; exact lt_irrefl _ hy
    exact div_lt_div_of_pos_left hy (hw _) (hlt y hy0)
  have hd : 0 ≤ fun y => F 1 y - F (-1) y := by
    intro y
    by_cases hy : 0 < h y
    · exact (sub_pos.mpr (hFlt y hy)).le
    · have hz : h y = 0 := le_antisymm (le_of_not_gt hy) (hn y)
      simp [F,hz]
  obtain ⟨z,hz⟩ := hp
  have hi := integral_pos_of_integrable_nonneg_nonzero ((hFc 1).sub (hFc (-1)))
    ((hFi 1).sub (hFi (-1))) hd (sub_pos.mpr (hFlt z hz)).ne'
  change 0 < ∫ x : ℝ, F 1 x - F (-1) x at hi
  rw [integral_sub (hFi 1) (hFi (-1))] at hi
  have he : w (-1) = w 1 := by norm_num [w]
  rw [he]
  exact mul_lt_mul_of_pos_left (sub_pos.mp hi) (hw _)
