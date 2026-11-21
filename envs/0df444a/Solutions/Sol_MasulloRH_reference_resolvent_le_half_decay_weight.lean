-- Prove2me | solution 1 for MasulloRH.reference_resolvent_le_half_decay_weight
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:55:59.349119+00:00
-- url     : https://prove2.me/submissions/f5fc107c-7323-4833-b3be-af5dcb8fa993

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH

theorem solution (ρ : ZetaZerosInTraceStrip (1/2)) :
    ‖zeroResolventTerm (1/2) 3 ρ‖ ≤ zeroDecayWeight (1/2) ρ / 2 := by
  let z := ρ.val
  have hzr : z.re < 1 := ρ.prop.2.2.1
  have hd (u : ℝ) (hu : 2 ≤ u) : 1 + z.im^2 ≤ ‖(u:ℂ)-z‖^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im,Complex.ofReal_im,zero_sub]
    nlinarith [mul_nonneg (show 0 ≤ u-z.re-1 by linarith) (show 0 ≤ u-z.re+1 by linarith)]
  have h3 : 1 + z.im^2 ≤ ‖3-z‖^2 := by simpa using hd 3 (by norm_num)
  have h5 : 1 + z.im^2 ≤ ‖5/2-z‖^2 := by convert hd (5/2) (by norm_num) using 1 <;> norm_num
  have hm : 1+z.im^2 ≤ ‖3-z‖*‖5/2-z‖ := by
    rcases le_total ‖3-z‖ ‖5/2-z‖ with h | h
    · nlinarith [mul_le_mul_of_nonneg_left h (norm_nonneg (3-z))]
    · nlinarith [mul_le_mul_of_nonneg_right h (norm_nonneg (5/2-z))]
  have ha0 : 0 < ‖3-z‖ := by by_contra! h; have := le_antisymm h (norm_nonneg _); rw [this] at h3; nlinarith [sq_nonneg z.im]
  have hb0 : 0 < ‖5/2-z‖ := by by_contra! h; have := le_antisymm h (norm_nonneg _); rw [this] at h5; nlinarith [sq_nonneg z.im]
  have hid : 1/(3-z) - 1/(5/2-z) = (-1/2)/((3-z)*(5/2-z)) := by
    rw [div_sub_div _ _ (norm_pos_iff.mp ha0) (norm_pos_iff.mp hb0)]
    congr 1
    ring
  change ‖(analyticOrderNatAt riemannZeta z : ℂ) * _‖ ≤ _
  rw [hid, norm_mul, Complex.norm_natCast, norm_div, norm_mul]
  change _ ≤ (analyticOrderNatAt riemannZeta z : ℝ)/(1+z.im^2)/2
  rw [show ‖(-1/2 : ℂ)‖ = (1/2 : ℝ) by norm_num [norm_div]]
  have h := one_div_le_one_div_of_le (by positivity : 0 < 1+z.im^2) hm
  have hh := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α:=ℝ) (analyticOrderNatAt riemannZeta z))
  simp only [div_eq_mul_inv, one_mul] at hh ⊢
  calc
    _ = ((analyticOrderNatAt riemannZeta z : ℝ) * (‖3-z‖ * ‖5/2-z‖)⁻¹) * 2⁻¹ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hh (by norm_num)
