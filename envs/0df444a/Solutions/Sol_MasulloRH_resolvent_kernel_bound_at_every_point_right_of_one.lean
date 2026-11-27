-- Prove2me | solution 1 for MasulloRH.resolvent_kernel_bound_at_every_point_right_of_one
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T03:24:07.570069+00:00
-- url     : https://prove2.me/submissions/53016975-e314-444e-8fdd-787b0796d506

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MasulloRH

theorem solution (s : ℂ) (hs : 1 < s.re) (z : ZetaZerosInTraceStrip (1 / 2)) :
    ‖zeroResolventTerm (1 / 2) s z‖ ≤
      ‖s - 5 / 2‖ * (1 + ‖s - 5 / 2‖ / (s.re - 1)) * zeroDecayWeight (1 / 2) z := by
  let a : ℂ := 5 / 2
  let d := ‖s - a‖
  let x := ‖s - z.val‖
  let y := ‖a - z.val‖
  let h := s.re - 1
  let w := 1 + z.val.im ^ 2
  have hh : 0 < h := sub_pos.mpr hs
  have hd : 0 ≤ d := norm_nonneg _
  have ha : a.re = 5 / 2 := by norm_num [a, Complex.div_ofNat_re]
  have hai : a.im = 0 := by norm_num [a, Complex.div_ofNat_im]
  have hx : h ≤ x := calc
    h ≤ (s - z.val).re := by simp only [Complex.sub_re]; dsimp [h]; linarith [z.prop.2.2.1]
    _ ≤ x := Complex.re_le_norm _
  have hxpos := hh.trans_le hx
  have hypos : 0 < y := lt_of_lt_of_le (show 0 < (a-z.val).re by
    rw [Complex.sub_re, ha]; linarith [z.prop.2.2.1]) (Complex.re_le_norm _)
  have hw : 0 < w := by dsimp [w]; positivity
  have hy2 : w ≤ y*y := by
    change 1 + z.val.im^2 ≤ ‖a-z.val‖ * ‖a-z.val‖
    rw [← sq, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, ha, hai]
    have hr : (1:ℝ) ≤ 5/2-z.val.re := by linarith [z.prop.2.2.1]
    nlinarith only [mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1) hr]
  have hxy : y ≤ x+d := calc
    ‖a-z.val‖ = ‖(s-z.val)-(s-a)‖ := by congr 1; ring
    _ ≤ x+d := norm_sub_le _ _
  have hdle : d ≤ (d/h)*x := calc
    d = (d/h)*h := (div_mul_cancel₀ _ hh.ne').symm
    _ ≤ (d/h)*x := mul_le_mul_of_nonneg_left hx (div_nonneg hd hh.le)
  have hwle : w ≤ (1+d/h)*(x*y) := calc
    w ≤ y*y := hy2
    _ ≤ (x+d)*y := mul_le_mul_of_nonneg_right hxy hypos.le
    _ ≤ (1+d/h)*(x*y) := by nlinarith only [mul_le_mul_of_nonneg_right hdle hypos.le]
  have hr : 1/(x*y) ≤ (1+d/h)/w :=
    (div_le_div_iff₀ (mul_pos hxpos hypos) hw).mpr (by linarith only [hwle])
  have hsz : s-z.val ≠ 0 := norm_pos_iff.mp hxpos
  have haz : a-z.val ≠ 0 := norm_pos_iff.mp hypos
  have identity : 1/(s-z.val) - 1/(a-z.val) = (a-s)/((s-z.val)*(a-z.val)) := by
    field_simp [hsz,haz]
    ring
  let m : ℝ := analyticOrderNatAt riemannZeta z.val
  have hm : 0 ≤ m := Nat.cast_nonneg _
  calc
    ‖zeroResolventTerm (1/2) s z‖ = (m*d)*(1/(x*y)) := by
      unfold zeroResolventTerm
      change ‖(analyticOrderNatAt riemannZeta z.val : ℂ) * (1/(s-z.val)-1/(a-z.val))‖ = _
      rw [identity, norm_mul, Complex.norm_natCast, norm_div, norm_mul, norm_sub_rev a s]
      change m * (d/(x*y)) = _
      ring
    _ ≤ (m*d)*((1+d/h)/w) := mul_le_mul_of_nonneg_left hr (mul_nonneg hm hd)
    _ = _ := by change (m*d)*((1+d/h)/w) = d*(1+d/h)*(m/w); ring
