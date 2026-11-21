-- Prove2me | solution 1 for MasulloRH.reference_real_resolvent_half_weight_error
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:38:52.805459+00:00
-- url     : https://prove2.me/submissions/def987fc-8a86-4f2d-83e7-c667f117f0d9

-- Quantitative remainder for the reference resolvent.
import Theorems.Thm_MasulloRH_reference_real_resolvent_sandwich
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH

theorem solution (z : ZetaZerosInTraceStrip (1/2)) :
    0 ≤ zeroDecayWeight (1/2) z / 2 - (zeroResolventTerm (1/2) 3 z).re ∧
    (1 + z.val.im^2) * (zeroDecayWeight (1/2) z / 2 - (zeroResolventTerm (1/2) 3 z).re)
      ≤ 16 * zeroDecayWeight (1/2) z := by
  refine ⟨sub_nonneg.mpr (reference_real_resolvent_sandwich z).2,?_⟩
  let u := 3-z.val.re
  let v := 5/2-z.val.re
  let t := z.val.im^2
  have hx := z.prop.2.1
  have hx' := z.prop.2.2.1
  have hu : 0 < u := by dsimp [u]; linarith
  have hv : 0 < v := by dsimp [v]; linarith
  have hu3 : u ≤ 3 := by dsimp [u]; linarith
  have hv5 : v ≤ 5/2 := by dsimp [v]; linarith
  have ht6 : 6 ≤ |z.val.im| := le_of_not_ge fun h =>
    (ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six hx hx' h) z.prop.1
  have ht : 36 ≤ t := by
    have h := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 6) ht6
    dsimp [t]; nlinarith [sq_abs z.val.im]
  have huv : u*v ≤ 15/2 := by
    have h := mul_le_mul hu3 hv5 hv.le (by norm_num : (0:ℝ) ≤ 3)
    linarith
  have hu2 := mul_self_le_mul_self hu.le hu3
  have hv2 := mul_self_le_mul_self hv.le hv5
  have hden1 : 0 < u^2+t := by nlinarith [sq_nonneg u]
  have hden2 : 0 < v^2+t := by nlinarith [sq_nonneg v]
  have hvu : u-v=1/2 := by dsimp [u,v]; ring
  have he : (zeroResolventTerm (1/2) 3 z).re =
      (analyticOrderNatAt riemannZeta z.val:ℝ) *
       ((t-u*v)/(2*((u^2+t)*(v^2+t)))) := by
    unfold zeroResolventTerm
    simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero,
      Complex.sub_re,one_div,Complex.inv_re,Complex.normSq_apply,Complex.sub_im]
    norm_num [Complex.div_ofNat_re,Complex.div_ofNat_im]
    left
    change u/(u*u+z.val.im*z.val.im)-v/(v*v+z.val.im*z.val.im) = _
    rw [show u*u+z.val.im*z.val.im=u^2+t by dsimp [t]; ring,
        show v*v+z.val.im*z.val.im=v^2+t by dsimp [t]; ring]
    field_simp [hden1.ne',hden2.ne']
    linear_combination (2*(t-u*v))*hvu
  rw [he]
  let M : ℝ := analyticOrderNatAt riemannZeta z.val
  let D := (u^2+t)*(v^2+t)
  have hD : 0 < D := mul_pos hden1 hden2
  have hd : t^2 ≤ D := by
    dsimp [D]
    nlinarith only [mul_le_mul (show t ≤ u^2+t by nlinarith [sq_nonneg u])
      (show t ≤ v^2+t by nlinarith [sq_nonneg v]) (by linarith : 0 ≤ t) hden1.le]
  have h22 : u^2+v^2+u*v-1 ≤ 22 := by nlinarith
  have h64 : u^2*v^2+u*v ≤ 64 := by
    nlinarith only [huv,mul_self_le_mul_self (mul_nonneg hu.le hv.le) huv]
  have hnum : D-(1+t)*(t-u*v) ≤ 22*t+64 := by
    dsimp [D]; nlinarith only [h64,mul_le_mul_of_nonneg_right h22 (by linarith : 0 ≤ t)]
  have hmain : (1+t)*(D-(1+t)*(t-u*v)) ≤ 32*D := by
    nlinarith only [mul_le_mul_of_nonneg_left hnum (by linarith : 0 ≤ 1+t),
      mul_nonneg (show 0 ≤ t by linarith) (show 0 ≤ t-36 by linarith),ht,hd]
  change (1+t)*(M/(1+t)/2 - M*((t-u*v)/(2*D))) ≤ 16*(M/(1+t))
  have hpos : 0 < 1+t := by linarith
  field_simp [hpos.ne', hD.ne']
  nlinarith only [mul_le_mul_of_nonneg_left hmain (show 0 ≤ M from Nat.cast_nonneg _)]
