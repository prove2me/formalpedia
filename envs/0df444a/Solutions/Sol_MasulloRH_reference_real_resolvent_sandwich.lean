-- Prove2me | solution 1 for MasulloRH.reference_real_resolvent_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:02:24.721385+00:00
-- url     : https://prove2.me/submissions/9001dc26-64c4-4ccc-9427-e00de70c20ee

-- New two-sided estimate; the factorization uses the reference points 3 and 5/2.
import Theorems.Thm_MasulloRH_reference_resolvent_le_half_decay_weight
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH

theorem solution (z : ZetaZerosInTraceStrip (1/2)) :
    zeroDecayWeight (1/2) z / 4 ≤ (zeroResolventTerm (1/2) 3 z).re ∧
    (zeroResolventTerm (1/2) 3 z).re ≤ zeroDecayWeight (1/2) z / 2 := by
  refine ⟨?_,(Complex.re_le_norm _).trans (reference_resolvent_le_half_decay_weight z)⟩
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
  have ha : u^2+t ≤ 5*t/4 := by nlinarith
  have hb : v^2+t ≤ 6*t/5 := by nlinarith
  have hd := mul_le_mul ha hb (by nlinarith [sq_nonneg v]) (by linarith)
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
  change (analyticOrderNatAt riemannZeta z.val:ℝ)/(1+t)/4 ≤ _
  rw [div_div,div_eq_mul_one_div]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply (div_le_div_iff₀ (by positivity : 0 < (1+t)*4) (by positivity)).mpr
  have hxprod := mul_le_mul_of_nonneg_right (show 3*t/4 ≤ t-u*v by linarith) (by linarith : 0 ≤ 4*(1+t))
  nlinarith only [hd,hxprod,ht]
