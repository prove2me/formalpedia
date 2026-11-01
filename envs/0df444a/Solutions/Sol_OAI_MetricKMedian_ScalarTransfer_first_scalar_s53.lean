-- Prove2me | solution 1 for OAI.MetricKMedian.ScalarTransfer.first_scalar_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:17:41.414065+00:00
-- url     : https://prove2.me/submissions/4962c5e3-4a31-42df-bbac-3414100d653a

import Mathlib
import Definitions.Def_OAIQ053K027

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_NormalizedTransfer
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

private theorem reciprocal_quadratic {c t w γ : ℝ} (ht : 0 < t)
    (hc : γ^2 ≤ (8/5)*c) : γ*w ≤ c/t+(2/5)*w^2*t := by
  have hs := sq_nonneg ((4/5)*w*t-γ)
  have hpoly : γ*w*t ≤ c+(2/5)*w^2*t^2 := by nlinarith only [hs, hc]
  calc
    γ*w ≤ (c+(2/5)*w^2*t^2)/t := (le_div_iff₀ ht).mpr hpoly
    _ = c/t+(2/5)*w^2*t := by field_simp

private theorem first_gap_identity {p x w r : ℝ} (hr : r ≠ 0)
    (hx : 1+x ≠ 0) (hd : 1-p*r ≠ 0) (s : Bool) :
    c p s*(1-p)/(1-p*r) -
      (2*x*(1-p)/(1+x)-2*x*p+(2-bit s)*p*(x+w)-(2/5)*p*w^2/r) =
    c p s*(1-p)-2*x*(1-p)/(1+x)+bit s*p*x-(2-bit s)*p*w+(2/5)*p^2*w^2+
      p*(c p s*(1-p)/((1-p*r)/r)+(2/5)*w^2*((1-p*r)/r)) := by
  field_simp [hr, hx, hd]
  ring

theorem first_scalar_s53_oai {p x w m r : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hw0 : 0 ≤ w) (hw : w ≤ 1-x)
    (hr0 : 0 < r) (hr : r ≤ 1)
    (hm : (1+x)*(m+2*x*p) = 2*x*(1-p))
    (hT1 : 0 ≤ T1 p x) (hT2 : 0 ≤ T2 p x) (s : Bool) :
    m+(2-bit s)*p*(x+w)-(2/5)*(p*w^2)/r ≤ c p s*(1-p)/(1-p*r) := by
  have hxden : 0 < 1+x := by linarith
  have hpr := mul_le_mul hp hr hr0.le (by norm_num : (0:ℝ) ≤ 1/2)
  have hden : 0 < 1-p*r := by linarith
  have ht : 0 < (1-p*r)/r := div_pos hden hr0
  have hm' : m = 2*x*(1-p)/(1+x)-2*x*p := by
    have he : m+2*x*p = 2*x*(1-p)/(1+x) := (eq_div_iff hxden.ne').mpr (by nlinarith only [hm])
    linarith
  have hgap := first_gap_identity (w := w) (ne_of_gt hr0) hxden.ne' hden.ne' s
  rw [←hm'] at hgap
  have hX0 : 0 ≤ 1-x := sub_nonneg.mpr hx
  have hgam : (if s then 31/50 else 22/25 : ℝ)^2 ≤ (8/5)*(c p s*(1-p)) := by
    cases s <;> norm_num [c, bit] <;> nlinarith [sq_nonneg (p-1/2)]
  have hagm := reciprocal_quadratic (w := w) ht hgam
  have hagmp := mul_le_mul_of_nonneg_left hagm hp0
  have hrest : 0 ≤ c p s*(1-p)-2*x*(1-p)/(1+x)+bit s*p*x-
      (2-bit s)*p*w+(2/5)*p^2*w^2+p*((if s then 31/50 else 22/25)*w) := by
    cases s
    · norm_num [c, bit]
      have hsum : w+(1-x) ≤ 2 := by linarith
      have hsum0 : 0 ≤ w+(1-x) := by linarith
      have hpp := mul_le_mul hp hsum hsum0 (by norm_num : (0:ℝ) ≤ 1/2)
      have hquad := mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hw))
        (show 0 ≤ 28/25-(2/5)*p*(w+(1-x)) by linarith)
      have hnonneg : 0 ≤ (1-x)*T1 p x/(1+x) := div_nonneg (mul_nonneg hX0 hT1) hxden.le
      have hid : (1-x)*T1 p x/(1+x) =
          (1-p)-2*x*(1-p)/(1+x)-(28/25)*p*(1-x)+(2/5)*p^2*(1-x)^2 := by
        unfold T1
        field_simp
        ring
      rw [hid] at hnonneg
      nlinarith only [hnonneg, hquad]
    · norm_num [c, bit]
      have hlin := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 19/50) hp0) (sub_nonneg.mpr hw)
      have hquad : 0 ≤ (2/5)*p^2*w^2 := by positivity
      have hnonneg : 0 ≤ T2 p x/(1+x) := div_nonneg hT2 hxden.le
      have hid : T2 p x/(1+x) = (1-p)^2-2*x*(1-p)/(1+x)+p*x-(19/50)*p*(1-x) := by
        unfold T2
        field_simp
        ring
      rw [hid] at hnonneg
      nlinarith only [hnonneg, hlin, hquad]
  have hgd : 0 ≤ c p s*(1-p)/(1-p*r) -
      (m+(2-bit s)*p*(x+w)-(2/5)*p*w^2/r) := by
    rw [hgap]
    linarith only [hagmp, hrest]
  have hresult := sub_nonneg.mp hgd
  convert hresult using 1 <;> first | rfl | ring

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.ScalarTransfer.first_scalar_s53_oai := @OAI.MetricKMedian.ScalarTransfer.first_scalar_s53_oai
