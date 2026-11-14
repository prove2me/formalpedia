-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_weight_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:35:43.8782+00:00
-- url     : https://prove2.me/submissions/ff8db7d6-1d53-4a5e-8a67-db723c507f44

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect

theorem solution (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) : c0*fW q ≤ gW q := by
  have h1q : 0 ≤ 1-q := by linarith
  let s := Real.sqrt q
  let t := Real.sqrt (1-q)
  let r := Real.sqrt 2
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hs2 : s^2=q := Real.sq_sqrt hq
  have ht2 : t^2=1-q := Real.sq_sqrt h1q
  have hr2 : r^2=2 := Real.sq_sqrt (by norm_num)
  have hr1 : 1 ≤ r := by nlinarith
  have hst : s+t ≤ r := by nlinarith [sq_nonneg (s-t)]
  have hden : 0 < 1+s+t := by linarith
  have hbase : (s+t-1)*(s+t+1)=2*s*t := by nlinarith [hs2,ht2]
  have hlim : (r-1)*(s+t+1) ≤ 1 := by
    have hh := mul_nonneg (show 0 ≤ r-1 by linarith) (show 0 ≤ r-(s+t) by linarith)
    nlinarith [hr2]
  have hfac := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hs) ht)
    (show 0 ≤ 1-(r-1)*(s+t+1) by linarith)
  have hident : (s+t+1)*((s+t-1)-2*(r-1)*s*t) =
      2*s*t*(1-(r-1)*(s+t+1)) := by nlinarith [hbase]
  have hlow : 2*(r-1)*s*t ≤ s+t-1 := by nlinarith [hfac,hident]
  have hroot : Real.sqrt (q*(1-q)) = s*t := Real.sqrt_mul hq _
  unfold c0 fW gW
  rw [hroot]
  change 2*(r-1)*(2*(s*t)) ≤ 2*(s+t-1)
  nlinarith
