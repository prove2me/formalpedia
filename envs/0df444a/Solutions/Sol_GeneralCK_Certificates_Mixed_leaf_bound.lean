-- Prove2me | solution 1 for GeneralCK.Certificates.Mixed.leaf_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T21:06:49.888986+00:00
-- url     : https://prove2.me/submissions/f8a8997f-1d99-4144-837c-e0528e9b278f

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_MixedBounds
import Theorems.Thm_GeneralCK_Certificates_PilotData_log_two

namespace GeneralCK.Certificates.Mixed









theorem neg_log_between {l u v : ℝ} (hl : 0 < l) (hv : l ≤ v) (hu : v ≤ u) :
    -Real.log u ≤ -Real.log v ∧ -Real.log v ≤ -Real.log l := by
  have hvp : 0 < v := lt_of_lt_of_le hl hv
  constructor
  · exact neg_le_neg (Real.log_le_log hvp hu)
  · exact neg_le_neg (Real.log_le_log hl hv)



end GeneralCK.Certificates.Mixed

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.Mixed
set_option maxHeartbeats 800000 in

theorem solution {l u a b c d v : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) (hu : u < 1/2)
    (hv₀ : l ≤ v) (hv₁ : v ≤ u)
    (ha : -Real.log l ≤ a) (hb : -Real.log (1-u) ≤ b)
    (hc : c ≤ -Real.log u) (hd : d ≤ -Real.log (1-l))
    (hcpos : 0 < (c+d)/2)
    (hnumpos : 0 ≤ a+b-(1-2*u)^2)
    (hnumeric :
      2*(1-2*l)*(u*a+(1-l)*b)^2*(a+b-(1-2*u)^2) ≤
        (13/6)*((69314718/100000000 : ℝ)*(4*l*(1-u))^2*((c+d)/2)^3)) :
    profile v ≤ 13/6 := by
  have hvpos : 0 < v := lt_of_lt_of_le hl hv₀
  have hvone : v < 1 := by linarith
  have huone : u < 1 := by linarith
  have hlone : l < 1 := by linarith
  have nlv := neg_log_between hl hv₀ hv₁
  have nlc := neg_log_between (by linarith : 0 < 1-u)
    (by linarith : 1-u ≤ 1-v) (by linarith : 1-v ≤ 1-l)
  have lvpos : 0 ≤ -Real.log v := neg_nonneg.mpr (Real.log_nonpos hvpos.le hvone.le)
  have lcpos : 0 ≤ -Real.log (1-v) :=
    neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  have apos : 0 ≤ a := le_trans lvpos (le_trans nlv.2 ha)
  have bpos : 0 ≤ b := le_trans lcpos (le_trans nlc.2 hb)
  have heq : hn v = v*(-Real.log v)+(1-v)*(-Real.log (1-v)) := by unfold hn; ring
  have hpos : 0 ≤ hn v := by rw [heq]; positivity
  have hupper : hn v ≤ u*a+(1-l)*b := by
    rw [heq]
    apply add_le_add
    · exact mul_le_mul hv₁ (le_trans nlv.2 ha) lvpos (by linarith)
    · exact mul_le_mul (by linarith) (le_trans nlc.2 hb) lcpos (by linarith)
  have keq : kap v = ((-Real.log v)+(-Real.log (1-v)))/2 := by
    rw [kap, Real.log_mul (ne_of_gt hvpos) (by positivity)]
    ring
  have klower : (c+d)/2 ≤ kap v := by rw [keq]; linarith [nlv.1, nlc.1]
  have kupper : kap v ≤ (a+b)/2 := by rw [keq]; linarith [nlv.2, nlc.2]
  have kpos : 0 < kap v := lt_of_lt_of_le hcpos klower
  have rpos : 0 ≤ 1-2*v := by linarith
  have rlower : 0 ≤ 1-2*u := by linarith
  have rsq : (1-2*u)^2 ≤ (1-2*v)^2 := by nlinarith
  have facupper : 2*kap v-(1-2*v)^2 ≤ a+b-(1-2*u)^2 := by linarith
  have nu_lower : 4*l*(1-u) ≤ 4*v*(1-v) := by
    have h := mul_le_mul hv₀ (by linarith : 1-u ≤ 1-v)
      (by linarith : 0 ≤ 1-u) hvpos.le
    nlinarith
  have nupos : 0 < 4*l*(1-u) := by positivity
  have loglower : (69314718/100000000 : ℝ) ≤ Real.log 2 := by
    have h := PilotData.log_two
    norm_num at h ⊢
    linarith [h.1]
  have logpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have denpos : 0 < Real.log 2*(4*v*(1-v))^2*(kap v)^3 := by positivity
  have denlower : (69314718/100000000 : ℝ)*(4*l*(1-u))^2*((c+d)/2)^3 ≤
      Real.log 2*(4*v*(1-v))^2*(kap v)^3 := by
    gcongr
  have numupper : 2*(1-2*v)*(hn v)^2*(2*kap v-(1-2*v)^2) ≤
      2*(1-2*l)*(u*a+(1-l)*b)^2*(a+b-(1-2*u)^2) := by
    calc
      _ ≤ 2*(1-2*v)*(hn v)^2*(a+b-(1-2*u)^2) := by
        exact mul_le_mul_of_nonneg_left facupper (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hnumpos
        apply mul_le_mul
        · linarith only [hv₀]
        · exact pow_le_pow_left₀ hpos hupper 2
        · positivity
        · linarith only [hl, hlu, hu]
  unfold profile
  apply (div_le_iff₀ denpos).mpr
  exact le_trans numupper (le_trans hnumeric
    (mul_le_mul_of_nonneg_left denlower (by norm_num : (0 : ℝ) ≤ 13/6)))
