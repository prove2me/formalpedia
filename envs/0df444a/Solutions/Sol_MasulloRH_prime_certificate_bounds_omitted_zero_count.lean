-- Prove2me | solution 1 for MasulloRH.prime_certificate_bounds_omitted_zero_count
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:38:35.703178+00:00
-- url     : https://prove2.me/submissions/d59a33be-2582-480c-88b8-4059648e47f0

import Theorems.Thm_MasulloRH_critical_line_certificate_bounds_missing_zero_mass
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Mathlib
open ArithmeticFunction MasulloRH

theorem solution (N : ℕ) (hN : 1 ≤ N)
    (F : Finset (ZetaZerosInTraceStrip (1/2))) (hF : ∀ z ∈ F, z.val.re = 1/2)
    (hcert : Real.log 2/2 + Real.pi/4 - 37/30 +
      (∑ j ∈ Finset.range (N+1), (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))) ≤
      ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4))))
    (H : ℝ) (S : Finset (ZetaZerosInTraceStrip (1/2)))
    (hS : ∀ z ∈ S, z ∉ F ∧ |z.val.im| ≤ H) :
    (∑ z ∈ S, (analyticOrderNatAt riemannZeta z.val:ℝ)) * (N:ℝ)^(3/2:ℝ) ≤
      384*(1+H^2) := by
  classical
  let w := fun z : ZetaZerosInTraceStrip (1/2) => if z ∈ F then 0 else zeroDecayWeight (1/2) z
  have hnon (z : ZetaZerosInTraceStrip (1/2)) : 0 ≤ w z := by
    dsimp [w]; split_ifs <;> first | exact le_rfl | change 0 ≤ (_:ℝ)/(1+z.val.im^2); positivity
  have hsum : Summable w := by
    have h := (weighted_zero_summability (1/2) (by norm_num)).indicator (↑F : Set _ )ᶜ
    apply h.congr
    intro z
    by_cases hz : z ∈ F <;> simp [w,Set.indicator_apply,hz]
  have hm := (critical_line_certificate_bounds_missing_zero_mass N hN F hF hcert).1
  have htot : ∑ z ∈ S, w z ≤ 384/(N:ℝ)^(3/2:ℝ) :=
    (hsum.sum_le_tsum S (fun z _ => hnon z)).trans hm
  have hd : 0 < 1+H^2 := by positivity
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : (∑ z ∈ S, (analyticOrderNatAt riemannZeta z.val:ℝ))/(1+H^2) ≤ 384/(N:ℝ)^(3/2:ℝ) := by
    rw [Finset.sum_div]
    apply le_trans _ htot
    apply Finset.sum_le_sum
    intro z hz
    rw [show w z = zeroDecayWeight (1/2) z by simp [w,(hS z hz).1]]
    change _ ≤ (_:ℝ)/(1+z.val.im^2)
    have hy := mul_self_le_mul_self (abs_nonneg _) (hS z hz).2
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [sq_abs z.val.im]
  exact (div_le_div_iff₀ hd (by positivity)).mp hc
