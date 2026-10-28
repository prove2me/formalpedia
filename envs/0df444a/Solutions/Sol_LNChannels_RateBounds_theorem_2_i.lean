-- Prove2me | solution 1 for LNChannels.RateBounds.theorem_2_i
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:24:03.271546+00:00
-- url     : https://prove2.me/submissions/26fc4d05-8e7a-48f9-b190-1a72a276cccd

import Mathlib
import Definitions.Def_LNChannels_RateBounds_ClosedForms

-- carved verbatim out of submission a1c4d4e7-4e3f-4620-b945-0b2e7fa15711, lines 105-144

section
set_option autoImplicit false

lemma log_bound (u c : ℝ) (hu : 0 < u) (hc : 0 < c) :
    Real.log (1 + c) < Real.log (1 + u) + c / u := by
  have h1 : Real.log ((1 + c) / (1 + u)) ≤ (1 + c) / (1 + u) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by positivity)] at h1
  have h2 : (1 + c) / (1 + u) - 1 < c / u := by
    rw [div_sub_one (by positivity), div_lt_div_iff₀ (by positivity) hu]
    nlinarith
  linarith

theorem solution (lam r B C : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hB : 0 < B) :
    (∃ m : ℝ, 0 < m ∧ LNChannels.Exact.uniCost lam r B m < lam * C / r) →
        Real.log (1 + B * Real.log (1 + r / lam)) < C := by
  rintro ⟨m, hm, hc⟩
  unfold LNChannels.Exact.uniCost at hc
  have hq : (r + lam) / lam = 1 + r / lam := by field_simp; ring
  rw [hq] at hc
  have hrl : 0 < r / lam := div_pos hr hlam
  set a := Real.log (1 + r / lam) with ha
  have ha0 : 0 < a := Real.log_pos (by linarith)
  have hal : a < r / lam := by
    have := Real.log_lt_sub_one_of_pos (by linarith : (0:ℝ) < 1 + r / lam) (by linarith)
    linarith
  have hpow : (1 + r / lam) ^ m = Real.exp (a * m) := Real.rpow_def_of_pos (by linarith) m
  rw [hpow] at hc
  have hu0 : 0 < Real.exp (a * m) - 1 := by
    have ham : 0 < a * m := by positivity
    have := Real.add_one_lt_exp ham.ne'; linarith
  set u := Real.exp (a * m) - 1 with hu
  have h1u : 1 + u = Real.exp (a * m) := by rw [hu]; ring
  have hlog : Real.log (1 + u) = a * m := by rw [h1u, Real.log_exp]
  have hk := log_bound u (a * B) hu0 (by positivity)
  rw [hlog] at hk
  have hc' : a * m + a * B / u < a * (lam * C / r) := by
    have e : a * m + a * B / u = a * (m + B * u⁻¹) := by ring
    rw [e]; exact mul_lt_mul_of_pos_left hc ha0
  have hL : 0 < Real.log (1 + a * B) := Real.log_pos (by nlinarith)
  have hC : 0 < C := by
    by_contra h
    push_neg at h
    have : lam * C / r ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hlam.le h) hr.le
    nlinarith
  have hal' : a * lam < r := by rwa [lt_div_iff₀ hlam] at hal
  have hfin : a * (lam * C / r) < C := by
    rw [mul_div_assoc', div_lt_iff₀ hr]
    nlinarith [mul_lt_mul_of_pos_right hal' hC]
  rw [mul_comm B a]
  linarith

end
