-- Prove2me | solution 1 for KendallBD.Cumul.psi_limit
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:55:58.884329+00:00
-- url     : https://prove2.me/submissions/f287d30d-a969-4175-b3e1-cd22874b48b4

import Mathlib
import Definitions.Def_KendallBD_Cumul_Setting

set_option autoImplicit false
open Filter Topology
open KendallBD.Cumul

theorem solution (lam0 mu0 : ℝ) (hlam : 0 < lam0) (hle : lam0 ≤ mu0) :
    ∀ w ∈ Set.Ioo (0:ℝ) 1,
      Tendsto (fun t => psi lam0 mu0 1 w t) atTop (𝓝 (w * alpha lam0 mu0 w)) ∧
      w * alpha lam0 mu0 w
        = (lam0 + mu0 - Real.sqrt ((lam0 + mu0) ^ 2 - 4 * lam0 * mu0 * w)) / (2 * lam0) := by
  intro w hw
  obtain ⟨hw0, hw1⟩ := hw
  have hμ : 0 < mu0 := lt_of_lt_of_le hlam hle
  have hdpos : 0 < (lam0 + mu0) ^ 2 - 4 * lam0 * mu0 * w := by
    nlinarith [mul_pos (mul_pos hlam hμ) (sub_pos.2 hw1), sq_nonneg (lam0 - mu0)]
  set s := Real.sqrt ((lam0 + mu0) ^ 2 - 4 * lam0 * mu0 * w) with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hdpos
  have hs2 : s ^ 2 = (lam0 + mu0) ^ 2 - 4 * lam0 * mu0 * w := Real.sq_sqrt hdpos.le
  have hlw : 0 < lam0 * w := mul_pos hlam hw0
  have hα : alpha lam0 mu0 w = (lam0 + mu0 - s) / (2 * lam0 * w) := rfl
  have hβ : beta lam0 mu0 w = (lam0 + mu0 + s) / (2 * lam0 * w) := rfl
  have hβα : beta lam0 mu0 w - alpha lam0 mu0 w = s / (lam0 * w) := by
    rw [hα, hβ]; field_simp; ring
  have hβαpos : 0 < beta lam0 mu0 w - alpha lam0 mu0 w := by
    rw [hβα]; positivity
  have hroot : lam0 * w * beta lam0 mu0 w ^ 2 - (lam0 + mu0) * beta lam0 mu0 w + mu0 = 0 := by
    rw [hβ]; field_simp; nlinarith [hs2]
  have hβ1 : beta lam0 mu0 w - 1 ≠ 0 := by
    intro h
    have : beta lam0 mu0 w = 1 := by linarith
    rw [this] at hroot
    have : lam0 * (w - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  refine ⟨?_, ?_⟩
  · have hE : Tendsto (fun t : ℝ => Real.exp (-lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w) * t))
        atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      apply Tendsto.const_mul_atTop_of_neg _ tendsto_id
      have : 0 < lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w) := mul_pos hlw hβαpos
      linarith
    have hne : (beta lam0 mu0 w - 1) + (1 - alpha lam0 mu0 w) * 0 ≠ 0 := by simpa using hβ1
    have h := (((tendsto_const_nhds (x := alpha lam0 mu0 w * (beta lam0 mu0 w - 1))).add
        ((tendsto_const_nhds (x := beta lam0 mu0 w * (1 - alpha lam0 mu0 w))).mul hE)).div
      ((tendsto_const_nhds (x := beta lam0 mu0 w - 1)).add
        ((tendsto_const_nhds (x := 1 - alpha lam0 mu0 w)).mul hE)) hne).const_mul w
    have e : w * ((alpha lam0 mu0 w * (beta lam0 mu0 w - 1) +
        beta lam0 mu0 w * (1 - alpha lam0 mu0 w) * 0) /
        ((beta lam0 mu0 w - 1) + (1 - alpha lam0 mu0 w) * 0)) = w * alpha lam0 mu0 w := by
      field_simp; ring
    rw [e] at h
    refine h.congr fun t => ?_
    simp only [psi, Pi.div_apply]
  · rw [hα]
    field_simp
