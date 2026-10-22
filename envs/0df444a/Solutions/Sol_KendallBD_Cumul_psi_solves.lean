-- Prove2me | solution 1 for KendallBD.Cumul.psi_solves
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:59:32.059627+00:00
-- url     : https://prove2.me/submissions/b73c7476-f9ba-479e-bb89-7cc59b945c17

import Mathlib
import Definitions.Def_KendallBD_Cumul_Setting

set_option autoImplicit false
open Filter Topology
open KendallBD.Cumul

theorem solution (lam0 mu0 : ℝ) (hlam : 0 < lam0) (hle : lam0 ≤ mu0) :
    ∀ w ∈ Set.Ioo (0:ℝ) 1,
      (∀ z ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, 0 ≤ t → SolvesPDE lam0 mu0 (psi lam0 mu0) z w t) ∧
      ∀ z : ℝ, psi lam0 mu0 z w 0 = z * w := by
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
  have hsum : lam0 * w * (alpha lam0 mu0 w + beta lam0 mu0 w) = lam0 + mu0 := by
    rw [hα, hβ]; field_simp; ring
  have hprod : lam0 * w * (alpha lam0 mu0 w * beta lam0 mu0 w) = mu0 := by
    rw [hα, hβ]; field_simp; nlinarith [hs2]
  have hβ1 : 1 < beta lam0 mu0 w := by
    rw [hβ, lt_div_iff₀ (by positivity)]
    nlinarith
  have hq : ∀ z : ℝ, lam0 * w * z ^ 2 - (lam0 + mu0) * z + mu0
      = lam0 * w * (z - alpha lam0 mu0 w) * (z - beta lam0 mu0 w) := by
    intro z
    linear_combination z * hsum - hprod
  have hpsi : ∀ z t : ℝ, psi lam0 mu0 z w t = w * ((alpha lam0 mu0 w * (beta lam0 mu0 w - z)
        + beta lam0 mu0 w * (z - alpha lam0 mu0 w)
          * Real.exp (-lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w) * t))
      / ((beta lam0 mu0 w - z)
        + (z - alpha lam0 mu0 w)
          * Real.exp (-lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w) * t))) := fun _ _ => rfl
  generalize alpha lam0 mu0 w = A at *
  generalize beta lam0 mu0 w = B at *
  refine ⟨fun z hz t ht => ?_, fun z => ?_⟩
  · obtain ⟨hz0, hz1⟩ := hz
    simp only [SolvesPDE, hpsi]
    set c : ℝ := -lam0 * w * (B - A) with hc
    set Et : ℝ := Real.exp (c * t) with hEt
    have hEpos : 0 < Et := Real.exp_pos _
    have hE1 : Et ≤ 1 := by
      rw [hEt]; apply Real.exp_le_one_iff.2
      have : 0 < lam0 * w * (B - A) := mul_pos hlw hβαpos
      rw [hc]; nlinarith
    have hu : 0 < B - z := by linarith
    have hD : 0 < (B - z) + (z - A) * Et := by
      rcases le_or_gt A z with h | h
      · nlinarith [mul_nonneg (sub_nonneg.2 h) hEpos.le]
      · nlinarith [mul_nonneg (sub_nonneg.2 h.le) (sub_nonneg.2 hE1)]
    have hDne : (B - z) + (z - A) * Et ≠ 0 := hD.ne'
    have hEd : HasDerivAt (fun s => Real.exp (c * s)) (Et * c) t := by
      have := ((hasDerivAt_id t).const_mul c).exp
      simpa [hEt, mul_comm] using this
    have hNt : HasDerivAt (fun s => A * (B - z) + B * (z - A) * Real.exp (c * s))
        (B * (z - A) * (Et * c)) t := (hEd.const_mul (B * (z - A))).const_add (A * (B - z))
    have hDt : HasDerivAt (fun s => (B - z) + (z - A) * Real.exp (c * s))
        ((z - A) * (Et * c)) t := (hEd.const_mul (z - A)).const_add (B - z)
    have hPt := (hNt.div hDt hDne).const_mul w
    have hNz : HasDerivAt (fun y => A * (B - y) + B * (y - A) * Et) (A * (-1) + B * Et) z := by
      have h1 : HasDerivAt (fun y : ℝ => B - y) (-1) z := by
        simpa using (hasDerivAt_id z).const_sub B
      have h2 : HasDerivAt (fun y : ℝ => (y - A) * Et) (Et) z := by
        simpa using ((hasDerivAt_id z).sub_const A).mul_const Et
      have := (h1.const_mul A).add (h2.const_mul B)
      have e : (fun y : ℝ => A * (B - y) + B * (y - A) * Et)
          = (fun y : ℝ => A * (B - y) + B * ((y - A) * Et)) := by funext y; ring
      rw [e]; exact this
    have hDz : HasDerivAt (fun y => (B - y) + (y - A) * Et) (-1 + Et) z := by
      have h1 : HasDerivAt (fun y : ℝ => B - y) (-1) z := by
        simpa using (hasDerivAt_id z).const_sub B
      have h2 : HasDerivAt (fun y : ℝ => (y - A) * Et) (Et) z := by
        simpa using ((hasDerivAt_id z).sub_const A).mul_const Et
      exact h1.add h2
    have hPz := (hNz.div hDz hDne).const_mul w
    refine ⟨_, _, hPt, hPz, ?_⟩
    beta_reduce
    rw [← hEt, hq z]
    clear_value Et
    field_simp
    rw [hc]
    ring
  · simp only [hpsi, mul_zero, Real.exp_zero]
    have : (B - z) + (z - A) * 1 = B - A := by ring
    rw [this]
    have h2 : B - A ≠ 0 := hβαpos.ne'
    field_simp
    ring
