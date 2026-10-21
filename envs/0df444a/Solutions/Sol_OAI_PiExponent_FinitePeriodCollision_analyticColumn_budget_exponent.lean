-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.analyticColumn_budget_exponent
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:00:22.58388+00:00
-- url     : https://prove2.me/submissions/045a7fd6-9a9d-4a6a-b76f-a9c9b127f53f

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic

open scoped BigOperators

theorem solution
    {m : ℕ} (h : ℕ) (a : Fin m → ℕ) (w : Fin m → ℝ)
    {R H w0 wstar : ℝ}
    (hR : 1 ≤ R) (hH : 0 ≤ H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i)
    (hcol : w0 * (h : ℝ) + ∑ i, w i * (a i : ℝ) ≤ H) :
    Real.exp ((h : ℝ) * R +
        (∑ i, w i * (a i : ℝ)) * Real.log (2 * R) / wstar) ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by
  let S : ℝ := ∑ i, w i * (a i : ℝ)
  have ha (i : Fin m) : 0 ≤ (a i : ℝ) := by positivity
  have hterm (i : Fin m) : 0 ≤ w i * (a i : ℝ) :=
    mul_nonneg (le_trans (le_of_lt hws) (hw i)) (ha i)
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ => hterm i
  have hbud : w0 * (h : ℝ) + S ≤ H := by
    simpa [S] using hcol
  have hbase : 0 ≤ w0 * (h : ℝ) := mul_nonneg hw0.le (Nat.cast_nonneg h)
  have hSle : S ≤ H := by linarith [hbase]
  have hhbound : (h : ℝ) ≤ H / w0 := by
    rw [le_div_iff₀ hw0]
    nlinarith
  have hRpos : 0 ≤ R := le_trans (by norm_num) hR
  have hlog : 0 ≤ Real.log (2 * R) :=
    Real.log_nonneg (by nlinarith)
  have hfirst : (h : ℝ) * R ≤ H * (R / w0) := by
    calc
      (h : ℝ) * R ≤ (H / w0) * R := mul_le_mul_of_nonneg_right hhbound hRpos
      _ = H * (R / w0) := by ring
  have hquot : S / wstar ≤ H / wstar :=
    div_le_div_of_nonneg_right hSle (le_of_lt hws)
  have hsecond : S * Real.log (2 * R) / wstar ≤ H * Real.log (2 * R) / wstar := by
    calc
      S * Real.log (2 * R) / wstar = (S / wstar) * Real.log (2 * R) := by
        ring
      _ ≤ (H / wstar) * Real.log (2 * R) := mul_le_mul_of_nonneg_right hquot hlog
      _ = H * Real.log (2 * R) / wstar := by
        ring
  calc
    Real.exp ((h : ℝ) * R +
        (∑ i, w i * (a i : ℝ)) * Real.log (2 * R) / wstar)
        ≤ Real.exp (H * (R / w0) + H * Real.log (2 * R) / wstar) := by
          apply Real.exp_le_exp.mpr
          simpa [S] using add_le_add hfirst hsecond
    _ = Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by
          congr 1
          ring
