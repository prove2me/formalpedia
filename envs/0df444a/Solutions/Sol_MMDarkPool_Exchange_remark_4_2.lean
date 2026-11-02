-- Prove2me | solution 1 for MMDarkPool.Exchange.remark_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T01:45:39.422118+00:00
-- url     : https://prove2.me/submissions/8b607419-cbe0-4720-86ac-3c708e3e692d

import Mathlib
import Definitions.Def_MMDarkPool_Exchange_Model

open MMDarkPool.Exchange

theorem solution (P : Params) (hP : Standing P) (Lstar : Inc P → ℤ → Vol) (q : ℤ) (hq : q ∈ Grid P) (w : ℤ → ℝ) (hw : w q < 0) (z : Inc P) (zS : ℝ) (hzS : zS ≠ -(P.γ / (P.γ + P.η)) * (q : ℝ)) : Ucal P Lstar (zS, z) q w < Ucal P Lstar (-(P.γ / (P.γ + P.η)) * (q : ℝ), z) q w := by
  obtain ⟨_, _, hσ, hγ, hη, _⟩ := hP
  unfold Ucal
  simp only
  set zs := -(P.γ / (P.γ + P.η)) * (q : ℝ) with hzs
  have hge : P.γ + P.η > 0 := by linarith
  have key : (P.η / 2) * P.σ ^ 2 * P.γ * (zS + (q : ℝ)) ^ 2 + (P.η ^ 2 * P.σ ^ 2 / 2) * zS ^ 2
      - ((P.η / 2) * P.σ ^ 2 * P.γ * (zs + (q : ℝ)) ^ 2 + (P.η ^ 2 * P.σ ^ 2 / 2) * zs ^ 2)
      = (P.η / 2) * P.σ ^ 2 * (P.γ + P.η) * (zS - zs) ^ 2 := by
    rw [hzs]; field_simp; ring
  have hpos : 0 < (P.η / 2) * P.σ ^ 2 * (P.γ + P.η) * (zS - zs) ^ 2 := by
    have : (zS - zs) ^ 2 > 0 := by
      have : zS - zs ≠ 0 := sub_ne_zero.mpr hzS
      positivity
    positivity
  have : w q * ((P.η / 2) * P.σ ^ 2 * P.γ * (zS + (q : ℝ)) ^ 2 + (P.η ^ 2 * P.σ ^ 2 / 2) * zS ^ 2)
      < w q * ((P.η / 2) * P.σ ^ 2 * P.γ * (zs + (q : ℝ)) ^ 2 + (P.η ^ 2 * P.σ ^ 2 / 2) * zs ^ 2) := by
    have := mul_lt_mul_of_neg_left (show ((P.η / 2) * P.σ ^ 2 * P.γ * (zs + (q : ℝ)) ^ 2 + (P.η ^ 2 * P.σ ^ 2 / 2) * zs ^ 2) < ((P.η / 2) * P.σ ^ 2 * P.γ * (zS + (q : ℝ)) ^ 2 + (P.η ^ 2 * P.σ ^ 2 / 2) * zS ^ 2) by linarith) hw
    exact this
  linarith
