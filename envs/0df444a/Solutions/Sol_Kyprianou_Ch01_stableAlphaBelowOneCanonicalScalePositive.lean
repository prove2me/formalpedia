-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaBelowOneCanonicalScalePositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:27:20.065665+00:00
-- url     : https://prove2.me/submissions/c5265bed-2579-4048-813b-160b26acae83

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaBelowOneGammaRecurrence
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Set
set_option autoImplicit false

theorem solution
    (alpha cpos cneg : ℝ)
    (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hsum : 0 < cpos + cneg) :
    0 < -Real.Gamma (-alpha) *
      Real.cos (Real.pi * alpha / 2) * (cpos + cneg) := by
  have hGpos : 0 < Real.Gamma (1 - alpha) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hrec :=
    Kyprianou.Ch01.stableAlphaBelowOneGammaRecurrence alpha ha0 ha1
  have hprod : 0 < -alpha * Real.Gamma (-alpha) := by
    rw [← hrec]
    exact hGpos
  have hGneg : Real.Gamma (-alpha) < 0 := by
    by_contra hn
    have hGn : 0 ≤ Real.Gamma (-alpha) := le_of_not_gt hn
    have hnonpos : -alpha * Real.Gamma (-alpha) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hGn
    linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hphase0 : 0 < Real.pi * alpha / 2 := by positivity
  have hphase1 : Real.pi * alpha / 2 < Real.pi / 2 := by
    nlinarith [mul_lt_mul_of_pos_left ha1 hpi]
  have hcos : 0 < Real.cos (Real.pi * alpha / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hphase1⟩
  exact mul_pos (mul_pos (neg_pos.mpr hGneg) hcos) hsum
