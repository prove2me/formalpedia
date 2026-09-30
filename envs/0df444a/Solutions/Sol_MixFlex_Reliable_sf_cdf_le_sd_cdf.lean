-- Prove2me | solution 1 for MixFlex.Reliable.sf_cdf_le_sd_cdf
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:15:39.158383+00:00
-- url     : https://prove2.me/submissions/455699d0-45cc-41c3-82f1-d1ba3b9378e6

import Mathlib
import Definitions.Def_MixFlex_Reliable_Model

open MeasureTheory
set_option autoImplicit false
open MixFlex.Reliable
theorem solution (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (hS : Setting μ X)
    (K : Fin N → ℝ) (w : ℝ) :
    μ.real {ω | wealthSF P X P.c (∑ n, K n) ω ≤ w} ≤ μ.real {ω | wealthSD P X K ω ≤ w} := by
  letI := hS.prob
  apply measureReal_mono
  intro ω hω
  have hm : (∑ n, min (X ω n) (K n)) ≤ min (∑ n, X ω n) (∑ n, K n) :=
    le_min (Finset.sum_le_sum fun n _ => min_le_left _ _)
      (Finset.sum_le_sum fun n _ => min_le_right _ _)
  have hp := mul_le_mul_of_nonneg_left hm hP.p_pos.le
  change wealthSF P X P.c (∑ n, K n) ω ≤ w at hω
  change wealthSD P X K ω ≤ w
  dsimp [wealthSF, wealthSD] at *
  linarith
  exact measure_ne_top _ _

