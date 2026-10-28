-- Prove2me | solution 1 for MultivarScores.L2Rule.smooth_ae_eq_of_L2div_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:56:26.586675+00:00
-- url     : https://prove2.me/submissions/4f3447ab-9381-41b2-866f-366ab2652af1

import Mathlib
import Definitions.Def_MultivarScores_L2Rule_Setting

open MeasureTheory MultivarScores.L2Rule

theorem solution {d : ℕ} (PX PY : Measure (E d)) (w h : E d → ℝ)
    (h_nonneg : ∀ z, 0 ≤ h z) (h_ne : ∀ᵐ z, h z ≠ 0)
    (hint : Integrable (fun z => (smooth PX w z - smooth PY w z) ^ 2 * h z))
    (h0 : L2div PX PY w h = 0) :
    smooth PX w =ᵐ[volume] smooth PY w := by
  unfold L2div at h0
  have hnn : 0 ≤ᵐ[volume] (fun z => (smooth PX w z - smooth PY w z) ^ 2 * h z) :=
    Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (h_nonneg z)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0
  filter_upwards [hz, h_ne] with z hz1 hz2
  have : (smooth PX w z - smooth PY w z) ^ 2 = 0 := by
    simpa [hz2] using hz1
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  linarith
