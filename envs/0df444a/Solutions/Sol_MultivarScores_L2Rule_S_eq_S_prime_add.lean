-- Prove2me | solution 1 for MultivarScores.L2Rule.S_eq_S_prime_add
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:11:12.528975+00:00
-- url     : https://prove2.me/submissions/bbb1c02a-6211-43d6-8038-3b21e7303437

import Mathlib
import Definitions.Def_MultivarScores_L2Rule_Setting

set_option autoImplicit false
open MeasureTheory MultivarScores.L2Rule

theorem solution {d : ℕ} (P : Measure (E d)) (w h : E d → ℝ) (y : E d)
    (h_sq_smooth : Integrable (fun z => smooth P w z ^ 2 * h z))
    (h_sq_w : Integrable (fun z => w (z - y) ^ 2 * h z))
    (h_cross : Integrable (fun z => smooth P w z * w (z - y) * h z)) :
    S P w h y = S' P w h y + ∫ z, w (z - y) ^ 2 * h z := by
  unfold S S'
  have hfun : (fun z => (smooth P w z - w (z - y)) ^ 2 * h z) =
      fun z => (smooth P w z ^ 2 * h z - 2 * (smooth P w z * w (z - y) * h z)) +
        w (z - y) ^ 2 * h z := by
    funext z; ring
  have i2 : Integrable (fun z => 2 * (smooth P w z * w (z - y) * h z)) := h_cross.const_mul 2
  have i1 : Integrable (fun z => smooth P w z ^ 2 * h z - 2 * (smooth P w z * w (z - y) * h z)) :=
    h_sq_smooth.sub i2
  rw [hfun, integral_add i1 h_sq_w, integral_sub h_sq_smooth i2, integral_const_mul]
