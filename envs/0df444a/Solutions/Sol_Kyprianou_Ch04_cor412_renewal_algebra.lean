-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_renewal_algebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:32:31.761276+00:00
-- url     : https://prove2.me/submissions/acffbd19-6adb-4a47-8e6a-97423aa25799

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution (m d β ψ W K : ℝ)
    (hm : 0 < m) (hd : 0 < d) (hβ : 0 < β) (hψ : 0 < ψ)
    (hW : W = m * β / ψ) (hrenew : W = m / d + K * W) :
    K = 1 - ψ / (d * β) := by
  have hpos : 0 < W := hW.symm ▸ div_pos (mul_pos hm hβ) hψ
  have hK : K = (W - m / d) / W := by
    apply (eq_div_iff hpos.ne').2
    linarith
  rw [hK, hW]
  field_simp [hm.ne', hd.ne', hβ.ne', hψ.ne']
  <;> ring
