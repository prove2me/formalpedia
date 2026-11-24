-- Prove2me | solution 1 for NodeStableProj.Main.app_C_size_estimate_order_delta_le_half
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-23T23:35:07.470446+00:00
-- url     : https://prove2.me/submissions/a7d4fac6-33bf-4a5c-b661-678b5cb44cf3

import Mathlib
import Definitions.Def_NodeStableProj_Main_SizeEstimate

open MeasureTheory

theorem solution :
    ∃ C : ℝ, ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ ≤ 1 / 2 →
      (2 * NodeStableProj.Main.sizeB (ε / 2) (δ / 2) : ℝ) ≤ C * (Real.log (1 / δ) / ε) := by
  refine ⟨20, fun ε δ hε hε1 hδ hδ2 => ?_⟩
  unfold NodeStableProj.Main.sizeB
  have hL2 : Real.log 2 ≤ Real.log (1 / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; linarith)
  have hl2 := Real.log_two_gt_d9
  have h8 : Real.log (4 / (δ / 2)) = 3 * Real.log 2 + Real.log (1 / δ) := by
    rw [show (4:ℝ) / (δ / 2) = 2 ^ 3 * (1 / δ) by field_simp; norm_num,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  set L := Real.log (1 / δ) with hL
  set w := 1 / ε with hw
  have hw1 : 1 ≤ w := by rw [hw, le_div_iff₀ hε]; linarith
  have hε2 : 1 / (ε / 2) = 2 * w := by rw [hw]; field_simp
  have hLε : L / ε = L * w := by rw [hw]; ring
  rw [h8, hε2, hLε]
  have hx : 0 ≤ 2 * w * (3 * Real.log 2 + L) := mul_nonneg (by linarith) (by linarith)
  have hc := Nat.ceil_lt_add_one hx
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hL2 (by positivity : (0:ℝ) ≤ w)]
