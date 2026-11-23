-- Prove2me | solution 1 for GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:35.31981+00:00
-- url     : https://prove2.me/submissions/19ed125c-5723-4a09-97d7-74b84268e2ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConstMulRpowMulLogPowLeRpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real Filter Asymptotics
open GlobalTheory
open Real Filter Asymptotics
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ a b C : ℝ, ∀ p : ℕ, a < b →
      ∃ x0 : ℝ, ∀ x ≥ x0, C * x ^ a * Real.log x ^ p ≤ x ^ b := by
  intro a b C p hab
  have hlo : (fun x : ℝ => Real.log x ^ (p : ℝ)) =o[atTop] fun x => x ^ (b - a) :=
    isLittleO_log_rpow_rpow_atTop _ (sub_pos.mpr hab)
  have hc : (0 : ℝ) < 1 / (|C| + 1) := by positivity
  have hev := (hlo.bound hc).and (eventually_gt_atTop (0 : ℝ))
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp hev
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨hb, hxpos⟩ := hx0 x hx
  rw [Real.rpow_natCast] at hb
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hxpos a
  have hxba : 0 < x ^ (b - a) := Real.rpow_pos_of_pos hxpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxba] at hb
  have hsplit : x ^ b = x ^ a * x ^ (b - a) := by
    rw [← Real.rpow_add hxpos]; ring_nf
  have h1 : C * Real.log x ^ p ≤ |C| * |Real.log x ^ p| := by
    rw [← abs_mul]; exact le_abs_self _
  have h2 : |C| * |Real.log x ^ p| ≤ x ^ (b - a) := by
    calc |C| * |Real.log x ^ p| ≤ (|C| + 1) * |Real.log x ^ p| := by
          gcongr; linarith
      _ ≤ (|C| + 1) * (1 / (|C| + 1) * x ^ (b - a)) := by gcongr
      _ = x ^ (b - a) := by field_simp
  calc C * x ^ a * Real.log x ^ p = x ^ a * (C * Real.log x ^ p) := by ring
    _ ≤ x ^ a * x ^ (b - a) := by gcongr; linarith
    _ = x ^ b := hsplit.symm
end _root_.GlobalTheory
end GlobalTheory
