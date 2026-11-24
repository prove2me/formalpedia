-- Prove2me | solution 1 for GlobalTheory.GaussCoset.exp_le_inv_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:10:04.280189+00:00
-- url     : https://prove2.me/submissions/583f1891-1219-4415-bc7d-9191aacbb0ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.GaussCoset
namespace GlobalTheory.GaussCoset
theorem _root_.solution {c : ℝ} (hc : 0 < c) (R : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-c * t ^ 2 + R * t) ≤
      ((n.factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c))) * t⁻¹ ^ n := by
  have hsq : 0 ≤ (2 * c * t - (R + 1)) ^ 2 / (4 * c) := by positivity
  have hid : (2 * c * t - (R + 1)) ^ 2 / (4 * c) =
      (R + 1) ^ 2 / (4 * c) - t - (-c * t ^ 2 + R * t) := by
    field_simp
    ring
  have h1 : Real.exp (-c * t ^ 2 + R * t) ≤
      Real.exp ((R + 1) ^ 2 / (4 * c)) * Real.exp (-t) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-t) ≤ (n.factorial : ℝ) * t⁻¹ ^ n := by
    have hpos : 0 < t ^ n / (n.factorial : ℝ) := by positivity
    have hle : t ^ n / (n.factorial : ℝ) ≤ Real.exp t := Real.pow_div_factorial_le_exp t ht.le n
    rw [Real.exp_neg, inv_pow, ← div_eq_mul_inv, ← inv_div]
    exact inv_anti₀ hpos hle
  calc Real.exp (-c * t ^ 2 + R * t)
      ≤ Real.exp ((R + 1) ^ 2 / (4 * c)) * Real.exp (-t) := h1
    _ ≤ Real.exp ((R + 1) ^ 2 / (4 * c)) * ((n.factorial : ℝ) * t⁻¹ ^ n) := by gcongr
    _ = ((n.factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c))) * t⁻¹ ^ n := by ring
end GlobalTheory.GaussCoset
