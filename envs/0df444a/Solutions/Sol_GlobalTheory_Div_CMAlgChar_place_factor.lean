-- Prove2me | solution 1 for GlobalTheory.Div.CMAlgChar.place_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:23:45.755339+00:00
-- url     : https://prove2.me/submissions/58e36fe8-636b-4444-b6d7-f40e52b6e4e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmAlgCharEqArgMulAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.CMAlgChar
namespace GlobalTheory.Div.CMAlgChar
theorem _root_.solution (z : ℂ) (hz : z ≠ 0) (a b w0 : ℤ) (hab : a + b = w0) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * a - w0) *
      (((‖z‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ) *
        ((‖(starRingEnd ℂ) z‖ : ℝ) : ℂ) ^ ((((w0 : ℝ) / 2 : ℝ)) : ℂ)) =
      z ^ a * (starRingEnd ℂ z) ^ b := by
  rw [Complex.norm_conj]
  set r : ℂ := ((‖z‖ : ℝ) : ℂ) with hr
  have hr0 : r ≠ 0 := by simp [hr, hz]
  rw [← Complex.cpow_add _ _ hr0]
  have hsum : ((((w0 : ℝ) / 2 : ℝ)) : ℂ) + ((((w0 : ℝ) / 2 : ℝ)) : ℂ) = ((w0 : ℤ) : ℂ) := by
    push_cast; ring
  rw [hsum, Complex.cpow_intCast]
  have hc : starRingEnd ℂ z = r ^ 2 / z := by
    rw [eq_div_iff hz, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hr]
    push_cast; rfl
  rw [hc]
  subst hab
  have he : 2 * a - (a + b) = a - b := by ring
  rw [he, div_zpow, div_zpow, zpow_sub₀ hz, zpow_sub₀ hr0, zpow_add₀ hr0, pow_two, mul_zpow]
  field_simp
end GlobalTheory.Div.CMAlgChar
