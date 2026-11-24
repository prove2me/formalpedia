-- Prove2me | solution 1 for GlobalTheory.LLower.norm_LSeries_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:53:26.818037+00:00
-- url     : https://prove2.me/submissions/f5e2bdf0-8b7d-4ecf-89bb-be5b14243b2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Theorems.Thm_GlobalTheory_LLower_tsum_one_div_rpow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LLower
namespace GlobalTheory.LLower
theorem _root_.solution {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries f s‖ ≤ s.re / (s.re - 1) := by
  have hσ : 1 < s.re := hs
  have hg : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ s.re) (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re) := by
    have hsum := Real.summable_one_div_nat_rpow.mpr hσ
    have := hsum.hasSum
    rw [hsum.tsum_eq_zero_add] at this
    simpa [Real.zero_rpow (by linarith : s.re ≠ 0)] using this
  refine (tsum_of_norm_bounded hg fun n => ?_).trans (tsum_one_div_rpow_le hσ)
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · subst hn
    simp [Real.zero_rpow (by linarith : s.re ≠ 0)]
  · have hpos : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
    exact div_le_div_of_nonneg_right (hf n) hpos.le
end GlobalTheory.LLower
