-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaBound.term_le_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:26:17.112801+00:00
-- url     : https://prove2.me/submissions/17ad2897-26b2-4076-bd9c-893b726f61d0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlane
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaBound_add_half_le_norm
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaBound_term_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaBound
open Finset
namespace GlobalTheory.CompanionTheory.DigammaBound
theorem _root_.solution (z : ℂ) (hz : 1 / 2 ≤ z.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / (z + ((k : ℂ) + 1))‖ ≤ 2 * ((k : ℝ) + 1)⁻¹ := by
  rw [term_eq z hz k]
  have ha : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hN := add_half_le_norm z hz ((k : ℝ) + 1) ha.le
  have hz' : ‖z‖ ≤ ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖ + ((k : ℝ) + 1) := by
    have h := norm_sub_le (z + (((k : ℝ) + 1 : ℝ) : ℂ)) (((k : ℝ) + 1 : ℝ) : ℂ)
    rw [add_sub_cancel_right, Complex.norm_real, Real.norm_of_nonneg ha.le] at h
    exact h
  have hNpos : 0 < ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖ := by linarith
  rw [div_le_iff₀ (by positivity)]
  have : 2 * ((k : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖) =
      2 * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖ := by
    field_simp
  rw [this]
  linarith
end GlobalTheory.CompanionTheory.DigammaBound
