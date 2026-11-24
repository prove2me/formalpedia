-- Prove2me | solution 1 for GlobalTheory.Hk.LFam.half_lt_re_of_region
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:30:29.797607+00:00
-- url     : https://prove2.me/submissions/bca3c882-ad7b-4835-b58e-8586fb703a73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Theorems.Thm_GlobalTheory_Hk_LFam_two_lt_ell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Hk
attribute [instance] LFam.ag LFam.ft
open GlobalTheory.Hk.LFam
variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)
namespace GlobalTheory.Hk.LFam
theorem _root_.solution {c : ℝ} (hc : c ≤ 1) {s : ℂ} (hs : 1 - c / 𝓕.ell s.im ≤ s.re) : 1 / 2 < s.re := by
  have h := 𝓕.two_lt_ell s.im
  have : c / 𝓕.ell s.im < 1 / 2 := by
    rw [div_lt_iff₀ (by linarith)]; linarith
  linarith
end GlobalTheory.Hk.LFam
