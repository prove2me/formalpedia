-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaBound.term_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:26:16.283838+00:00
-- url     : https://prove2.me/submissions/ef6abbf8-b609-4930-8949-dcd22a9ffa53

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
    ‖1 / ((k : ℂ) + 1) - 1 / (z + ((k : ℂ) + 1))‖ ≤ ‖z‖ / ((k : ℝ) + 1) ^ 2 := by
  rw [term_eq z hz k]
  have ha : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hN := add_half_le_norm z hz ((k : ℝ) + 1) ha.le
  apply div_le_div_of_nonneg_left (norm_nonneg z) (by positivity)
  nlinarith
end GlobalTheory.CompanionTheory.DigammaBound
