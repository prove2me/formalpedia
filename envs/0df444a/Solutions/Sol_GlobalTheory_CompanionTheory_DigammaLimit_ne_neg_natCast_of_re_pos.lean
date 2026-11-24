-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaLimit.ne_neg_natCast_of_re_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:26:25.213283+00:00
-- url     : https://prove2.me/submissions/bc864c43-1c2f-451e-bd86-1d9d04fed499

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_add_natCast_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Metric Set
open scoped Nat Real
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaLimit
namespace GlobalTheory.CompanionTheory.DigammaLimit
theorem _root_.solution {z : ℂ} (hz : 0 < z.re) (m : ℕ) : z ≠ -(m : ℂ) := by
  intro h
  exact add_natCast_ne_zero hz m (by rw [h]; ring)
end GlobalTheory.CompanionTheory.DigammaLimit
