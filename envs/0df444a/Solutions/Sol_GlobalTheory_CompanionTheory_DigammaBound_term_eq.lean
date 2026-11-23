-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaBound.term_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:57.053649+00:00
-- url     : https://prove2.me/submissions/a2298117-842f-4d7a-8710-5e6d4eb2648b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlane
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaBound_add_half_le_norm

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
    ‖1 / ((k : ℂ) + 1) - 1 / (z + ((k : ℂ) + 1))‖ =
      ‖z‖ / (((k : ℝ) + 1) * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hc : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  have hN := add_half_le_norm z hz ((k : ℝ) + 1) hk
  have h2 : z + (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hN
    linarith
  have h1 : (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    rw [← hc]
    exact_mod_cast Nat.succ_ne_zero k
  rw [hc]
  have : 1 / (((k : ℝ) + 1 : ℝ) : ℂ) - 1 / (z + (((k : ℝ) + 1 : ℝ) : ℂ)) =
      z / ((((k : ℝ) + 1 : ℝ) : ℂ) * (z + (((k : ℝ) + 1 : ℝ) : ℂ))) := by
    field_simp
    ring
  rw [this, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk]
end GlobalTheory.CompanionTheory.DigammaBound
