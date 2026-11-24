-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_norm_real_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:38:10.911796+00:00
-- url     : https://prove2.me/submissions/99e873b9-696d-4291-bee2-b9e0e2cdfca8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EntireAntilinearLatticePeriodsConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {c : ℂ} {C : ℝ} (h : ∀ r : ℝ, ‖(r : ℂ) * c‖ ≤ C) : c = 0 := by
  by_contra hc
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h0 : 0 ≤ C := (norm_nonneg _).trans (h 0)
  have key := h ((C + 1) / ‖c‖)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by linarith) hpos.le), div_mul_cancel₀ _ hpos.ne'] at key
  linarith
end GlobalTheory
