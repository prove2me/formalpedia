-- Prove2me | solution 1 for GlobalTheory.eventually_const_mul_rpow_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:27.376297+00:00
-- url     : https://prove2.me/submissions/0a97d85d-29cf-4390-991b-1066548a62c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiveElementaryInequalitiesEventually

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (a b c : ℝ) (h : a < b) :
    ∀ᶠ x : ℝ in atTop, c * x ^ a ≤ x ^ b := by
  have ht := tendsto_rpow_atTop (sub_pos.2 h)
  filter_upwards [ht.eventually_ge_atTop c, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have e : x ^ b = x ^ (b - a) * x ^ a := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le _)
end GlobalTheory
