-- Prove2me | solution 1 for GroundTheory.Global.prod_norm_natCast_infinitePlaceCompletion_pow_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:09:52.869812+00:00
-- url     : https://prove2.me/submissions/c0abf770-279f-4f51-871b-9f37f0f6516f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (n : ℕ) :
    ∏ w : InfinitePlace K, ‖(n : w.Completion)‖ ^ w.mult = (n : ℝ) ^ Module.finrank ℚ K := by
  have h := InfinitePlace.prod_eq_abs_norm (n : K)
  have hw : ∀ w : InfinitePlace K, ‖(n : w.Completion)‖ = w (n : K) := fun w ↦ by
    rw [← map_natCast (algebraMap K w.Completion) n]
    exact InfinitePlace.Completion.norm_coe (K := K) (v := w) _
  simp_rw [hw, h, ← map_natCast (algebraMap ℚ K) n, Algebra.norm_algebraMap]
  push_cast
  exact abs_of_nonneg (by positivity)
end GroundTheory.Global
