-- Prove2me | solution 2 for GroundTheory.Global.eq_one_of_sq_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:44:31.392137+00:00
-- url     : https://prove2.me/submissions/d9a6f704-fad9-4b59-8643-c722de2db1b5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Theorems.Thm_GroundTheory_Global_eq_one_of_forall_norm_pow_two_pow_sub_one_lt

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
open Topology Filter
namespace GroundTheory.Global
theorem _root_.solution {s : Set ℂ} (hsq : ∀ z ∈ s, z ^ 2 ∈ s)
    (hs : ∀ z ∈ s, ‖z - 1‖ < 1 / 2) {z : ℂ} (hz : z ∈ s) : z = 1 := by
  refine eq_one_of_forall_norm_pow_two_pow_sub_one_lt fun k ↦ hs _ ?_
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    rw [pow_succ, pow_mul]
    exact hsq _ ih
end GroundTheory.Global
