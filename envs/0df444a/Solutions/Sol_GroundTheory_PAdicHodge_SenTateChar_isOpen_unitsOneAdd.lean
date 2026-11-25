-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SenTateChar.isOpen_unitsOneAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:36.44771+00:00
-- url     : https://prove2.me/submissions/0d165266-170d-4a95-b353-d696986f4ad7

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharUnits
import Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_mem_unitsOneAdd_iff_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.SenTateChar
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge.SenTateChar
theorem _root_.solution (k : ℕ) : IsOpen (unitsOneAdd p k : Set ℤ_[p]ˣ) := by
  have hr : (p : ℝ) ^ (-(k : ℤ)) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hset : (unitsOneAdd p k : Set ℤ_[p]ˣ) =
      (fun u : ℤ_[p]ˣ => (u : ℤ_[p])) ⁻¹' Metric.closedBall (1 : ℤ_[p]) ((p : ℝ) ^ (-(k : ℤ))) := by
    ext u
    simp only [SetLike.mem_coe, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    exact mem_unitsOneAdd_iff_norm
  rw [hset]
  exact (IsUltrametricDist.isOpen_closedBall _ hr).preimage Units.continuous_val
end GroundTheory.PAdicHodge.SenTateChar
