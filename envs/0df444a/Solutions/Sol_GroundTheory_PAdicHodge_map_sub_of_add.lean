-- Prove2me | solution 1 for GroundTheory.PAdicHodge.map_sub_of_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:53.515803+00:00
-- url     : https://prove2.me/submissions/df80e957-20fb-4aa6-a762-66bf75b0677c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open UniformSpace Topology Filter Set
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable (E : IntermediateField ℚ_[p] (PadicAlgCl p))
variable (R : PadicAlgCl p → PadicAlgCl p)
variable {E R}
variable {c : ℝ} (hadd : ∀ y ∈ E, ∀ z ∈ E, R (y + z) = R y + R z)
  (hbound : ∀ y ∈ E, ‖R y‖ ≤ c * ‖y‖)
include hadd
namespace GroundTheory.PAdicHodge
theorem _root_.solution {y z : PadicAlgCl p} (hy : y ∈ E) (hz : z ∈ E) :
    R (y - z) = R y - R z := by
  have h := hadd (y - z) (sub_mem hy hz) z hz
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]
end GroundTheory.PAdicHodge
