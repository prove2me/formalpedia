-- Prove2me | solution 1 for GroundTheory.PAdicHodge.lipschitzWith_coe_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:16.640915+00:00
-- url     : https://prove2.me/submissions/6e85a714-37d2-4c9d-8d71-a6edb6c29b39

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Theorems.Thm_GroundTheory_PAdicHodge_map_sub_of_add

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
include hbound
namespace GroundTheory.PAdicHodge
theorem _root_.solution :
    LipschitzWith (Real.toNNReal c) fun y : E => ((R y : PadicAlgCl p) : ℂ_[p]) := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [UniformSpace.Completion.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm,
    ← map_sub_of_add hadd y.2 z.2]
  exact (hbound _ (sub_mem y.2 z.2)).trans
    (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal c) (norm_nonneg _))
end GroundTheory.PAdicHodge
