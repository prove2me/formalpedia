-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_extendToClosure_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:02:18.540149+00:00
-- url     : https://prove2.me/submissions/3097d455-afce-420f-9dd4-767334b39eba

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_induction

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
theorem _root_.solution {x : ℂ_[p]} (hx : x ∈ closureInCp E) :
    ‖extendToClosure E R x‖ ≤ c * ‖x‖ := by
  refine extendToClosure_induction hadd hbound (P := fun u v => ‖v‖ ≤ c * ‖u‖)
    (isClosed_le (continuous_norm.comp continuous_snd)
      (continuous_const.mul (continuous_norm.comp continuous_fst))) (fun y hy => ?_) x hx
  rw [PadicComplex.norm_extends, PadicComplex.norm_extends]
  exact hbound y hy
end GroundTheory.PAdicHodge
