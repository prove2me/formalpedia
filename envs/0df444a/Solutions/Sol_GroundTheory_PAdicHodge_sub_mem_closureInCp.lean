-- Prove2me | solution 1 for GroundTheory.PAdicHodge.sub_mem_closureInCp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:53.954169+00:00
-- url     : https://prove2.me/submissions/3960546d-b864-4403-998f-808315b657ca

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
include hbound
omit hadd hbound
namespace GroundTheory.PAdicHodge
theorem _root_.solution {x x' : ℂ_[p]} (hx : x ∈ closureInCp E) (hx' : x' ∈ closureInCp E) :
    x - x' ∈ closureInCp E :=
  map_mem_closure₂ continuous_sub hx hx' (by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact ⟨y - z, sub_mem hy hz, UniformSpace.Completion.coe_sub y z⟩)
end GroundTheory.PAdicHodge
