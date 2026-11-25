-- Prove2me | solution 1 for GroundTheory.PAdicHodge.extendToClosure_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:11.722201+00:00
-- url     : https://prove2.me/submissions/a5913764-e00c-40af-be8f-7bbd5b8a74c1

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_extendOnClosure_toClosureInCp

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
theorem _root_.solution {y : PadicAlgCl p} (hy : y ∈ E) :
    extendToClosure E R (y : ℂ_[p]) = ((R y : PadicAlgCl p) : ℂ_[p]) := by
  rw [extendToClosure_of_mem (coe_mem_closureInCp hy)]
  exact extendOnClosure_toClosureInCp hadd hbound ⟨y, hy⟩
end GroundTheory.PAdicHodge
