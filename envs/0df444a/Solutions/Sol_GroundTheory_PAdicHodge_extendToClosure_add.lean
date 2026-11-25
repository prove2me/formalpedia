-- Prove2me | solution 1 for GroundTheory.PAdicHodge.extendToClosure_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:26.741571+00:00
-- url     : https://prove2.me/submissions/33272784-2f41-4e1f-8ce1-02aa204d4ce3

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Theorems.Thm_GroundTheory_PAdicHodge_sub_mem_closureInCp
import Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_sub

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
theorem _root_.solution {x x' : ℂ_[p]} (hx : x ∈ closureInCp E) (hx' : x' ∈ closureInCp E) :
    x + x' ∈ closureInCp E ∧
      extendToClosure E R (x + x') = extendToClosure E R x + extendToClosure E R x' := by
  have h0 : (0 : ℂ_[p]) ∈ closureInCp E := by
    simpa using coe_mem_closureInCp (zero_mem E)
  have hneg : -x' ∈ closureInCp E := by simpa using sub_mem_closureInCp h0 hx'
  have h1 : x + x' = x - -x' := by rw [sub_neg_eq_add]
  have hR0 : extendToClosure E R 0 = 0 := by
    have := extendToClosure_sub hadd hbound h0 h0
    rwa [sub_self, sub_self] at this
  have hRneg : extendToClosure E R (-x') = -extendToClosure E R x' := by
    have := extendToClosure_sub hadd hbound h0 hx'
    rwa [zero_sub, hR0, zero_sub] at this
  refine ⟨h1 ▸ sub_mem_closureInCp hx hneg, ?_⟩
  rw [h1, extendToClosure_sub hadd hbound hx hneg, hRneg, sub_neg_eq_add]
end GroundTheory.PAdicHodge
