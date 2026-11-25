-- Prove2me | solution 1 for GroundTheory.PAdicHodge.lowIndex_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:40:28.840575+00:00
-- url     : https://prove2.me/submissions/c2b2eec3-87d9-4d50-a228-a9bf45072462

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Theorems.Thm_GroundTheory_PAdicHodge_mem_domSet_shift_iff
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_lowIndex_le
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_lowIndex_mem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_zero_elem
attribute [local simp] P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.PAdicHodge
open Laurent Filter Topology
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] {a : ℤ → L} {ρ : ℝ}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (hρ0 : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0) (N : ℤ) :
    lowIndex (fun k => a (k + N)) ρ = lowIndex a ρ - N := by
  have hs := convergesAt_shift hρ0 h N
  have hs0 : (fun k => a (k + N)) ≠ 0 := by
    intro h0
    apply ha
    funext j
    have := congrFun h0 (j - N)
    simpa using this
  refine le_antisymm (lowIndex_le hρ0 hs hs0 ((mem_domSet_shift_iff hρ0 N _).2 ?_)) ?_
  · rw [sub_add_cancel]; exact lowIndex_mem hρ0 h ha
  · have := lowIndex_le hρ0 h ha ((mem_domSet_shift_iff hρ0 N _).1 (lowIndex_mem hρ0 hs hs0))
    linarith
end GroundTheory.PAdicHodge
