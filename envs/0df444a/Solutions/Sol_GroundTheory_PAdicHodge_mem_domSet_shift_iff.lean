-- Prove2me | solution 1 for GroundTheory.PAdicHodge.mem_domSet_shift_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:30:48.445786+00:00
-- url     : https://prove2.me/submissions/f055e6ad-68d5-44d6-9005-2c98922a26b3

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
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
theorem _root_.solution (hρ0 : 0 < ρ) (N k : ℤ) :
    k ∈ domSet (fun k => a (k + N)) ρ ↔ k + N ∈ domSet a ρ := by
  simp only [domSet, Set.mem_setOf_eq, gaussNorm_shift hρ0, weight_shift hρ0 N k]
  exact mul_left_inj' (zpow_pos hρ0 _).ne'
end GroundTheory.PAdicHodge
