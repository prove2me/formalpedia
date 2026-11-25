-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.coeffB_invSelf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:27:13.059731+00:00
-- url     : https://prove2.me/submissions/98ac58ed-dc7e-485e-aadf-58787ac26fd7

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
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ) {ρ : ℝ}
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution : T.coeffB (IsLocalization.Away.invSelf T.π) = Pi.single (-1) 1 := by
  rw [T.coeffB_eq (x := 1) (N := 1) (by rw [pow_one, mul_comm, IsLocalization.Away.mul_invSelf, map_one]),
    zcoeff_one]
  funext k
  simp only [Pi.single_apply, Nat.cast_one]
  congr 1; exact propext ⟨fun h => by omega, fun h => by omega⟩
end GroundTheory.PAdicHodge.TeichLift
