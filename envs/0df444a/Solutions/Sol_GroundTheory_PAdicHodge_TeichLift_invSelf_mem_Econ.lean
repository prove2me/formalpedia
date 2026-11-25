-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.invSelf_mem_Econ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:48:45.394882+00:00
-- url     : https://prove2.me/submissions/47038bf8-1012-4459-a29c-8ed14d048b8a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeffB_invSelf
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_mem_Econ

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.PAdicHodge
open Laurent Filter Topology
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ) {ρ : ℝ}
variable {b c : T.B}
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution (ρ : Set.Ioo (0 : ℝ) 1) : IsLocalization.Away.invSelf T.π ∈ T.Econ ρ := by
  rw [mem_Econ, coeffB_invSelf]; exact convergesAt_pi_single _ _ _
end GroundTheory.PAdicHodge.TeichLift
