-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.algebraMap_teich_mem_Econ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:48:17.496199+00:00
-- url     : https://prove2.me/submissions/84e32f4a-0cf4-4bf6-8cda-635e8aa539f9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_zcoeff_teich
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
theorem _root_.solution (c : L) (ρ : Set.Ioo (0 : ℝ) 1) :
    algebraMap Γ T.B (T.teich c) ∈ T.Econ ρ := by
  rw [mem_Econ, coeffB_algebraMap, zcoeff_teich]; exact convergesAt_pi_single _ _ _
end GroundTheory.PAdicHodge.TeichLift
