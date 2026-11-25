-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.nontrivial_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:30:45.503903+00:00
-- url     : https://prove2.me/submissions/123f810c-54cd-46d4-9808-b971db254d01

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded

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
theorem _root_.solution : Nontrivial T.B := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h1 : algebraMap Γ T.B 0 = algebraMap Γ T.B 1 := by rw [map_zero, map_one]; exact h
  have h2 := congrArg T.red (T.algebraMap_injective h1)
  rw [map_zero, map_one] at h2
  exact zero_ne_one h2
end GroundTheory.PAdicHodge.TeichLift
