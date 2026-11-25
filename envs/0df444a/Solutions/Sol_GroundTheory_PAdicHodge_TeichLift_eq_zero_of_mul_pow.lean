-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.eq_zero_of_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:27:05.488234+00:00
-- url     : https://prove2.me/submissions/95ec0443-a143-4c96-8195-49a4506d6520

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
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution {b : T.B} {N : ℕ} (h : b * algebraMap Γ T.B T.π ^ N = 0) : b = 0 := by
  have hu : IsUnit (algebraMap Γ T.B T.π ^ N) := (IsLocalization.Away.algebraMap_isUnit T.π).pow N
  exact (hu.mul_left_eq_zero).1 h
end GroundTheory.PAdicHodge.TeichLift
