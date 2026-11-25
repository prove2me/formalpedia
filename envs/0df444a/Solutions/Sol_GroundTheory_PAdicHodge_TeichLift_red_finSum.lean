-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.red_finSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:14.714208+00:00
-- url     : https://prove2.me/submissions/beefc737-0731-463d-a15a-f84f2c5615ee

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_red___ee117558e102
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_finSum_succ__591efcd7936f

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
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open Ideal
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution (a : ℕ → L) (n : ℕ) : T.red (T.finSum a (n + 1)) = a 0 := by
  rw [finSum_succ', map_add, map_mul, red_π, zero_mul, add_zero, red_teich]
end GroundTheory.PAdicHodge.TeichLift
