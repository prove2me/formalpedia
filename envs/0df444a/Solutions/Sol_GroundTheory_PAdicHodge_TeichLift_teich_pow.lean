-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.teich_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:30.949009+00:00
-- url     : https://prove2.me/submissions/bb03eda8-6465-44d8-97be-e4221743bafa

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich

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
theorem _root_.solution (a : L) (n : ℕ) : T.teich (a ^ n) = T.teich a ^ n := map_pow _ _ _
end GroundTheory.PAdicHodge.TeichLift
