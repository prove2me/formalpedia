-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.teich_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:18.731012+00:00
-- url     : https://prove2.me/submissions/ea821653-81a1-47ca-93ab-c9957e6eea23

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
theorem _root_.solution (a b : L) : T.teich (a * b) = T.teich a * T.teich b := map_mul _ _ _
end GroundTheory.PAdicHodge.TeichLift
