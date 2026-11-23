-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.PrefixLe.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:37.508504+00:00
-- url     : https://prove2.me/submissions/af05dcdf-cdc1-4c7c-8565-0cdedfb1d4e2

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
variable {T}
namespace GroundTheory.PAdicHodge.TeichLift
namespace PrefixLe
theorem _root_.solution {x : Γ} {n : ℕ} {b b' : ℝ} (h : T.PrefixLe x n b) (hb : b ≤ b') :
    T.PrefixLe x n b' := fun m hm => (h m hm).trans hb
end PrefixLe
end GroundTheory.PAdicHodge.TeichLift
