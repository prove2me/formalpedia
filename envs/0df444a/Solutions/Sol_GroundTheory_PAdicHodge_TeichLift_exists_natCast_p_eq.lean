-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.exists_natCast_p_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:38.542059+00:00
-- url     : https://prove2.me/submissions/755575d1-f2f6-40e5-aa55-7410757c21f9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_red_natCast

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
theorem _root_.solution : ∃ w ∈ T.int, (p : Γ) = T.π * w :=
  T.exists_eq_π_mul _ (natCast_mem _ p) (by rw [red_natCast, CharP.cast_eq_zero])
end GroundTheory.PAdicHodge.TeichLift
