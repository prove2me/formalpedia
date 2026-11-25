-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.quotEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:13.621944+00:00
-- url     : https://prove2.me/submissions/6ec6c665-582b-48e9-ab08-07bdd6b86fbc

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
theorem _root_.solution (a : L) (x : Γ) (h : T.red x = a) :
    T.quotEquiv.symm a = Ideal.Quotient.mk T.I x := by
  rw [RingEquiv.symm_apply_eq, quotEquiv_mk, h]
end GroundTheory.PAdicHodge.TeichLift
