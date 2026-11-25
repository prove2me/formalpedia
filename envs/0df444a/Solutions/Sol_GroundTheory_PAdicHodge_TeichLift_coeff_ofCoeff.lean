-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:33:23.553497+00:00
-- url     : https://prove2.me/submissions/51f611f8-ec09-4c54-b7ee-48a17edb6e97

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_eq_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_mk_sub_finSum_mem

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
theorem _root_.solution (a : ℕ → L) : T.coeff (T.ofCoeff a) = a :=
  funext fun n => T.coeff_eq_of_mem (T.mk_sub_finSum_mem a (n + 1)) n le_rfl
end GroundTheory.PAdicHodge.TeichLift
