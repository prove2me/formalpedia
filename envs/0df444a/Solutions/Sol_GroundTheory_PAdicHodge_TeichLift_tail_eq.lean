-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.tail_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:57:18.916638+00:00
-- url     : https://prove2.me/submissions/bfe0f694-9674-4f26-ad7a-0a8b4f1b7d69

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_red___ee117558e102
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift___mul_cancel_eaec830aa15d
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_sub_teich_eq___mul_tail_219974f30227

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
theorem _root_.solution {x y : Γ} {a : L} (h : x = T.teich a + T.π * y) : T.tail x = y := by
  have ha : T.red x = a := by rw [h, map_add, map_mul, red_π, zero_mul, add_zero, red_teich]
  refine T.π_mul_cancel ?_
  rw [← T.sub_teich_eq_π_mul_tail, ha, h]; ring
end GroundTheory.PAdicHodge.TeichLift
