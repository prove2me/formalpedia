-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.tail_mem_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:21:44.888812+00:00
-- url     : https://prove2.me/submissions/69b56dcc-a787-4375-95ee-c8f7bc83ad97

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift___mul_cancel_eaec830aa15d
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_sub_teich_eq___mul_tail_219974f30227
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_teich_mem_int

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
theorem _root_.solution {x : Γ} (hx : x ∈ T.int) : T.tail x ∈ T.int := by
  have h1 : x - T.teich (T.red x) ∈ T.int :=
    sub_mem hx (T.teich_mem_int (T.norm_red_le_one x hx))
  obtain ⟨y, hy, hxy⟩ := T.exists_eq_π_mul _ h1 (T.red_sub_teich_red x)
  rw [T.sub_teich_eq_π_mul_tail] at hxy
  rwa [T.π_mul_cancel hxy]
end GroundTheory.PAdicHodge.TeichLift
