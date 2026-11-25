-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.prefixLe_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:53:35.823372+00:00
-- url     : https://prove2.me/submissions/d50a985a-f958-4a89-bb09-20843020a348

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_of_mem_span

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
theorem _root_.solution {x : Γ} {n : ℕ} (h : x ∈ Ideal.span {T.π ^ (n + 1)}) {b : ℝ}
    (hb : 0 ≤ b) : T.PrefixLe x n b := fun m hm => by
  rw [T.coeff_of_mem_span h m hm, norm_zero]; exact hb
end GroundTheory.PAdicHodge.TeichLift
