-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.prefixLe_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:54:24.416229+00:00
-- url     : https://prove2.me/submissions/1a2aaa94-6481-4afa-952c-7b31c75ac2e6

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_add
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_prefixLe_neg

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
theorem _root_.solution {x y : Γ} {n : ℕ} {b : ℝ} (hx : T.PrefixLe x n b) (hy : T.PrefixLe y n b) :
    T.PrefixLe (x - y) n b := by
  rw [sub_eq_add_neg]; exact T.prefixLe_add hx (T.prefixLe_neg hy)
end GroundTheory.PAdicHodge.TeichLift
