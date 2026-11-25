-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.finSum_mem_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:02.304511+00:00
-- url     : https://prove2.me/submissions/a74a7e8a-0967-4f5a-a3b2-ff7550797d4a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
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
theorem _root_.solution {a : ℕ → L} {n : ℕ} (h : ∀ i < n, ‖a i‖ ≤ 1) : T.finSum a n ∈ T.int :=
  Subring.sum_mem _ fun i hi =>
    mul_mem (pow_mem T.π_mem_int _) (T.teich_mem_int (h i (Finset.mem_range.1 hi)))
end GroundTheory.PAdicHodge.TeichLift
