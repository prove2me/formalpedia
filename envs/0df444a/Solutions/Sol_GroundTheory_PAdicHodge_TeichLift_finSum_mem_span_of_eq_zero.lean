-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.finSum_mem_span_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:48:19.252804+00:00
-- url     : https://prove2.me/submissions/35402b51-61fa-468f-95f5-a7f55ef127eb

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_finSum_congr

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
theorem _root_.solution {a : ℕ → L} {n m : ℕ} (h : ∀ i < m, a i = 0) (hmn : m ≤ n) :
    T.finSum a n ∈ Ideal.span {T.π ^ m} := by
  have h0 : T.finSum a m = 0 := by
    rw [T.finSum_congr (b := 0) h]; simp [finSum]
  simpa [h0] using T.finSum_sub_finSum_mem a hmn
end GroundTheory.PAdicHodge.TeichLift
