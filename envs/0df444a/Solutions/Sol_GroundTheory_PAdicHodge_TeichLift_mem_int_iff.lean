-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.mem_int_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:33:16.317313+00:00
-- url     : https://prove2.me/submissions/a944ed5a-31e1-4a6b-b048-ac8efae540df

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_sub_partialSum_mem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_tail_mem_int
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_finSum_mem_int

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
theorem _root_.solution {x : Γ} : x ∈ T.int ↔ ∀ n, ‖T.coeff x n‖ ≤ 1 := by
  constructor
  · intro hx n
    have : T.tail^[n] x ∈ T.int := by
      induction n with
      | zero => exact hx
      | succ n ih => rw [Function.iterate_succ_apply']; exact T.tail_mem_int ih
    exact T.norm_red_le_one _ this
  · intro h
    exact T.mem_int_of_approx x fun N =>
      ⟨T.partialSum x N, T.finSum_mem_int fun i _ => h i, T.sub_partialSum_mem x N⟩
end GroundTheory.PAdicHodge.TeichLift
