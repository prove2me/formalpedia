-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_multiset_sum_le_of_forall_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:30:47.080654+00:00
-- url     : https://prove2.me/submissions/ae5ba338-65a2-47c9-91de-a20f62d769f1

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
variable {E : Type*} [NormedField E] [IsUltrametricDist E]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {s : Multiset E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ a ∈ s, ‖a‖ ≤ C) : ‖s.sum‖ ≤ C := by
  induction s using Multiset.induction_on with
  | empty => simpa using hC
  | cons a t ih =>
    rw [Multiset.sum_cons]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (Multiset.mem_cons_self a t))
        (ih fun b hb => h b (Multiset.mem_cons_of_mem hb)))
end GroundTheory.PAdicHodge
