-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_multiset_prod_le_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:55.180805+00:00
-- url     : https://prove2.me/submissions/64a8d885-255b-4c71-802c-6d21fe634482

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
omit [IsUltrametricDist E]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {s : Multiset E} {C : ℝ} (h : ∀ a ∈ s, ‖a‖ ≤ C) :
    ‖s.prod‖ ≤ C ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ, mul_comm (C ^ _)]
    exact mul_le_mul (h a (Multiset.mem_cons_self a t))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb)) (norm_nonneg _)
      ((norm_nonneg a).trans (h a (Multiset.mem_cons_self a t)))
end GroundTheory.PAdicHodge
