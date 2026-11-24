-- Prove2me | solution 1 for GlobalTheory.idempotent_eq_of_forall_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:27:10.458635+00:00
-- url     : https://prove2.me/submissions/7f135b92-d989-432a-bc3c-c68d9e694d06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_idempotent_eq_of_sub_mem_jacobson
import Theorems.Thm_GlobalTheory_mem_jacobson_bot_of_forall_isMaximal
import Theorems.Thm_GlobalTheory_one_sub_mem_iff_notMem_of_isIdempotentElem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
theorem _root_.solution {S : Type*} [CommRing S] {a b : S}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : ∀ n : Ideal S, n.IsMaximal → (a ∈ n ↔ b ∈ n)) : a = b := by
  refine idempotent_eq_of_sub_mem_jacobson ha hb
    (mem_jacobson_bot_of_forall_isMaximal fun n hn ↦ ?_)
  by_cases han : a ∈ n
  · exact sub_mem han ((h n hn).1 han)
  · have h1 := (one_sub_mem_iff_notMem_of_isIdempotentElem ha n).2 han
    have h2 := (one_sub_mem_iff_notMem_of_isIdempotentElem hb n).2 (mt (h n hn).2 han)
    simpa using sub_mem h2 h1
end GlobalTheory
