-- Prove2me | solution 1 for GlobalTheory.one_sub_mem_iff_notMem_of_isIdempotentElem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:27:40.116968+00:00
-- url     : https://prove2.me/submissions/fc04c425-7f1b-42ad-b5d2-dd9ae379850c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing

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
theorem _root_.solution {S : Type*} [CommRing S] {e : S}
    (he : IsIdempotentElem e) (n : Ideal S) [hn : n.IsPrime] : 1 - e ∈ n ↔ e ∉ n := by
  refine ⟨fun h h' ↦ hn.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using add_mem h h')),
    fun h ↦ ?_⟩
  have : e * (1 - e) ∈ n := by rw [mul_sub, mul_one, he.eq, sub_self]; exact zero_mem _
  exact (hn.mem_or_mem this).resolve_left h
end GlobalTheory
