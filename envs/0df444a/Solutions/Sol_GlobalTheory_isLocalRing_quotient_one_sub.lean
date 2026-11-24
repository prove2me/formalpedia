-- Prove2me | solution 1 for GlobalTheory.isLocalRing_quotient_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:32:30.139033+00:00
-- url     : https://prove2.me/submissions/2b7bca88-38fc-4aad-8dd8-24cfcad306f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
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
theorem _root_.solution {S : Type*} [CommRing S] {e : S} (he : IsIdempotentElem e)
    (q : Ideal S) [hq : q.IsMaximal] (H : ∀ n : Ideal S, n.IsMaximal → (e ∉ n ↔ n = q)) :
    IsLocalRing (S ⧸ Ideal.span {1 - e}) := by
  have hle : Ideal.span {1 - e} ≤ q := by
    rw [Ideal.span_singleton_le_iff_mem, one_sub_mem_iff_notMem_of_isIdempotentElem he, H q hq]
  refine .of_unique_max_ideal ⟨q.map (Ideal.Quotient.mk _),
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using hle),
    fun m hm ↦ ?_⟩
  have := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective (K := m)
  have h : m.comap (Ideal.Quotient.mk _) = q := by
    rw [← H _ this, ← one_sub_mem_iff_notMem_of_isIdempotentElem he, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)]
    exact zero_mem _
  rw [← h, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
end GlobalTheory
