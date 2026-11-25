-- Prove2me | solution 1 for HatAffineOffsets.puncturedLine_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:19:12.104818+00:00
-- url     : https://prove2.me/submissions/e97f97fa-b422-4588-bc73-7db0c9740dcf

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Theorems.Thm_HatAffineOffsets_puncturedLine_card_eq_allowed
import Theorems.Thm_HatAffineOffsets_nonzeroFinset_card
import Theorems.Thm_HatAffineGenericCore_mem_coeffSupport
import Theorems.Thm_HatAffineGenericCore_mem_puncturedValues
import Theorems.Thm_HatAffineGenericCore_puncturedValues_card
attribute [local simp] HatAffineGenericCore.mem_coeffSupport
attribute [local simp] HatAffineGenericCore.mem_puncturedValues
attribute [local simp] HatAffineGenericCore.puncturedValues_card



set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9
namespace HatAffineOffsets
theorem _root_.solution
    {K : Type u} [Field K] [Fintype K]
    (hq : 4 <= Fintype.card K)
    (c e : K) (hc : c ≠ 0) :
    (puncturedLine c e).card =
      if e = 0 then Fintype.card K - 1 else Fintype.card K - 2 := by
  classical
  rw [puncturedLine_card_eq_allowed]
  by_cases he : e = 0
  · subst e
    rw [if_pos rfl]
    have hallowed : allowedLineParameter c 0 = nonzeroFinset K := by
      ext t
      simp [allowedLineParameter, nonzeroFinset, hc]
    rw [hallowed, nonzeroFinset_card]
  · rw [if_neg he]
    let z : K := -e / c
    have hz0 : z ≠ 0 := div_ne_zero (neg_ne_zero.mpr he) hc
    have hzero : forall t : K, c * t + e = 0 ↔ t = z := by
      intro t
      constructor
      · intro ht
        apply (eq_div_iff hc).mpr
        calc
          t * c = c * t := by rw [mul_comm]
          _ = (c * t + e) - e := by ring
          _ = -e := by rw [ht]; exact zero_sub e
      · intro htz
        have htc : t * c = -e := (eq_div_iff hc).mp htz
        calc
          c * t + e = t * c + e := by rw [mul_comm]
          _ = -e + e := by rw [htc]
          _ = 0 := neg_add_cancel e
    have hallowed :
        allowedLineParameter c e = (nonzeroFinset K).erase z := by
      ext t
      simp only [allowedLineParameter, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨ht, hne⟩
        refine ⟨?_, ht⟩
        intro htz
        exact hne ((hzero t).mpr htz)
      · rintro ⟨htz, ht⟩
        refine ⟨ht, ?_⟩
        intro hct
        exact htz ((hzero t).mp hct)
    rw [hallowed, Finset.card_erase_of_mem]
    · rw [nonzeroFinset_card]
      omega
    · simpa [nonzeroFinset, hz0]
end HatAffineOffsets
