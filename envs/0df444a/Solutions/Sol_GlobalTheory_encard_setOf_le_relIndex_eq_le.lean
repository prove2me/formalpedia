-- Prove2me | solution 1 for GlobalTheory.encard_setOf_le_relIndex_eq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:13:27.644888+00:00
-- url     : https://prove2.me/submissions/d38c1c6a-025f-43e3-8ed6-ee8816203be2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Theorems.Thm_GlobalTheory_setOf_le_relIndex_eq_image
import Theorems.Thm_GlobalTheory_encard_setOf_index_eq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {M : Type*} [AddCommGroup M]
namespace GlobalTheory
theorem _root_.solution (K : AddSubgroup M) [Module.Free ℤ K] [Module.Finite ℤ K]
    {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup M | H ≤ K ∧ H.relIndex K = m}.encard ≤ ((m ^ finrank ℤ K : ℕ) : ℕ∞) := by
  rw [setOf_le_relIndex_eq_image]
  exact (Set.encard_image_le _ _).trans (encard_setOf_index_eq_le hm)
end GlobalTheory
