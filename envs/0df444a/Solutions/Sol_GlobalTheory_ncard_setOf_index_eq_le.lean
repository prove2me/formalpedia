-- Prove2me | solution 1 for GlobalTheory.ncard_setOf_index_eq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:24:42.604457+00:00
-- url     : https://prove2.me/submissions/ab20c6b7-ca2a-421b-979a-a5224be1bbfe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Theorems.Thm_GlobalTheory_encard_setOf_index_eq_le
import Theorems.Thm_GlobalTheory_finite_setOf_index_eq

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
theorem _root_.solution [Module.Free ℤ M] [Module.Finite ℤ M] {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup M | H.index = m}.ncard ≤ m ^ finrank ℤ M := by
  have h := encard_setOf_index_eq_le (M := M) hm
  rw [← (finite_setOf_index_eq (M := M) hm).cast_ncard_eq] at h
  exact_mod_cast h
end GlobalTheory
