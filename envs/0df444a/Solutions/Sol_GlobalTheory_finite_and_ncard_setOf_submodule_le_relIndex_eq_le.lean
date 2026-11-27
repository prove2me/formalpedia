-- Prove2me | solution 1 for GlobalTheory.finite_and_ncard_setOf_submodule_le_relIndex_eq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:48.788246+00:00
-- url     : https://prove2.me/submissions/082c61b0-c22c-4539-8852-f9eb150cb857

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Theorems.Thm_GlobalTheory_encard_setOf_submodule_le_relIndex_eq_le

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
theorem _root_.solution {R : Type*} [Ring R] [Module R M]
    (L : Submodule R M) [Module.Free ℤ L] [Module.Finite ℤ L] {m : ℕ} (hm : m ≠ 0) :
    {H : Submodule R M | H ≤ L ∧ H.toAddSubgroup.relIndex L.toAddSubgroup = m}.Finite ∧
    {H : Submodule R M | H ≤ L ∧ H.toAddSubgroup.relIndex L.toAddSubgroup = m}.ncard ≤
      m ^ finrank ℤ L := by
  have h := encard_setOf_submodule_le_relIndex_eq_le L hm
  have hf := Set.finite_of_encard_le_coe h
  refine ⟨hf, ?_⟩
  rw [← hf.cast_ncard_eq] at h
  exact_mod_cast h
end GlobalTheory
