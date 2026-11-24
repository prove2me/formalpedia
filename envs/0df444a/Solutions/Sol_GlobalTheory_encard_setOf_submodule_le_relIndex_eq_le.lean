-- Prove2me | solution 1 for GlobalTheory.encard_setOf_submodule_le_relIndex_eq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:19:53.581722+00:00
-- url     : https://prove2.me/submissions/11933486-b392-4a01-bc94-996c80ab6907

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Theorems.Thm_GlobalTheory_encard_setOf_le_relIndex_eq_le

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
    {H : Submodule R M | H ≤ L ∧ H.toAddSubgroup.relIndex L.toAddSubgroup = m}.encard ≤
      ((m ^ finrank ℤ L : ℕ) : ℕ∞) := by
  haveI : Module.Free ℤ L.toAddSubgroup := inferInstanceAs (Module.Free ℤ L)
  haveI : Module.Finite ℤ L.toAddSubgroup := inferInstanceAs (Module.Finite ℤ L)
  refine le_trans ?_ (encard_setOf_le_relIndex_eq_le L.toAddSubgroup hm)
  refine Set.encard_le_encard_of_injOn (f := Submodule.toAddSubgroup) ?_
    Submodule.toAddSubgroup_injective.injOn
  rintro H ⟨h1, h2⟩
  exact ⟨h1, h2⟩
end GlobalTheory
