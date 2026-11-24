-- Prove2me | solution 1 for GlobalTheory.finite_setOf_index_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:45.304745+00:00
-- url     : https://prove2.me/submissions/ed696638-c73c-4a08-948d-24a88eba0ad5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
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
theorem _root_.solution [Module.Free ℤ M] [Module.Finite ℤ M] {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup M | H.index = m}.Finite :=
  Set.finite_of_encard_le_coe (encard_setOf_index_eq_le hm)
end GlobalTheory
