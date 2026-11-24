-- Prove2me | solution 1 for GlobalTheory.finite_and_ncard_setOf_index_pi_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:30:15.145854+00:00
-- url     : https://prove2.me/submissions/6bb4a06c-d86b-417c-8fbe-ec4658845a3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Theorems.Thm_GlobalTheory_finite_setOf_index_eq
import Theorems.Thm_GlobalTheory_ncard_setOf_index_eq_le

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
theorem _root_.solution (ρ : ℕ) {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup (Fin ρ → ℤ) | H.index = m}.Finite ∧
      {H : AddSubgroup (Fin ρ → ℤ) | H.index = m}.ncard ≤ m ^ ρ := by
  refine ⟨finite_setOf_index_eq hm, ?_⟩
  simpa using ncard_setOf_index_eq_le (M := Fin ρ → ℤ) hm
end GlobalTheory
