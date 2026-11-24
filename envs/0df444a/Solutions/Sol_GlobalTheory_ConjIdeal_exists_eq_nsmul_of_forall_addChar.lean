-- Prove2me | solution 1 for GlobalTheory.ConjIdeal.exists_eq_nsmul_of_forall_addChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:57:22.238045+00:00
-- url     : https://prove2.me/submissions/8931c59e-d06a-4f92-b098-0fcaf1f80c66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqNsmulOfForallAddChar
import Theorems.Thm_GlobalTheory_ConjIdeal_exists_eq_nsmul_of_forall_zmod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ConjIdeal
namespace GlobalTheory.ConjIdeal
theorem _root_.solution {X : Type*} [AddCommGroup X] [Module.Free ℤ X] {M : ℕ}
    (hM : M ≠ 0) {C : Type*} [CommMonoid C] {ζ : C} (hζ : IsPrimitiveRoot ζ M) (v : X)
    (h : ∀ t : AddChar X C, (∀ x, t x ^ M = 1) → t v = 1) : ∃ z : X, v = M • z := by
  haveI : NeZero M := ⟨hM⟩
  refine exists_eq_nsmul_of_forall_zmod M v fun t => ?_
  have h1 := h ((AddChar.zmodChar M hζ.pow_eq_one).compAddMonoidHom t) fun x => by
    rw [← AddChar.map_nsmul_eq_pow]
    simp
  rw [AddChar.compAddMonoidHom_apply, AddChar.zmodChar_apply, hζ.pow_eq_one_iff_dvd] at h1
  rw [← ZMod.val_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)
end GlobalTheory.ConjIdeal
