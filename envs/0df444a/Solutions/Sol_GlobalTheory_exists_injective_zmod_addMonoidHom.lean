-- Prove2me | solution 1 for GlobalTheory.exists_injective_zmod_addMonoidHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:40.755682+00:00
-- url     : https://prove2.me/submissions/5737ea86-8fa5-4f20-aba8-7bd7fd78ee50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteOfPerfectPairingZmod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function Cardinal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {a n : ℕ} (hn : n ≠ 0) (h : a ∣ n) :
    ∃ ι : ZMod a →+ ZMod n, Injective ι := by
  obtain ⟨k, rfl⟩ := h
  have ha : a ≠ 0 := left_ne_zero_of_mul hn
  have hk : k ≠ 0 := right_ne_zero_of_mul hn
  haveI : NeZero a := ⟨ha⟩
  refine ⟨ZMod.lift a ⟨zmultiplesHom (ZMod (a * k)) (k : ZMod (a * k)), ?_⟩, ?_⟩
  · simp only [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul]
    rw [← Nat.cast_mul, ZMod.natCast_self]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h2 : ((x.val : ℤ) : ZMod a) = x := by simp
    rw [← h2, ZMod.lift_coe] at hx
    simp only [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul] at hx
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hx
    have hd : a ∣ x.val := Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hk) hx
    have hv : x.val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt x)
    rw [← ZMod.natCast_zmod_val x, hv, Nat.cast_zero]
end GlobalTheory
