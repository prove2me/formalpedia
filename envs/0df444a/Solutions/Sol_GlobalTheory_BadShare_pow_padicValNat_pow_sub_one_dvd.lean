-- Prove2me | solution 1 for GlobalTheory.BadShare.pow_padicValNat_pow_sub_one_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:05:22.425095+00:00
-- url     : https://prove2.me/submissions/ac45fb4b-a69e-4a97-bbcb-9401d873f256

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumPrimePowerPartPowSubOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare
private theorem padicValNat_pow_sub_one_eq_add (g d l : ℕ) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hd : d ≠ 0)
    (hl : l.Prime) (hlg : l ∣ g - 1) :
    padicValNat l (g ^ d - 1) = padicValNat l (g - 1) + padicValNat l d := by
  have := Fact.mk hl
  have hlg' : ¬ l ∣ g := by
    intro h
    have h' := Nat.dvd_sub h hlg
    have e : g - (g - 1) = 1 := by omega
    rw [e] at h'
    exact hl.one_lt.ne' (Nat.dvd_one.mp h')
  rcases hl.eq_two_or_odd' with rfl | hodd
  · have hx : ¬ (2 : ℤ) ∣ (g : ℤ) := by exact_mod_cast hlg'
    have h4' : (4 : ℤ) ∣ (g : ℤ) - 1 := by
      have := Int.natCast_dvd_natCast.mpr h4
      rwa [Nat.cast_sub (by omega : 1 ≤ g), Nat.cast_one, Nat.cast_ofNat] at this
    have key := Int.two_pow_sub_pow' d h4' hx
    rw [one_pow] at key
    have e1 : (g : ℤ) ^ d - 1 = ((g ^ d - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
      push_cast
      ring
    have e2 : (g : ℤ) - 1 = ((g - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ g)]
      push_cast
      ring
    have e3 : (2 : ℤ) = ((2 : ℕ) : ℤ) := rfl
    rw [e1, e2, e3, Int.natCast_emultiplicity, Int.natCast_emultiplicity, Int.natCast_emultiplicity] at key
    have hN : g ^ d - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hd (by omega))
    rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, padicValNat_eq_emultiplicity hN,
      padicValNat_eq_emultiplicity (by omega : g - 1 ≠ 0), padicValNat_eq_emultiplicity hd]
    exact key
  · have := padicValNat.pow_sub_pow hodd (by omega : 1 < g) hlg hlg' hd
    rwa [one_pow] at this
end GlobalTheory.BadShare
end

set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution (g d l : ℕ) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hd : d ≠ 0)
    (hl : l.Prime) (hlg : l ∣ g - 1) : l ^ padicValNat l (g ^ d - 1) ∣ d * (g - 1) := by
  rw [padicValNat_pow_sub_one_eq_add g d l hg h4 hd hl hlg, pow_add, mul_comm d]
  exact mul_dvd_mul pow_padicValNat_dvd pow_padicValNat_dvd
end GlobalTheory.BadShare
