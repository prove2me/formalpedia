-- Prove2me | solution 1 for GlobalTheory.exists_isKroneckerChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:42:20.501824+00:00
-- url     : https://prove2.me/submissions/8db5903b-c4c3-41a9-84df-25e673c9c116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Theorems.Thm_GlobalTheory_isKroneckerChar_of_jacobiSym

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory
open QuadraticZeta
namespace GlobalTheory
theorem _root_.solution {d : ℕ} (hd0 : d ≠ 0) (hd : d % 4 = 0 ∨ d % 4 = 3) :
    ∃ χ : DirichletCharacter ℂ d, IsKroneckerChar χ := by
  haveI : NeZero d := ⟨hd0⟩
  rcases hd with hd | hd
  · obtain ⟨k, hk⟩ : 4 ∣ d := Nat.dvd_of_mod_eq_zero hd
    let f : ℕ → ℤ := fun n => if Odd n then J(-(d : ℤ) | n) else 0
    have hf : ∀ n, f (n % d) = f n := fun n => by
      have : Odd (n % d) ↔ Odd n := by
        rw [Nat.odd_iff, Nat.odd_iff, Nat.mod_mod_of_dvd _ ⟨2 * k, by omega⟩]
      simp only [f, this]
      split_ifs with h
      · have e : -(d : ℤ) = 4 * -k := by rw [hk]; push_cast; ring
        rw [e, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.at_four h,
          jacobiSym.at_four (this.2 h), jacobiSym.mod_right _ h, hk]
        simp
      · rfl
    refine ⟨⟨⟨⟨fun x => f x.val, ?_⟩, fun x y => ?_⟩, fun x hx => ?_⟩, fun n hn => ?_⟩
    · rw [← Nat.cast_one (R := ZMod d), ZMod.val_natCast, hf]
      simp [f]
    · simp only [ZMod.val_mul, hf, f, Nat.odd_mul]
      by_cases h1 : Odd x.val <;> by_cases h2 : Odd y.val <;> simp [h1, h2]
      rw [jacobiSym.mul_right' _ h1.pos.ne' h2.pos.ne', Int.cast_mul]
    · simp only [f]
      split_ifs with h
      · rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime] at hx
        rw [Int.cast_eq_zero, jacobiSym.eq_zero_iff]
        exact ⟨h.pos.ne', by rwa [Int.neg_gcd, Int.gcd_natCast_natCast, Nat.gcd_comm]⟩
      · simp
    · change ((f (n : ZMod d).val : ℤ) : ℂ) = _
      rw [ZMod.val_natCast, hf]
      simp [f, hn]
  · have hf : ∀ n : ℕ, J(((n % d : ℕ) : ℤ) | d) = J(n | d) := fun n => by
      rw [jacobiSym.mod_left n]; simp
    refine ⟨⟨⟨⟨fun x => (J(x.val | d) : ℤ), ?_⟩, fun x y => ?_⟩, fun x hx => ?_⟩,
      isKroneckerChar_of_jacobiSym hd fun n => ?_⟩
    · rw [← Nat.cast_one (R := ZMod d), ZMod.val_natCast, hf]
      simp
    · simp only [ZMod.val_mul, hf]
      rw [Nat.cast_mul, jacobiSym.mul_left, Int.cast_mul]
    · rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime] at hx
      change ((J(x.val | d) : ℤ) : ℂ) = 0
      rw [Int.cast_eq_zero, jacobiSym.eq_zero_iff]
      exact ⟨hd0, by rwa [Int.gcd_natCast_natCast]⟩
    · change ((J((n : ZMod d).val | d) : ℤ) : ℂ) = _
      rw [ZMod.val_natCast, hf]
end GlobalTheory
