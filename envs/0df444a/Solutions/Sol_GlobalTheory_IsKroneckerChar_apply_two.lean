-- Prove2me | solution 1 for GlobalTheory.IsKroneckerChar.apply_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:53:59.938792+00:00
-- url     : https://prove2.me/submissions/697c251e-f87e-483e-b834-1a13ecb5d0cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr

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
open GlobalTheory.IsKroneckerChar
variable {d : ℕ} {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ)
include hχ
namespace GlobalTheory.IsKroneckerChar
theorem _root_.solution (h4 : d % 4 ≠ 1) : χ 2 = (ZMod.χ₈ ((-(d : ℤ) : ℤ) : ZMod 8) : ℤ) := by
  rcases Nat.even_or_odd d with h | h
  · rw [MulChar.map_nonunit, (ZMod.χ₈_int_eq_if_mod_eight _),
      if_pos (by obtain ⟨k, rfl⟩ := h; omega)]
    · simp
    · rw [show (2 : ZMod d) = ((2 : ℕ) : ZMod d) by simp, ZMod.isUnit_iff_coprime,
        Nat.coprime_two_left, Nat.not_odd_iff_even]
      exact h
  · have h' : Odd (d + 2) := h.add_even even_two
    have := hχ _ h'
    rw [jacobiSym.mod_left' (a₂ := 2) (by
      push_cast
      rw [show (2 : ℤ) = -d + (d + 2) by ring, show (d : ℤ) + (-d + (d + 2)) = d + 2 by ring,
        Int.add_emod_right]), jacobiSym.at_two h'] at this
    rw [Nat.odd_iff] at h
    rw [show (2 : ZMod d) = ((d + 2 : ℕ) : ZMod d) by simp, this, ZMod.χ₈_int_eq_if_mod_eight,
      ZMod.χ₈_nat_eq_if_mod_eight]
    congr 1
    split_ifs <;> omega
end GlobalTheory.IsKroneckerChar
