-- Prove2me | solution 1 for GlobalTheory.IsKroneckerChar.apply_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:53:59.011982+00:00
-- url     : https://prove2.me/submissions/38e9b5da-dc9f-47c4-8c73-1f3811c8c780

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
theorem _root_.solution (hd : 0 < d) : χ (-1) = -1 := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  have h' : Odd (4 * k + 3) := ⟨2 * k + 1, by ring⟩
  have := hχ _ h'
  rw [← one_mul J(_ | _), ← jacobiSym.at_four h', ← jacobiSym.mul_left,
    jacobiSym.mod_left' (a₂ := -1) (by
      push_cast
      rw [show (4 : ℤ) * -(k + 1) = -1 - (4 * k + 3) by ring, Int.sub_emod_right]),
    jacobiSym.at_neg_one h', ZMod.χ₄_nat_three_mod_four (by omega)] at this
  have e : ((4 * k + 3 : ℕ) : ZMod (k + 1)) = -1 := by
    have := ZMod.natCast_self (k + 1)
    push_cast at this ⊢
    linear_combination 4 * this
  simpa [e] using this
end GlobalTheory.IsKroneckerChar
