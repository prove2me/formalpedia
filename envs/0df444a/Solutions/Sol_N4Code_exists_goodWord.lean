-- Prove2me | solution 1 for N4Code.exists_goodWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:08.555488+00:00
-- url     : https://prove2.me/submissions/5576a1a0-2d22-44ba-92c7-71429fd150cb

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_goodTuples_card
import Theorems.Thm_N4Code_goodWord_iff
import Theorems.Thm_N4Code_goodWords_card


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (k : ℕ → ℕ)
    (hk : ∀ i ∈ Finset.Icc 0 15, k i ≤ count C i) :
    ∃ y : Word n, ∀ i ∈ Finset.Icc 0 15, w_i C i y = k i := by
  have hcard : 0 < (GoodWords C k).card := by
    rw [goodWords_card, goodTuples_card]
    have hone : 1 ≤ ∏ i ∈ Finset.Icc 0 15, Nat.choose (count C i) (k i) := by
      apply Finset.one_le_prod'
      intro i hi
      exact Nat.succ_le_of_lt (Nat.choose_pos (hk i hi))
    omega
  rcases Finset.card_pos.mp hcard with ⟨y, hy⟩
  exact ⟨y, (goodWord_iff C k y).1 hy⟩
end N4Code
