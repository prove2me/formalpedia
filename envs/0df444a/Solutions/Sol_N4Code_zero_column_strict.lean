-- Prove2me | solution 1 for N4Code.zero_column_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:53.4937+00:00
-- url     : https://prove2.me/submissions/28e39c55-47f1-45ab-8743-bde436a0f2dd

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_witness_exists_C0form
import Theorems.Thm_N4Code_even_pair
import Theorems.Thm_N4Code_Columns07_normalize
import Theorems.Thm_N4Code_exists_col0_of_count_pos
import Theorems.Thm_N4Code_count0_normalize
import Theorems.Thm_N4Code_even_W_normalize
import Theorems.Thm_N4Code_notC0_normalize
import Theorems.Thm_N4Code_rowPermute_col0
import Theorems.Thm_N4Code_Y3c_move
import Theorems.Thm_N4Code_zero_column_strict_transfer

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (h0 : count C 0 ≥ 1)
    (hC0 : ¬ ∃ C0 : Code n, Equivalent C C0 ∧
      count C0 0 + count C0 5 + count C0 6 = n ∧
        Odd (count C0 5) ∧ Odd (count C0 6)) :
    ∃ t : Fin n, C t = col0 ∧ ∃ s' : Column,
      (colVal s' = 3 ∨ colVal s' = 5 ∨ colVal s' = 6) ∧
        UniversalStrictBetter (replaceColumn C t s') C := by
  rcases even_pair C with ⟨i, j, hij, hEven⟩
  let C' : Code n := normalizeCode C i j
  let ρ : Equiv (Fin 4) (Fin 4) := (permEven i j).symm
  let f : Fin n → Bool := fun t => (row C i) t
  have hh : ∀ u : Fin n, C' u = rowPermute ρ (if f u then flipCol (C u) else C u) := by
    intro u
    rfl
  have h07 : Columns07 C' := Columns07_normalize C i j hij
  have hcnt0 : 1 ≤ count C' 0 := count0_normalize C i j hij h0
  have hWeven : Even (count C' 4 + count C' 5 + count C' 6 + count C' 7) :=
    even_W_normalize C i j hij hEven
  have hnotC0 : ¬ C0form C' := notC0_normalize C i j (by simpa [C0form] using hC0)
  rcases witness_exists_C0form C' h07 hcnt0 hWeven hnotC0 with ⟨t', ht', hy'⟩
  rcases exists_col0_of_count_pos C h0 with ⟨t, htC⟩
  have htC' : C' t = col0 := by
    have hh' := hh t
    rw [htC] at hh'
    have hf : f t = false := by
      simp [f, row, colBit, htC, col0]
    rw [hf] at hh'
    simp at hh'
    rwa [rowPermute_col0] at hh'
  have hyT : ∃ y : Word n, Y3c C' col5 colZeros_col5_nonempty colOnes_col5_nonempty t y :=
    Y3c_move C' col5 colZeros_col5_nonempty colOnes_col5_nonempty t t' htC' ht' hy'
  exact ⟨t, htC, zero_column_strict_transfer C C' ρ f hh t htC htC' hyT⟩
end N4Code
