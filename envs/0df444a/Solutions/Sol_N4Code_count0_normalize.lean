-- Prove2me | solution 1 for N4Code.count0_normalize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:50.692928+00:00
-- url     : https://prove2.me/submissions/9e2b4442-14e6-4a0b-a9a3-d7e01611c253

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_exists_col0_of_count_pos
import Theorems.Thm_N4Code_count_eq_card


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (i j : Fin 4) (_hij : i ≠ j)
    (h : 1 ≤ count C 0) : 1 ≤ count (normalizeCode C i j) 0 := by
  rcases exists_col0_of_count_pos C h with ⟨t, ht⟩
  have ht' : normalizeCode C i j t = col0 := by
    unfold normalizeCode
    have hf : row C i t = false := by
      rw [row, colBit]
      simp [ht, col0]
    have hrp : rowPermute (permEven i j).symm col0 = col0 := by
      funext k
      simp [rowPermute, col0]
    simp [ht, hf, hrp]
  have hmem : t ∈ (Finset.univ.filter fun u : Fin n => colVal (normalizeCode C i j u) = 0) := by
    simp [ht', colVal, col0]
  have hcard : 1 ≤ (Finset.univ.filter fun u : Fin n => colVal (normalizeCode C i j u) = 0).card := by
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨t, hmem⟩)
  simpa [count_eq_card] using hcard
end N4Code
