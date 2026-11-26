-- Prove2me | solution 1 for N4Code.sum_counts_4_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:48.732234+00:00
-- url     : https://prove2.me/submissions/66a2968a-b0a7-4cfe-b492-c8fed7cf1571

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_Columns07_le7
import Theorems.Thm_N4Code_testBit2_of_le7
import Theorems.Thm_N4Code_colBit_eq_testBit


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    count C 4 + count C 5 + count C 6 + count C 7 = hammingWeight (row C 1) := by
  have hcomb : count C 4 + count C 5 + count C 6 + count C 7 =
      ∑ t : Fin n, (if colVal (C t) = 4 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 ∨ colVal (C t) = 7
        then 1 else 0) := by
    unfold count
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h4 : colVal (C t) = 4 <;> by_cases h5 : colVal (C t) = 5 <;>
      by_cases h6 : colVal (C t) = 6 <;> by_cases h7 : colVal (C t) = 7 <;>
        simp [h4, h5, h6, h7]
  rw [hcomb]
  unfold hammingWeight row
  change (∑ t : Fin n, if colVal (C t) = 4 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 ∨ colVal (C t) = 7
      then 1 else 0) =
      ∑ t : Fin n, if colBit 1 (C t) then 1 else 0
  apply Finset.sum_congr rfl
  intro t _
  have hb := colBit_eq_testBit (C t) ⟨1, by decide⟩
  have hle := Columns07_le7 C h07 t
  have hiff : (colVal (C t) = 4 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 ∨ colVal (C t) = 7) ↔
      colBit 1 (C t) = true := by
    have htb := testBit2_of_le7 (colVal (C t)) hle
    have hb' : colBit 1 (C t) = (colVal (C t)).testBit 2 := by simpa using hb
    rwa [← hb'] at htb
  simp [hiff]
end N4Code
