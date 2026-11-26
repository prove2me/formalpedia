-- Prove2me | solution 1 for N4Code.IsLinear_all_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:02:10.521808+00:00
-- url     : https://prove2.me/submissions/9f7160f7-dab9-4944-8c64-0b40bcbf9aca

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
import Theorems.Thm_N4Code_colOfNat_colVal


set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (h : IsLinear C) : allEvenWeights C := by
  intro t
  rcases h.1 t with h0 | h3 | h5 | h6
  · have : colWeight (C t) = 0 := by
      rw [← colOfNat_colVal (C t), h0]
      decide
    rw [this]
    exact ⟨0, by omega⟩
  · have : colWeight (C t) = 2 := by
      rw [← colOfNat_colVal (C t), h3]
      decide
    rw [this]
    exact ⟨1, by omega⟩
  · have : colWeight (C t) = 2 := by
      rw [← colOfNat_colVal (C t), h5]
      decide
    rw [this]
    exact ⟨1, by omega⟩
  · have : colWeight (C t) = 2 := by
      rw [← colOfNat_colVal (C t), h6]
      decide
    rw [this]
    exact ⟨1, by omega⟩
end N4Code
