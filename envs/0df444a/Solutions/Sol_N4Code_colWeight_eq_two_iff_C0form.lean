-- Prove2me | solution 1 for N4Code.colWeight_eq_two_iff_C0form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:05.890003+00:00
-- url     : https://prove2.me/submissions/2989f1e0-7abd-4596-9e8b-7c133c960960

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_C0form_types
import Theorems.Thm_N4Code_colOfNat_colVal


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (h : C0form C) (t : Fin n) :
    colWeight (C t) = 2 ↔ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
  rcases C0form_types C h t with h0 | h5 | h6
  · have hw : colWeight (C t) = 0 := by
      rw [← colOfNat_colVal (C t), h0]
      decide
    constructor
    · intro h2
      omega
    · intro h56
      omega
  · have hw : colWeight (C t) = 2 := by
      rw [← colOfNat_colVal (C t), h5]
      decide
    constructor
    · intro _
      exact Or.inl h5
    · intro _
      exact hw
  · have hw : colWeight (C t) = 2 := by
      rw [← colOfNat_colVal (C t), h6]
      decide
    constructor
    · intro _
      exact Or.inr h6
    · intro _
      exact hw
end N4Code
