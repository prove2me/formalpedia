-- Prove2me | solution 1 for N4Code.col0_of_normalize_col0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:15.182162+00:00
-- url     : https://prove2.me/submissions/a6ad7aff-d695-435d-868a-9ea241525e0a

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_rowPermute_symm
import Theorems.Thm_N4Code_rowPermute_col0

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (i j : Fin 4) (t : Fin n)
    (h0n : (normalizeCode C i j) t = col0) (hf : (row C i) t = false) : C t = col0 := by
  set ρ := (permEven i j).symm
  have h : rowPermute ρ (C t) = col0 := by
    unfold normalizeCode at h0n
    simpa [hf] using h0n
  have hinv : C t = rowPermute (permEven i j) col0 := by
    have := congr_arg (rowPermute (permEven i j)) h
    rw [rowPermute_symm] at this
    exact this
  rw [hinv, rowPermute_col0]
end N4Code
