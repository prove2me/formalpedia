-- Prove2me | solution 1 for N4Code.dRow_eq_indicator_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:24.723545+00:00
-- url     : https://prove2.me/submissions/805c2875-f4dc-41ad-b135-a499943fac95

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
import Theorems.Thm_N4Code_dRow_eq_hammingDist


set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) :
    dRow C j y = ∑ t : Fin n, if colBit j (C t) ≠ y t then 1 else 0 := by
  rw [dRow_eq_hammingDist]
  unfold hammingDist hammingWeight
  apply Finset.sum_congr rfl
  intro t _
  cases hb : C t j <;> cases hy : y t <;>
    simp [hy, bitXor, row, colBit]
end N4Code
