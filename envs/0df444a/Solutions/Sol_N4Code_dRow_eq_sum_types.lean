-- Prove2me | solution 1 for N4Code.dRow_eq_sum_types
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:07.968981+00:00
-- url     : https://prove2.me/submissions/c4a02ed3-68fc-49ca-8264-22795ce496b2

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_w_i_eq_zero_of_count_zero
import Theorems.Thm_N4Code_count_eq_card
import Theorems.Thm_N4Code_dRow_eq_sum


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) (S : Finset ℕ)
    (hSle : S ⊆ Finset.Icc 0 15) (hS : ∀ t : Fin n, colVal (C t) ∈ S) :
    dRow C j y = ∑ i ∈ S, if i.testBit (3 - j.val) then count C i - w_i C i y else w_i C i y := by
  rw [dRow_eq_sum]
  symm
  apply Finset.sum_subset hSle
  intro i hi hnot
  have hcount : count C i = 0 := by
    rw [count_eq_card, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro t ht
    have hcv : colVal (C t) = i := (Finset.mem_filter.mp ht).2
    exact hnot (by simpa [hcv] using hS t)
  have hw : w_i C i y = 0 := w_i_eq_zero_of_count_zero C i y hcount
  simp [hcount, hw]
end N4Code
