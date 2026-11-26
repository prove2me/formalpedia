-- Prove2me | solution 1 for N4Code.twobitCount_replace_0_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:32.248435+00:00
-- url     : https://prove2.me/submissions/2293174f-0460-43ef-a774-6386ba46cb7e

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_colVal_eq_zero_iff_col0
import Theorems.Thm_N4Code_colOfNat_colVal


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (h0 : C t = col0) :
    twobitCount (replaceColumn C t col5) = twobitCount C + 1 := by
  unfold twobitCount
  rw [Finset.card_filter, Finset.card_filter]
  have hsplit := sum_split_at (fun u : Fin n =>
      if colWeight ((replaceColumn C t col5) u) = 2 then 1 else 0) t
  have hsplitC := sum_split_at (fun u : Fin n =>
      if colWeight (C u) = 2 then 1 else 0) t
  have hcong : (∑ u ∈ (Finset.univ.erase t : Finset (Fin n)),
      if colWeight ((replaceColumn C t col5) u) = 2 then 1 else 0) =
      ∑ u ∈ (Finset.univ.erase t : Finset (Fin n)), if colWeight (C u) = 2 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    have hu' : u ≠ t := (Finset.mem_erase.mp hu).1
    simp [replaceColumn, hu']
  have ht1 : (if colWeight ((replaceColumn C t col5) t) = 2 then 1 else 0) = 1 := by
    have hw : colWeight col5 = 2 := by decide
    simp [replaceColumn, hw]
  have ht0 : (if colWeight (C t) = 2 then 1 else 0) = 0 := by
    have hcv : colVal (C t) = 0 := (colVal_eq_zero_iff_col0 (C t)).mpr h0
    have hw : colWeight (C t) = 0 := by
      rw [← colOfNat_colVal (C t), hcv]
      decide
    simp [hw]
  calc
    (∑ u : Fin n, if colWeight ((replaceColumn C t col5) u) = 2 then 1 else 0)
        = (∑ u ∈ (Finset.univ.erase t : Finset (Fin n)),
            if colWeight ((replaceColumn C t col5) u) = 2 then 1 else 0) + 1 := by
          rw [hsplit, ht1]
    _ = (∑ u ∈ (Finset.univ.erase t : Finset (Fin n)),
            if colWeight (C u) = 2 then 1 else 0) + 1 := by rw [hcong]
    _ = (∑ u : Fin n, if colWeight (C u) = 2 then 1 else 0) + 1 := by
          rw [hsplitC, ht0]
end N4Code
