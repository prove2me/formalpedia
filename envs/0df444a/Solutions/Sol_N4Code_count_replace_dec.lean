-- Prove2me | solution 1 for N4Code.count_replace_dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:26.611452+00:00
-- url     : https://prove2.me/submissions/060fe87b-072c-49fd-8259-31fcf1a4741d

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (i : ℕ)
    (hc : colVal (C t) = i) (hi' : colVal s' ≠ i) :
    count (replaceColumn C t s') i = count C i - 1 := by
  unfold count
  have hsplit := sum_split_at
    (fun u : Fin n => if colVal (replaceColumn C t s' u) = i then 1 else 0) t
  rw [hsplit]
  have hS : (∑ u ∈ (Finset.univ.erase t),
      if colVal (replaceColumn C t s' u) = i then 1 else 0) =
      ∑ u ∈ (Finset.univ.erase t), if colVal (C u) = i then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    have hu' : u ≠ t := (Finset.mem_erase.mp hu).1
    simp [replaceColumn, hu']
  have ht' : colVal (replaceColumn C t s' t) = colVal s' := by
    simp [replaceColumn]
  have hsplit2 := sum_split_at (fun u : Fin n => if colVal (C u) = i then 1 else 0) t
  rw [hsplit2]
  rw [hS, ht', hc]
  simp [hi']
end N4Code
