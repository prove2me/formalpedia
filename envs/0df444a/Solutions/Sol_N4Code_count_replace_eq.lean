-- Prove2me | solution 1 for N4Code.count_replace_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:33.372649+00:00
-- url     : https://prove2.me/submissions/68a108c0-e176-46b8-8c67-9e5a9f3b35a8

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (s' : Column) (i : ℕ)
    (hc : colVal (C t) ≠ i) (hi' : colVal s' ≠ i) :
    count (replaceColumn C t s') i = count C i := by
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
  rw [hS, ht']
  simp [hi', hc]
end N4Code
