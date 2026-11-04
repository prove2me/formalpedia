-- Prove2me | solution 1 for List.getD_flatMap_finRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:01:51.714463+00:00
-- url     : https://prove2.me/submissions/871b84c5-ab9a-48a5-b499-9c7013d3c3d3

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
public import Theorems.Thm_List_getD_flatMap_range

set_option autoImplicit false
public section
open List
variable {α β : Type*}
namespace List
theorem _root_.solution {n k : ℕ} (f : Fin n → List α) (hf : ∀ i, (f i).length = k)
    (i : Fin n) {r : ℕ} (hr : r < k) (d : α) :
    ((List.finRange n).flatMap f).getD ((i : ℕ) * k + r) d = (f i).getD r d := by
  have hrange : (List.finRange n).flatMap f =
      (List.range n).flatMap fun z => if h : z < n then f ⟨z, h⟩ else [] := by
    rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
    exact List.flatMap_congr fun j _ => by simp
  rw [hrange, getD_flatMap_range _ (fun z hz => by simp [hz, hf]) i.isLt hr]
  simp
end List
