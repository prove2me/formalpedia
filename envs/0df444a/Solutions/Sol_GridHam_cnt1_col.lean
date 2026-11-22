-- Prove2me | solution 1 for GridHam.cnt1_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:16:18.572038+00:00
-- url     : https://prove2.me/submissions/f439c6c4-05dd-4cb8-9652-26d766cb9d33

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
public import Theorems.Thm_GridHam_cnt1_cons
public import Theorems.Thm_GridHam_cnt1_append

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (x : ℕ) : ∀ h, cnt1 ((List.range h).map (fun y => (x, y))) = (h + x % 2) / 2 := by
  intro h
  induction h with
  | zero =>
    rw [show cnt1 ((List.range 0).map (fun y => (x, y))) = 0 from rfl]
    omega
  | succ h ih =>
    rw [List.range_succ, List.map_append, cnt1_append, ih]
    have e : cnt1 (List.map (fun y => (x, y)) [h]) = (if (x + h) % 2 = 1 then 1 else 0) := by
      rw [show List.map (fun y => (x, y)) [h] = [(x, h)] from rfl, cnt1_cons]
      by_cases hc : (x + h) % 2 = 1 <;> simp [cnt1, parity, hc]
    rw [e]
    split_ifs <;> omega
end GridHam
