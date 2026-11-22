-- Prove2me | solution 1 for GridHam.cnt1_grid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:19:44.289977+00:00
-- url     : https://prove2.me/submissions/691fb222-b9d3-4dd5-9000-d86c4cbf2e41

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
public import Theorems.Thm_GridHam_cnt1_append
public import Theorems.Thm_GridHam_cnt1_col
public import Theorems.Thm_GridHam_allCoords_succ

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (h : ℕ) (hh : h % 2 = 1) : ∀ w, 2 * cnt1 (allCoords w h) + w % 2 = w * h := by
  intro w
  induction w with
  | zero => simp [allCoords, cnt1]
  | succ w ih =>
    rw [allCoords_succ, cnt1_append, cnt1_col, Nat.add_mul, Nat.one_mul]
    omega
end GridHam
