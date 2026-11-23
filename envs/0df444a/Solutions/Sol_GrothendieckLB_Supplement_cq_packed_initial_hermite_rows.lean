-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_packed_initial_hermite_rows
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:07:42.01647+00:00
-- url     : https://prove2.me/submissions/bff70c97-e501-436d-9877-7d12d0cf3469
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_cq_initial_hermite_transform_moment_0
import Theorems.Thm_GrothendieckLB_Supplement_cq_initial_hermite_transform_moment_2
import Theorems.Thm_GrothendieckLB_Supplement_cq_initial_hermite_transform_moment_4
open GrothendieckLB.Supplement CQHeadArithmetic CQHeadCertificate

theorem solution : ∀ c : ℕ, c < 24 → firstChecks c=true := by
  intro c _
  apply List.all_eq_true.mpr
  intro j _
  let n := 16*c+j
  change (if 2*n < 754 then startOK (2*n) else true)=true
  split
  · rename_i hn
    have h : n < 377 := by omega
    unfold startOK
    rw [if_pos (show (2*n)%2=0 by omega)]
    apply decide_eq_true
    have A := cq_initial_hermite_transform_moment_0 n h
    have B := cq_initial_hermite_transform_moment_2 n h
    have C := cq_initial_hermite_transform_moment_4 n h
    have extI (u v : MomentCombination) (a : u.e0=v.e0) (b : u.e2=v.e2) (c : u.e4=v.e4) : u=v := by
      cases u; cases v; congr
    exact extI _ _ A B C
  · rfl
