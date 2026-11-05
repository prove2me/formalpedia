-- Prove2me | solution 1 for LL_Decomp1537b.Irho_one_one
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:16.809393+00:00
-- url     : https://prove2.me/submissions/b391af80-7092-4c46-a33c-ae5932645c42

import Mathlib
import Definitions.Def_LL_Decomp1537b_I1
import Definitions.Def_LL_Decomp1537b_Irho

open Finset Real

theorem solution (N N1 : ℕ) (h : ℤ) :
    LL_Decomp1537b.Irho N N1 h 1 1 = LL_Decomp1537b.I1 N N1 h := by
  unfold LL_Decomp1537b.Irho LL_Decomp1537b.I1
  simp
