-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.allocation_sum_support_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:20:43.466976+00:00
-- url     : https://prove2.me/submissions/bbfd7061-4bfd-4a91-a6db-8e05f73222eb

import Mathlib.Tactic
import Definitions.Def_allocationSum
import Definitions.Def_allocationWeight
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_allocation_sum_filter_zero_coords
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_allocation_sum_support_reindex

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    OAI.PiExponent.LiteralAnalytic.allocationSum e k =
      OAI.PiExponent.LiteralAnalytic.allocationSum
        (fun i : {j : σ // e j ≠ 0} => e i.1) k := by
  rw [OAI.PiExponent.LiteralAnalytic.allocation_sum_filter_zero_coords,
    OAI.PiExponent.LiteralAnalytic.allocation_sum_support_reindex]