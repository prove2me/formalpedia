-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_head_through_degree_51
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:02:30.504594+00:00
-- url     : https://prove2.me/submissions/22d4fcc7-e93e-4f16-8c05-1c07266a9ac8

import Theorems.Thm_GrothendieckLB_Supplement_cq_taylor_bounds_of_integer_checks
import Theorems.Thm_GrothendieckLB_Supplement_cq_head_integer_comparisons_51
open GrothendieckLB GrothendieckLB.Supplement

theorem solution :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    (88157382204959954858 : ℝ)/10^20 ≤ taylorCoeff 1 H ∧
      ∀ j : ℕ, j < 25 → |taylorCoeff (2*j+3) H| ≤
        ((cqHeadUnits[j]?.getD 0 : ℕ) : ℝ)/10^20 := by
  have h := cq_taylor_bounds_of_integer_checks (n:=51) (by decide) (List.range 25)
    (fun j hj => by have := List.mem_range.mp hj; omega) cq_head_integer_comparisons_51
  exact ⟨h.1,fun j hj => h.2 j (List.mem_range.mpr hj)⟩
