-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_stable_integrated_coeff_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:34:26.984179+00:00
-- url     : https://prove2.me/submissions/a5a1ab8c-12fe-4ad5-821f-afc89d1e6a67

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_source_stable_ratio_lt_one
import Theorems.Thm_Kyprianou_Ch08_StageB_source_stable_integrated_term_factor
set_option autoImplicit false
open Kyprianou.Ch08.StageB

theorem solution (α q β : ℝ) (hα : 1 < α) (hq : 0 < q)
    (hβ : q ^ (1 / α) < β) :
    Summable (fun n : ℕ =>
      q ^ n * β ^ (-(α * (n + 1) + 1))) := by
  have hqroot : 0 ≤ q ^ (1 / α) := Real.rpow_nonneg hq.le _
  have hβ0 : 0 < β := lt_of_le_of_lt hqroot hβ
  obtain ⟨hρ0,hρ1⟩ := source_stable_ratio_lt_one α q β hα hq hβ
  have hs : Summable (fun n : ℕ =>
      β ^ (-(α + 1)) * (q / β ^ α)^n) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  exact hs.congr (fun n => by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (source_stable_integrated_term_factor α q β hβ0 n).symm)
