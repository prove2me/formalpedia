-- Prove2me | solution 1 for Malliavin.integral_cov_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:24.60799+00:00
-- url     : https://prove2.me/submissions/169d4c39-950c-4c37-b7c2-7d9785fa8050

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral
import Theorems.Thm_Malliavin_integral_cov_incr_before
import Theorems.Thm_Malliavin_integral_cov_incr_after
import Theorems.Thm_Malliavin_integral_cov_incr_self
import Theorems.Thm_Malliavin_partition_succ_le_castSucc

set_option autoImplicit false
open Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
variable {W : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hW : IsWienerCov W) {n : ℕ} (P : Partition n) (i j : Fin n) :
    ∫ z, (W (P.t i.succ) z - W (P.t i.castSucc) z) *
          (W (P.t j.succ) z - W (P.t j.castSucc) z)
      = if i = j then (P.t i.succ : ℝ) - (P.t i.castSucc : ℝ) else 0 := by
  have hci : P.t i.castSucc ≤ P.t i.succ := P.mono.monotone (Fin.castSucc_le_succ i)
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    exact integral_cov_incr_self hW hci
  · rw [if_neg h]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · exact integral_cov_incr_after hW hci (partition_succ_le_castSucc P hlt)
        (P.mono.monotone (Fin.castSucc_le_succ j))
    · exact integral_cov_incr_before hW (partition_succ_le_castSucc P hgt) hci
        (P.mono.monotone (Fin.castSucc_le_succ j))
end Malliavin
