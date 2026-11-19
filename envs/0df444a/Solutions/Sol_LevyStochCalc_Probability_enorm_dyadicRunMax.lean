-- Prove2me | solution 1 for LevyStochCalc.Probability.enorm_dyadicRunMax
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:57:43.237569+00:00
-- url     : https://prove2.me/submissions/8ad12999-2e62-4c0f-9329-2d4d9fb5d0ff

import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F000

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LevyStochCalc.Probability

theorem solution {Ω : Type*} (M : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) :
    (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)
      = ⨆ k : Fin (2 ^ n + 1), (‖M (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) := by
  apply le_antisymm
  · obtain ⟨k, hk, heq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
      (fun k => ‖M (dyadicTime T n k) ω‖)
    rw [Finset.mem_range] at hk
    have hnn : 0 ≤ dyadicRunMax M T n ω := dyadicRunMax_nonneg M T n ω
    have hnorm : ‖dyadicRunMax M T n ω‖ = ‖M (dyadicTime T n k) ω‖ := by
      rw [Real.norm_of_nonneg hnn, dyadicRunMax, heq]
    have hnnorm : (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) =
        (‖M (dyadicTime T n k) ω‖₊ : ℝ≥0∞) := by
      rw [ENNReal.coe_inj]
      ext
      exact hnorm
    rw [hnnorm]
    exact le_iSup (fun j : Fin (2 ^ n + 1) => (‖M (dyadicTime T n (j : ℕ)) ω‖₊ : ℝ≥0∞))
      ⟨k, hk⟩
  · refine iSup_le fun k => ?_
    have hle : ‖M (dyadicTime T n (k : ℕ)) ω‖ ≤ dyadicRunMax M T n ω :=
      Finset.le_sup' (f := fun j => ‖M (dyadicTime T n j) ω‖) (Finset.mem_range.mpr k.isLt)
    rw [ENNReal.coe_le_coe]
    change ‖M (dyadicTime T n (k : ℕ)) ω‖ ≤ ‖dyadicRunMax M T n ω‖
    rwa [Real.norm_of_nonneg (dyadicRunMax_nonneg M T n ω)]
