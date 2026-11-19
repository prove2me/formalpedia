-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.dgs_to_sivp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-18T22:51:04.752811+00:00
-- url     : https://prove2.me/submissions/e9ed27ee-20e7-404c-a4c8-a1661a107ab0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dyadic_sivp_scale_bound
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dgs_ideal_short_spanning_pool
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dgs_blind_dyadic_selection_mqpt

set_option autoImplicit false
open QAlgorithms.Complexity
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open scoped BigOperators Classical

theorem solution :
  ∃ C k : ℕ,1 ≤ C ∧ ∀ G : MFamily,IsMQPT G →
    ∀ error : ℕ → ℝ,Negligible error →
      ∃ A : MFamily,IsMQPT A ∧ ∃ cutoff : ℕ,∀ n ≥ cutoff,1 ≤ n →
        DGSAt G n (error n) →
          SolvesSIVP A (famN n) ((C : ℝ)*(famq n : ℝ)*Real.logb 2 ((n : ℝ)+2)^k) := by
  obtain ⟨C, k, d, hC, hscale⟩ := dyadic_sivp_scale_bound
  obtain ⟨n₀, hpool⟩ := dgs_ideal_short_spanning_pool
  refine ⟨C, k, hC, ?_⟩
  intro G hG error herr
  obtain ⟨A, hA, n₁, hsolve⟩ := dgs_blind_dyadic_selection_mqpt d G hG error herr
  refine ⟨A, hA, max n₀ n₁, ?_⟩
  intro n hn hpos hdgs
  change SolvesSIVP A n _
  apply hsolve n ((le_max_right n₀ n₁).trans hn) hpos hdgs
  intro B hB
  obtain ⟨j, hj, hthreshold, hnorm⟩ := hscale n hpos B hB
  exact ⟨j, hj, hthreshold, hnorm,
    hpool n ((le_max_left n₀ n₁).trans hn) hpos B hB _ (by positivity) hthreshold⟩
