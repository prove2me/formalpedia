-- Prove2me | solution 1 for MinSumDimRed.Doubling.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T16:17:25.467165+00:00
-- url     : https://prove2.me/submissions/10f768b8-e709-42c6-972b-d1661534ee3f

import Mathlib
import Definitions.Def_MinSumDimRed_Doubling_Costs

open MinSumDimRed.Doubling

theorem solution {d : ℕ} (S : Finset (Pt d)) (c : Pt d) (hc : IsOneMedianCenter S c) :
    (S.card : ℝ) * ∑ y ∈ S, ‖y - c‖ ≤ ∑ y ∈ S, ∑ y' ∈ S, ‖y - y'‖ := by
  rw [Finset.sum_comm, ← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum (fun y' _ => hc y')
