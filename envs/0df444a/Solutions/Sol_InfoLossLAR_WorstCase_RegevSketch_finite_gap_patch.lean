-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.finite_gap_patch
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T08:54:00.559207+00:00
-- url     : https://prove2.me/submissions/7971ec59-4b0b-4bb4-98c3-43f9bfb90ae4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_finite_exact_gap
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_gap_dimension_dispatch

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase

open InfoLossLAR.WorstCase.RegevSketch

theorem solution (A : Family) (hA : IsQPT A) (cutoff : ℕ) (gamma : ℕ → ℝ)
    (hgamma : ∀ n, 1 ≤ n → 1 ≤ gamma n) :
    ∃ patched : Family, IsQPT patched ∧ ∀ n, 1 ≤ n →
      (cutoff ≤ n → SolvesGapSVP A (famN n) (gamma n)) →
        SolvesGapSVP patched (famN n) (gamma n) := by
  obtain ⟨E, hE, hExact⟩ := finite_exact_gap cutoff
  obtain ⟨P, hP, hDispatch⟩ := gap_dimension_dispatch E A hE hA cutoff
  refine ⟨P, hP, ?_⟩
  intro n hn hAabove B hB δ hδ
  by_cases hnsmall : n < cutoff
  · have hbase := hExact n hn hnsmall B hB δ hδ
    have hprob : acceptProb P (encGapInstance B δ) = acceptProb E (encGapInstance B δ) := by
      simpa [hnsmall] using hDispatch n B δ
    constructor
    · intro hy
      rw [hprob]
      exact hbase.1 hy
    · intro hn
      rw [hprob]
      apply hbase.2
      have hδreal : (0 : ℝ) ≤ δ := by exact_mod_cast hδ.le
      have hle : (δ : ℝ) ≤ gamma n * δ := by
        simpa using mul_le_mul_of_nonneg_right (hgamma n ‹1 ≤ n›) hδreal
      simpa only [one_mul] using hle.trans_lt hn
  · have hnlarge : cutoff ≤ n := Nat.le_of_not_gt hnsmall
    have hbase := hAabove hnlarge B hB δ hδ
    have hprob : acceptProb P (encGapInstance B δ) = acceptProb A (encGapInstance B δ) := by
      simpa [hnsmall] using hDispatch n B δ
    simpa [hprob] using hbase

