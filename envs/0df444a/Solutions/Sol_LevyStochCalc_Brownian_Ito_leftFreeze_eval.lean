-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.leftFreeze_eval
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T05:04:14.232704+00:00
-- url     : https://prove2.me/submissions/cab469bd-ed47-4b27-866e-39af81e3637e

import Definitions.Def_LevyStochCalc_Brownian_LeftFreeze_F000
open LevyStochCalc.Analysis LevyStochCalc.Brownian.Ito

theorem solution {Ω : Type*} [MeasurableSpace Ω] (Y : ℝ → Ω → ℝ) {C : ℝ}
    (hYb : ∀ s ω, |Y s ω| ≤ C) (hYm : ∀ s, Measurable (Y s))
    {t : ℝ} (ht : 0 < t) (n : ℕ) {s : ℝ} (hs : 0 < s) (hst : s ≤ t) (ω : Ω) :
    (leftFreeze Y hYb hYm ht n).eval s ω = Y (leftPt t n s) ω := by
  let k : Fin (2 ^ n) := ⟨leftIdx t n s, leftIdx_lt ht n hs hst⟩
  have hleft : dyadicPartition t n k.castSucc = leftPt t n s := rfl
  have hk : dyadicPartition t n k.castSucc < s ∧ s ≤ dyadicPartition t n k.succ := by
    rw [dyadicPartition_succ, hleft]
    exact ⟨leftPt_lt ht n hs, le_leftPt_add ht n hs⟩
  change (∑ j : Fin (2 ^ n), if dyadicPartition t n j.castSucc < s ∧
    s ≤ dyadicPartition t n j.succ then Y (dyadicPartition t n j.castSucc) ω else 0) = _
  rw [Finset.sum_eq_single k]
  · rw [if_pos hk, hleft]
  · intro j _ hj
    apply if_neg
    intro h
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · exact (not_lt_of_ge h.2) (((dyadicPartition_strictMono ht n).monotone
        (Fin.succ_le_castSucc_iff.mpr hlt)).trans_lt hk.1)
    · exact (not_lt_of_ge hk.2) (((dyadicPartition_strictMono ht n).monotone
        (Fin.succ_le_castSucc_iff.mpr hgt)).trans_lt h.1)
  · simp
