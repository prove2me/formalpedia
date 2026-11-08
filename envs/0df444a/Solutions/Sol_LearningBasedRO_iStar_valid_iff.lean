-- Prove2me | solution 1 for LearningBasedRO.iStar_valid_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:16:07.038254+00:00
-- url     : https://prove2.me/submissions/c8d78d1d-beea-4d16-9847-f67b0b8b0cc9

import Mathlib
import Definitions.Def_LearningBasedRO_Model

open MeasureTheory

open LearningBasedRO in
theorem solution (n₂ : ℕ) (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    ((iStarSet n₂ ϵ δ).Nonempty ↔ 1 - δ ≤ 1 - (1 - ϵ) ^ n₂) ∧
      (1 - δ ≤ 1 - (1 - ϵ) ^ n₂ ↔ Real.log δ / Real.log (1 - ϵ) ≤ (n₂ : ℝ)) := by
  have h1e : 0 ≤ 1 - ϵ := by linarith
  have hb : ∀ k, 0 ≤ binomTerm n₂ ϵ k := by
    intro k
    unfold binomTerm
    positivity
  have htot : ∑ k ∈ Finset.range (n₂ + 1), binomTerm n₂ ϵ k = 1 := by
    calc ∑ k ∈ Finset.range (n₂ + 1), binomTerm n₂ ϵ k
        = ∑ k ∈ Finset.range (n₂ + 1), (1 - ϵ) ^ k * ϵ ^ (n₂ - k) * (n₂.choose k : ℝ) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          unfold binomTerm
          ring
      _ = ((1 - ϵ) + ϵ) ^ n₂ := (add_pow _ _ _).symm
      _ = 1 := by rw [sub_add_cancel, one_pow]
  have hfull : ∑ k ∈ Finset.range n₂, binomTerm n₂ ϵ k = 1 - (1 - ϵ) ^ n₂ := by
    rw [Finset.sum_range_succ] at htot
    have hlast : binomTerm n₂ ϵ n₂ = (1 - ϵ) ^ n₂ := by simp [binomTerm]
    linarith
  have hmono : ∀ r, r ≤ n₂ → ∑ k ∈ Finset.range r, binomTerm n₂ ϵ k ≤
      ∑ k ∈ Finset.range n₂, binomTerm n₂ ϵ k := fun r hr =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hr) (fun k _ _ => hb k)
  constructor
  · constructor
    · rintro ⟨r, _, h2, h3⟩
      rw [← hfull]
      exact h3.trans (hmono r h2)
    · intro h
      rcases Nat.eq_zero_or_pos n₂ with h0 | h0
      · exfalso
        subst h0
        rw [pow_zero] at h
        linarith
      · exact ⟨n₂, h0, le_refl _, by rw [hfull]; exact h⟩
  · have hL : Real.log (1 - ϵ) < 0 := Real.log_neg (by linarith) (by linarith)
    have hpos : 0 < (1 - ϵ) ^ n₂ := pow_pos (by linarith) _
    rw [div_le_iff_of_neg hL, ← Real.log_pow, Real.log_le_log_iff hpos hδ0]
    constructor <;> intro h <;> linarith
