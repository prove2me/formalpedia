-- Prove2me | solution 1 for KWSpectrum.Estimator.rate_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T01:04:20.815316+00:00
-- url     : https://prove2.me/submissions/086de6c4-3455-498e-90e1-92aabd3c3c52

import Mathlib
import Definitions.Def_KWSpectrum_Estimator_Model

open QAlgorithms QAlgorithms.Schur KWSpectrum.Estimator

lemma kw_gibbs_term (s q : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q) (hsupp : 0 < s → 0 < q) :
    s - q ≤ s * Real.log (s / q) ∧ (s * Real.log (s / q) = s - q → s = q) := by
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨by simp [hq], fun h => ?_⟩
    simp at h; linarith
  · have hqp := hsupp hpos
    have hlog : Real.log (s / q) = - Real.log (q / s) := by
      rw [← Real.log_inv, inv_div]
    have h1 := Real.log_le_sub_one_of_pos (div_pos hqp hpos)
    have hmul : s * (q / s) = q := by field_simp
    refine ⟨?_, fun h => ?_⟩
    · rw [hlog]
      nlinarith
    · by_contra hne
      have h2 := Real.log_lt_sub_one_of_pos (div_pos hqp hpos)
        (by intro h'; rw [div_eq_one_iff_eq hpos.ne'] at h'; exact hne h'.symm)
      rw [hlog] at h
      nlinarith

lemma kw_gibbs {d : ℕ} (s q : Fin d → ℝ) (hs : ∀ j, 0 ≤ s j) (hq : ∀ j, 0 ≤ q j)
    (hsupp : ∀ j, 0 < s j → 0 < q j) (hsum : ∑ j, q j = ∑ j, s j) :
    0 ≤ ∑ j, s j * Real.log (s j / q j) ∧
      (∑ j, s j * Real.log (s j / q j) = 0 → s = q) := by
  have hterm := fun j => kw_gibbs_term (s j) (q j) (hs j) (hq j) (hsupp j)
  have hge : ∑ j, (s j - q j) ≤ ∑ j, s j * Real.log (s j / q j) :=
    Finset.sum_le_sum fun j _ => (hterm j).1
  have h0 : ∑ j, (s j - q j) = 0 := by rw [Finset.sum_sub_distrib, hsum, sub_self]
  refine ⟨by linarith, fun h => ?_⟩
  have hz : ∑ j, (s j * Real.log (s j / q j) - (s j - q j)) = 0 := by
    rw [Finset.sum_sub_distrib, h, h0, sub_self]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by linarith [(hterm j).1])] at hz
  funext j
  exact (hterm j).2 (by linarith [hz j (Finset.mem_univ _)])

theorem solution {d : ℕ} (r s : Fin d → ℝ) (hr : r ∈ SpectrumSet d)
    (hs : s ∈ SpectrumSet d) :
    0 ≤ rate r s ∧ (rate r s = 0 ↔ s = r) := by
  obtain ⟨_, hr0, hr1⟩ := hr
  obtain ⟨_, hs0, hs1⟩ := hs
  unfold rate
  split_ifs with h
  · refine ⟨le_top, ?_⟩
    obtain ⟨j, hj, hrj⟩ := h
    constructor
    · intro h'; exact absurd h' (by simp)
    · intro hsr; rw [hsr] at hj; linarith
  · push Not at h
    have hsupp : ∀ j, 0 < s j → 0 < r j := fun j hj =>
      lt_of_le_of_ne (hr0 j) (h j hj).symm
    have hg := kw_gibbs s r hs0 hr0 hsupp (by rw [hr1, hs1])
    refine ⟨EReal.coe_nonneg.mpr hg.1, ?_⟩
    rw [EReal.coe_eq_zero]
    refine ⟨hg.2, fun hsr => ?_⟩
    subst hsr
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : s j = 0
    · simp [hj]
    · simp [div_self hj]
