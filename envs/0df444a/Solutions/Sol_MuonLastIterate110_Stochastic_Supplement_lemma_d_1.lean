-- Prove2me | solution 1 for MuonLastIterate110.Stochastic.Supplement.lemma_d_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:59:55.37134+00:00
-- url     : https://prove2.me/submissions/83e73710-e092-45da-bc66-60d1d89ad37a

import Mathlib
import Definitions.Def_MuonLastIterate110_Stochastic_Supplement_DensityOne

open Filter Topology MuonLastIterate110.Stochastic.Supplement

lemma muon_bad (a : ℕ → ℝ) (p s c : ℝ) (hs : 0 < s) (hc : 0 < c) (t : ℕ) (ht : 1 ≤ t)
    (hbad : a t > c * (t : ℝ) ^ (-(1 - p) / s)) :
    c ^ s < (t : ℝ) * ((t : ℝ) ^ (-p) * a t ^ s) := by
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  set r := c * (t : ℝ) ^ (-(1 - p) / s) with hr
  have hr0 : 0 ≤ r := by positivity
  have h1 : r ^ s < a t ^ s := Real.rpow_lt_rpow hr0 hbad hs
  have h2 : r ^ s = c ^ s * (t : ℝ) ^ (-(1 - p)) := by
    rw [hr, Real.mul_rpow hc.le (by positivity), ← Real.rpow_mul htr.le]
    congr 2; field_simp
  have h3 : (t : ℝ) * (t : ℝ) ^ (-p) * (t : ℝ) ^ (-(1 - p)) = 1 := by
    rw [mul_assoc, ← Real.rpow_add htr, show -p + -(1 - p) = (-1 : ℝ) by ring,
      Real.rpow_neg_one, mul_inv_cancel₀ htr.ne']
  have hpos : 0 < (t : ℝ) * (t : ℝ) ^ (-p) := by positivity
  calc c ^ s = (t : ℝ) * (t : ℝ) ^ (-p) * r ^ s := by
        rw [h2]; linear_combination (-(c ^ s)) * h3
    _ < (t : ℝ) * (t : ℝ) ^ (-p) * a t ^ s := mul_lt_mul_of_pos_left h1 hpos
    _ = _ := by ring

theorem solution (a : ℕ → ℝ) (p s : ℝ)
    (ha : ∀ t : ℕ, 1 ≤ t → 0 ≤ a t) (hp : 0 ≤ p) (hp' : p < 1) (hs : 0 < s)
    (hsum : Summable (fun t : ℕ => ((t + 1 : ℕ) : ℝ) ^ (-p) * a (t + 1) ^ s)) :
    DensityOne a (fun t => (t : ℝ) ^ (-(1 - p) / s)) := by
  classical
  intro c hc
  set g : ℕ → ℝ := fun t => ((t + 1 : ℕ) : ℝ) ^ (-p) * a (t + 1) ^ s with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k => by
    have := ha (k + 1) (by omega)
    positivity
  have hcs : 0 < c ^ s := Real.rpow_pos_of_pos hc s
  have htail := tendsto_sum_nat_add g
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 htail) (ε * c ^ s / 2) (by positivity)
  have hK' : ∑' k, g (k + K) < ε * c ^ s / 2 := by
    have := hK K le_rfl
    rw [Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * K / ε)
  refine ⟨N + K + 1, fun T hT => ?_⟩
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  set bad := (Finset.Icc 1 T).filter (fun t => a t > c * (t : ℝ) ^ (-(1 - p) / s))
  -- split the bad set
  have hsplit : bad ⊆ Finset.Icc 1 K ∪ (Finset.Ioc K T).filter
      (fun t => a t > c * (t : ℝ) ^ (-(1 - p) / s)) := by
    intro t ht
    simp only [bad, Finset.mem_filter, Finset.mem_Icc] at ht
    by_cases htK : t ≤ K
    · exact Finset.mem_union_left _ (Finset.mem_Icc.2 ⟨ht.1.1, htK⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨by omega, ht.1.2⟩, ht.2⟩)
  set bad2 := (Finset.Ioc K T).filter (fun t => a t > c * (t : ℝ) ^ (-(1 - p) / s))
  have hcard1 : (bad.card : ℝ) ≤ K + bad2.card := by
    have := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact_mod_cast this
  -- bound bad2
  have hb2 : (bad2.card : ℝ) * c ^ s ≤ T * ∑' k, g (k + K) := by
    have h1 : (bad2.card : ℝ) * c ^ s = ∑ t ∈ bad2, c ^ s := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : ∀ t ∈ bad2, c ^ s ≤ T * ((t : ℝ) ^ (-p) * a t ^ s) := by
      intro t ht
      simp only [bad2, Finset.mem_filter, Finset.mem_Ioc] at ht
      have hb := muon_bad a p s c hs hc t (by omega) ht.2
      have hnn : 0 ≤ (t : ℝ) ^ (-p) * a t ^ s := by
        have := ha t (by omega); positivity
      have htT : (t : ℝ) ≤ T := by exact_mod_cast ht.1.2
      nlinarith
    have hnn : ∀ t ∈ Finset.Ioc K T, 0 ≤ (t : ℝ) ^ (-p) * a t ^ s := by
      intro t ht
      have := ha t (by simp at ht; omega); positivity
    have h3 : ∑ t ∈ bad2, (t : ℝ) ^ (-p) * a t ^ s ≤ ∑ t ∈ Finset.Ioc K T, (t : ℝ) ^ (-p) * a t ^ s :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun t ht _ => hnn t ht)
    have h4 : ∑ t ∈ Finset.Ioc K T, (t : ℝ) ^ (-p) * a t ^ s = ∑ k ∈ Finset.range (T - K), g (k + K) := by
      rw [Finset.sum_bij (fun t _ => t - K - 1)]
      · intro t ht; simp at ht ⊢; omega
      · intro t1 h1 t2 h2 h; simp at h1 h2; omega
      · intro k hk; refine ⟨k + K + 1, ?_, ?_⟩ <;> simp at hk ⊢ <;> omega
      · intro t ht
        simp at ht
        simp only [hg]
        have e : t - K - 1 + K + 1 = t := by omega
        rw [e]
    have h5 : ∑ k ∈ Finset.range (T - K), g (k + K) ≤ ∑' k, g (k + K) :=
      Summable.sum_le_tsum _ (fun k _ => hg0 _) ((summable_nat_add_iff K).2 hsum)
    calc (bad2.card : ℝ) * c ^ s = ∑ t ∈ bad2, c ^ s := h1
      _ ≤ ∑ t ∈ bad2, (T : ℝ) * ((t : ℝ) ^ (-p) * a t ^ s) := Finset.sum_le_sum h2
      _ = T * ∑ t ∈ bad2, (t : ℝ) ^ (-p) * a t ^ s := by rw [Finset.mul_sum]
      _ ≤ T * ∑' k, g (k + K) := by
          apply mul_le_mul_of_nonneg_left _ hTpos.le
          linarith
  have hb2' : (bad2.card : ℝ) / T < ε / 2 := by
    rw [div_lt_iff₀ hTpos]
    have : (bad2.card : ℝ) * c ^ s < ε / 2 * T * c ^ s := by
      calc (bad2.card : ℝ) * c ^ s ≤ T * ∑' k, g (k + K) := hb2
        _ < T * (ε * c ^ s / 2) := mul_lt_mul_of_pos_left hK' hTpos
        _ = ε / 2 * T * c ^ s := by ring
    exact lt_of_mul_lt_mul_right this hcs.le
  have hK2 : (K : ℝ) / T < ε / 2 := by
    rw [div_lt_iff₀ hTpos]
    have hTN : (N : ℝ) < T := by exact_mod_cast (show N < T by omega)
    have : 2 * K / ε < T := lt_trans hN hTN
    rw [div_lt_iff₀ hε] at this
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  calc (bad.card : ℝ) / T ≤ (K + bad2.card) / T := div_le_div_of_nonneg_right hcard1 hTpos.le
    _ = K / T + bad2.card / T := by rw [add_div]
    _ < ε / 2 + ε / 2 := add_lt_add hK2 hb2'
    _ = ε := by ring
