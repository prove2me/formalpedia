-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45OuterUCPPrefixLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:24:12.22059+00:00
-- url     : https://prove2.me/submissions/71c9cc61-00e2-4f9d-83e7-e1e898d30753

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Uniform convergence in outer probability preserves agreement on a random prefix. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G J : NNReal → ℕ → NNReal → Ω → ℝ)
    (I L : NNReal → Ω → ℝ) (τ : Ω → NNReal)
    (hG : ∀ T ε, 0 < ε → Tendsto
      (fun j => (P {w | ∃ t ≤ T, ε ≤ |G T j t w - I t w|}).toReal)
      atTop (nhds 0))
    (hJ : ∀ T ε, 0 < ε → Tendsto
      (fun j => (P {w | ∃ t ≤ T, ε ≤ |J T j t w - L t w|}).toReal)
      atTop (nhds 0))
    (hEq : ∀ᵐ w ∂P, ∀ T j t, t ≤ τ w → G T j t w = J T j t w) :
    ∀ᵐ w ∂P, ∀ t ≤ τ w, I t w = L t w := by
  have hsmall (n m : ℕ) : ∀ᵐ w ∂P, ∀ t ≤ (n : NNReal), t ≤ τ w →
      |I t w - L t w| < 2 * (1 / (m + 1 : ℝ)) := by
    let ε : ℝ := 1 / (m+1 : ℝ)
    have hε : 0 < ε := by dsimp [ε]; positivity
    let E := {w | ¬ ∀ t ≤ (n : NNReal), t ≤ τ w → |I t w - L t w| < 2*ε}
    let A (j : ℕ) := {w | ∃ t ≤ (n : NNReal), ε ≤ |G n j t w - I t w|}
    let B (j : ℕ) := {w | ∃ t ≤ (n : NNReal), ε ≤ |J n j t w - L t w|}
    have hb (j : ℕ) : P E ≤ P (A j) + P (B j) := by
      apply le_trans _ (measure_union_le _ _)
      apply measure_mono_ae
      filter_upwards [hEq] with w hw
      intro he
      change ¬ ∀ t ≤ (n : NNReal), t ≤ τ w → |I t w - L t w| < 2*ε at he
      push Not at he
      obtain ⟨t,ht,hτ,hd⟩ := he
      by_contra hn
      have ha : |G n j t w - I t w| < ε := by
        exact lt_of_not_ge (fun h => hn (Or.inl ⟨t,ht,h⟩))
      have hc : |J n j t w - L t w| < ε := by
        exact lt_of_not_ge (fun h => hn (Or.inr ⟨t,ht,h⟩))
      rw [← hw n j t hτ] at hc
      have htri : |I t w - L t w| ≤ |G n j t w - I t w| + |G n j t w - L t w| := by
        rw [abs_sub_comm (G n j t w) (I t w)]
        exact abs_sub_le _ _ _
      linarith
    have hbr (j : ℕ) : (P E).toReal ≤ (P (A j)).toReal + (P (B j)).toReal := by
      have h := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨measure_ne_top P _, measure_ne_top P _⟩) (hb j)
      rwa [ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _)] at h
    have hlim : (P E).toReal ≤ 0 := by
      have hlim : Tendsto (fun j => (P (A j)).toReal + (P (B j)).toReal) atTop (nhds 0) := by
        simpa only [add_zero] using (hG n ε hε).add (hJ n ε hε)
      exact ge_of_tendsto hlim (Eventually.of_forall hbr)
    have hz : P E = 0 := by
      exact ((ENNReal.toReal_eq_zero_iff (P E)).mp (le_antisymm hlim ENNReal.toReal_nonneg)).resolve_right
        (measure_ne_top P _)
    exact ae_iff.mpr hz
  have hall : ∀ᵐ w ∂P, ∀ n m : ℕ, ∀ t ≤ (n : NNReal), t ≤ τ w →
      |I t w - L t w| < 2 * (1 / (m + 1 : ℝ)) :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr (hsmall n)
  filter_upwards [hall] with w hw
  intro t ht
  obtain ⟨n,hn⟩ := exists_nat_gt t
  by_contra hne
  have hp : 0 < |I t w - L t w| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt (show 0 < |I t w - L t w| / 2 by positivity)
  have h := hw n m t hn.le ht
  linarith
