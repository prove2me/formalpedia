-- Prove2me | solution 1 for NoRegretLastIterate.eq_3_22
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:12:19.513471+00:00
-- url     : https://prove2.me/submissions/fff73c06-1f8c-4a1e-8b7b-ed8631f375d6

import Mathlib

open MeasureTheory Filter Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Q : ℕ → Ω → ℝ) {q : ℝ}
    (hq : 0 < q ∧ q < 1) (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => Q n ω) atTop (𝓝 q)) :
    ∀ᵐ ω ∂μ, ∀ γ' : ℝ, γ' < min (q * (2 - q) / 4) ((1 + q) * (1 - q) / 4) →
      ∀ᶠ t : ℕ in atTop, γ' ≤ (∑ s ∈ Finset.range t, Q s ω * (1 - Q s ω)) / t := by
  obtain ⟨hq0, hq1⟩ := hq
  have hmin : min (q * (2 - q) / 4) ((1 + q) * (1 - q) / 4) ≤ q * (1 - q) := by
    rcases le_total q (2 / 3) with h | h
    · exact le_trans (min_le_left _ _) (by nlinarith)
    · exact le_trans (min_le_right _ _) (by nlinarith)
  filter_upwards [hconv] with ω hω
  intro γ' hγ
  have h1 : Tendsto (fun n => Q n ω * (1 - Q n ω)) atTop (𝓝 (q * (1 - q))) :=
    hω.mul (tendsto_const_nhds.sub hω)
  have h2 := h1.cesaro
  have h3 : ∀ᶠ t : ℕ in atTop, γ' < (t⁻¹ : ℝ) * ∑ s ∈ Finset.range t, Q s ω * (1 - Q s ω) :=
    h2.eventually (lt_mem_nhds (lt_of_lt_of_le hγ hmin))
  filter_upwards [h3] with t ht
  rw [div_eq_inv_mul]
  exact ht.le
