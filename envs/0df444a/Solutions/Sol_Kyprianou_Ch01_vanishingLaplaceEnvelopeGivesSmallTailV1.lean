-- Prove2me | solution 1 for Kyprianou.Ch01.vanishingLaplaceEnvelopeGivesSmallTailV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:26:41.032171+00:00
-- url     : https://prove2.me/submissions/3a5c71f9-9365-4123-b9fd-be6ae3c5ae7d

import Mathlib
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (E : ℝ≥0 → Set Ω)
    (c : ℝ) (hc : 0 < c)
    (g : ℝ≥0 → ℝ)
    (hg : Tendsto g (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)))
    (hBound : ∀ s : ℝ≥0, 0 < s →
       c * (P (E s)).toReal ≤ g s)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ s : ℝ≥0, 0 < s ∧ (P (E s)).toReal < δ := by
  let sn : ℕ → ℝ≥0 :=
    fun n => (1 : ℝ≥0) / ((n : ℝ≥0) + 1)
  have hsn : Tendsto sn atTop (𝓝 (0 : ℝ≥0)) := by
    simpa [sn] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  have hlim : Tendsto (fun n => g (sn n)) atTop (𝓝 (0 : ℝ)) :=
    hg.comp hsn
  have hcδ : 0 < c * δ := mul_pos hc hδ
  have hEv : ∀ᶠ n : ℕ in atTop, g (sn n) < c * δ :=
    (tendsto_order.1 hlim).2 (c * δ) hcδ
  obtain ⟨n, hn⟩ := hEv.exists
  have hspos : 0 < sn n := by
    dsimp [sn]
    positivity
  have hLe : c * (P (E (sn n))).toReal ≤ g (sn n) :=
    hBound (sn n) hspos
  refine ⟨sn n, hspos, ?_⟩
  have hLt : c * (P (E (sn n))).toReal < c * δ :=
    lt_of_le_of_lt hLe hn
  exact lt_of_mul_lt_mul_left hLt hc.le
