-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45CompactUniformLimitRightV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:36:37.981267+00:00
-- url     : https://prove2.me/submissions/2125e84b-74e7-442d-b4ef-1bf86740aa54

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Choose a single approximating path within a quarter of the desired accuracy on the compact horizon and use its right continuity at the interior time. -/
theorem solution
    (A : ℕ → NNReal → ℝ) (Z : NNReal → ℝ)
    (T t : NNReal) (ht : t < T)
    (hR : ∀ n : ℕ, ContinuousWithinAt (A n) (Ici t) t)
    (hU : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ s ≤ T, |A n s - Z s| ≤ δ) :
    ContinuousWithinAt Z (Ici t) t := by
  rw [ContinuousWithinAt,Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨n,hn⟩ := hU (δ/4) (by positivity)
  have hA := Metric.tendsto_nhds.mp (hR n) (δ/2) (by positivity)
  have hT : ∀ᶠ s in nhdsWithin t (Ici t), s < T :=
    nhdsWithin_le_nhds (Iio_mem_nhds ht)
  filter_upwards [hA,hT] with s hsA hsT
  have h₁ := hn n le_rfl s hsT.le
  have h₂ := hn n le_rfl t ht.le
  rw [Real.dist_eq] at hsA
  rw [Real.dist_eq]
  have h₃ : |Z s-A n s| ≤ δ/4 := by rw [abs_sub_comm]; exact h₁
  have h₄ : |Z s-Z t| ≤ |Z s-A n s|+(|A n s-A n t|+|A n t-Z t|) := by
    calc
      _ = |(Z s-A n s)+(A n s-Z t)| := by congr 1; ring
      _ ≤ |Z s-A n s|+|A n s-Z t| := abs_add_le _ _
      _ ≤ _ := add_le_add le_rfl (by
        calc
          _ = |(A n s-A n t)+(A n t-Z t)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _)
  linarith only [h₃,h₂,hsA,h₄]
