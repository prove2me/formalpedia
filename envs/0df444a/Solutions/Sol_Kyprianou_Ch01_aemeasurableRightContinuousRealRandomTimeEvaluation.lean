-- Prove2me | solution 1 for Kyprianou.Ch01.aemeasurableRightContinuousRealRandomTimeEvaluation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:48:16.260133+00:00
-- url     : https://prove2.me/submissions/46860ffb-ca50-4a71-a5da-75945534908e

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Sampling a process at a random finite time is almost-everywhere
measurable under fixed-time measurability and almost-sure right continuity. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (F t))
    (hRight : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => F s ω) (Set.Ici t) t)
    (T : Ω → ℝ≥0) (hT : Measurable T) :
    AEMeasurable (fun ω : Ω => F (T ω) ω) P := by
  let c : ℕ → ℝ≥0 → ℝ≥0 :=
    fun n t => (⌈t * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n
  have hc_ge : ∀ n t, t ≤ c n t := by
    intro n t
    simp only [c]
    rw [le_div_iff₀ (by positivity)]
    exact Nat.le_ceil _
  have hc_le : ∀ n t, c n t ≤ t + 1 / 2 ^ n := by
    intro n t
    simp only [c]
    rw [div_le_iff₀ (by positivity), add_mul, one_div,
      inv_mul_cancel₀ (by positivity)]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hPath : Measurable (fun ω : Ω => fun s : ℝ≥0 => F s ω) :=
    measurable_pi_iff.2 hMeas
  have hmeas : ∀ n : ℕ,
      Measurable (fun ω : Ω => F (c n (T ω)) ω) := by
    intro n
    have hGrid : Measurable (fun p : (ℝ≥0 → ℝ) × ℕ =>
        p.1 ((p.2 : ℝ≥0) / 2 ^ n)) :=
      measurable_from_prod_countable_left (fun k =>
        measurable_pi_apply ((k : ℝ≥0) / 2 ^ n))
    have hIndex : Measurable (fun ω : Ω => ⌈T ω * 2 ^ n⌉₊) :=
      Nat.measurable_ceil.comp (hT.mul_const _)
    change Measurable (fun ω : Ω =>
      F ((⌈T ω * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n) ω)
    exact hGrid.comp (hPath.prodMk hIndex)
  have ht : ∀ t : ℝ≥0,
      Tendsto (fun n => c n t) atTop (𝓝[Ici t] t) := by
    intro t
    refine tendsto_nhdsWithin_iff.2
      ⟨?_, Eventually.of_forall (fun n => hc_ge n t)⟩
    have hlim : Tendsto (fun n : ℕ => t + 1 / (2:ℝ≥0) ^ n)
        atTop (𝓝 t) := by
      have : Tendsto (fun n : ℕ => (1:ℝ≥0) / 2 ^ n)
          atTop (𝓝 0) := by
        simp only [one_div, ← inv_pow]
        exact tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num) (by norm_num)
      simpa using tendsto_const_nhds.add this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hlim (hc_ge · t) (hc_le · t)
  refine aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n => (hmeas n).aemeasurable) ?_
  filter_upwards [hRight] with ω hω
  exact (hω (T ω)).tendsto.comp (ht (T ω))
