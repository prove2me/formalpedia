-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41DenseBlockCountV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:43:35.816154+00:00
-- url     : https://prove2.me/submissions/aa0585e3-f528-413a-b931-6126b2a69d97

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41FiniteBlockGridV4
import Theorems.Thm_Kyprianou_Ch04_exercise41IncreasingCountLimitV4
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (a δ : NNReal) (h : ℝ) (n : ℕ) (q : ℕ → NNReal)
    (hh : 0 < h) (hd : 0 < L.drift)
    (hw : (n : ℝ) * h ≤ (δ : ℝ))
    (hp : 0 < P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
      L.drift / 2 * (u : ℝ) ≤ L.X u ω}) :
    let A : ℕ → ℕ → Set Ω := fun m i =>
      {ω | ∃ k < m, (a : ℝ) + (i : ℝ) * h ≤ (q k : ℝ) ∧
        (q k : ℝ) < (a : ℝ) + ((i : ℝ) + 1) * h ∧
        |L.X (q k) ω| < L.drift * h / 8}
    let N : Ω → ℝ≥0∞ := fun ω =>
      ⨆ m : ℕ, ∑ i ∈ Finset.range n, (A m i).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω
    let p := P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
      L.drift / 2 * (u : ℝ) ≤ L.X u ω}
    Measurable N ∧ (∫⁻ ω, N ω ∂P) ≤ 2 / p := by
  letI : IsProbabilityMeasure P := L.isProbability
  dsimp only
  let A : ℕ → ℕ → Set Ω := fun m i =>
    {ω | ∃ k < m, (a : ℝ) + (i : ℝ) * h ≤ (q k : ℝ) ∧
      (q k : ℝ) < (a : ℝ) + ((i : ℝ) + 1) * h ∧
      |L.X (q k) ω| < L.drift * h / 8}
  let p := P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
    L.drift / 2 * (u : ℝ) ≤ L.X u ω}
  change Measurable (fun ω => ⨆ m : ℕ, ∑ i ∈ Finset.range n,
    (A m i).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω) ∧
    (∫⁻ ω, ⨆ m : ℕ, ∑ i ∈ Finset.range n,
      (A m i).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω ∂P) ≤ 2 / p
  have hf (m : ℕ) : (∀ i ∈ Finset.range n, MeasurableSet (A m i)) ∧
      p * ∑ i ∈ Finset.range n, P (A m i) ≤ 2 := by
    let D : ℕ → Finset NNReal := fun i =>
      ((Finset.range m).image q).filter fun t =>
        (a : ℝ) + (i : ℝ) * h ≤ (t : ℝ) ∧
          (t : ℝ) < (a : ℝ) + ((i : ℝ) + 1) * h
    have hc (i : ℕ) (_hi : i ∈ Finset.range n) (t : NNReal) (ht : t ∈ D i) :
        (a : ℝ) + (i : ℝ) * h ≤ (t : ℝ) ∧
        (t : ℝ) < (a : ℝ) + ((i : ℝ) + 1) * h :=
      (Finset.mem_filter.mp ht).2
    have hb (i : ℕ) (hi : i ∈ Finset.range n) (t : NNReal) (ht : t ∈ D i) :
        a ≤ t ∧ t < a + δ := by
      have hs := hc i hi t ht
      have hidx : (i : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hi)
      constructor
      · exact_mod_cast (show (a : ℝ) ≤ (t : ℝ) by nlinarith [Nat.cast_nonneg (α := ℝ) i])
      · exact_mod_cast (show (t : ℝ) < (a : ℝ) + (δ : ℝ) by nlinarith)
    have heq (i : ℕ) : {ω | ∃ t ∈ D i, |L.X t ω| < L.drift * h / 8} = A m i := by
      ext ω
      constructor
      · rintro ⟨t, ht, hx⟩
        obtain ⟨ht', hl, hu⟩ := Finset.mem_filter.mp ht
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht'
        exact ⟨k, Finset.mem_range.mp hk, hl, hu, hx⟩
      · rintro ⟨k, hk, hl, hu, hx⟩
        exact ⟨q k, Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩, hl, hu⟩, hx⟩
    have H := exercise41FiniteBlockGridV4 P F L (Finset.range n) D a δ h hh hd hb hc
    dsimp only at H
    simpa only [heq] using H
  apply exercise41IncreasingCountLimitV4 P (Finset.range n) A (2 / p)
  · intro m i hi
    exact (hf m).1 i hi
  · intro i hi m k hmk ω hω
    obtain ⟨j, hj, hl, hu, hx⟩ := hω
    exact ⟨j, hj.trans_le hmk, hl, hu, hx⟩
  · intro m
    apply (ENNReal.le_div_iff_mul_le (Or.inl hp.ne') (Or.inl (measure_ne_top P _))).2
    rw [mul_comm]
    exact (hf m).2
