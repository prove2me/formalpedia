-- Prove2me | solution 1 for Kyprianou.Ch07.unitOscillationSublinear_of_summableTails
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:09:53.59562+00:00
-- url     : https://prove2.me/submissions/fbe0271b-b787-4d44-b583-27e436c88236

import Mathlib
import Theorems.Thm_thm_5_8
import Definitions.Def_Kyprianou_Ch07_UnitTimeOscillationObservables

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hSum : ∀ k : ℕ, (∑' n : ℕ,
      P {ω : Ω | ((k : ℝ) + 1)⁻¹ * (n : ℝ) ≤
        |Kyprianou.Ch07.maximalUnitIncrement X n ω|}) ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => Kyprianou.Ch07.maximalUnitIncrement X n ω / (n : ℝ))
      atTop (nhds (0 : ℝ)) := by
  have hEvent (k : ℕ) :
      ∀ᵐ ω ∂P, ∀ᶠ n in (atTop : Filter ℕ),
        ¬ (|Kyprianou.Ch07.maximalUnitIncrement X n ω| ≥
          ((k : ℝ) + 1)⁻¹ * (n : ℝ)) := by
    let A : ℕ → Set Ω := fun n =>
      {ω | ((k : ℝ) + 1)⁻¹ * (n : ℝ) ≤
          |Kyprianou.Ch07.maximalUnitIncrement X n ω|}
    have hz : P (limsup A atTop) = 0 := thm_5_8 P A (hSum k)
    have hae : ∀ᵐ ω ∂P, ω ∉ limsup A atTop := by
      apply ae_iff.mpr
      simpa only [not_not, Set.setOf_mem_eq] using hz
    filter_upwards [hae] with ω hω
    have hnot : ∀ᶠ n in (atTop : Filter ℕ), ω ∉ A n :=
      Filter.not_frequently.mp
        (by simpa only [mem_limsup_iff_frequently_mem] using hω)
    simpa only [A, Set.mem_setOf_eq] using hnot
  have hAll :
      ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n in (atTop : Filter ℕ),
        ¬ (|Kyprianou.Ch07.maximalUnitIncrement X n ω| ≥
          ((k : ℝ) + 1)⁻¹ * (n : ℝ)) :=
    eventually_countable_forall.mpr hEvent
  filter_upwards [hAll] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hlim : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹)
      atTop (nhds (0 : ℝ)) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨k, hk⟩ :
      ∃ k : ℕ, ((k : ℝ) + 1)⁻¹ < ε :=
    (hlim.eventually (isOpen_Iio.mem_nhds hε)).exists
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hω k)
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hn_nat : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn_nat
  have hbound : |Kyprianou.Ch07.maximalUnitIncrement X n ω| <
      ((k : ℝ) + 1)⁻¹ * (n : ℝ) :=
    lt_of_not_ge (hN n (le_trans (le_max_left N 1) hn))
  have hbound' : |Kyprianou.Ch07.maximalUnitIncrement X n ω| <
      ε * (n : ℝ) :=
    lt_of_lt_of_le hbound
      (mul_le_mul_of_nonneg_right hk.le hn0.le)
  have hratio :
      |Kyprianou.Ch07.maximalUnitIncrement X n ω / (n : ℝ)| < ε := by
    rw [abs_div, abs_of_pos hn0]
    exact (div_lt_iff₀ hn0).mpr hbound'
  simpa only [Real.dist_eq, sub_zero] using hratio
