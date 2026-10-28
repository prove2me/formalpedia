-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_of_tendsto_lintegral_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:22:00.539627+00:00
-- url     : https://prove2.me/submissions/7e3234f0-1872-4f32-8341-ff6a85e8f951

import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedClamp
import Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_of_tendsto_sq_enorm_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
section Clamped
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
section ClampProcess
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ')
/-- If the integrals of a sequence of nonnegative functions are summable, their sum is finite
almost everywhere. -/
theorem LevyStochCalc.Brownian.Ito.ae_tsum_ne_top_of_lintegral_summable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : ℕ → α → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (hsum : ∑' i : ℕ, ∫⁻ a, g i a ∂μ ≠ ⊤) : ∀ᵐ a ∂μ, ∑' i : ℕ, g i a ≠ ⊤ := by
  have h1 : ∫⁻ a, ∑' i : ℕ, g i a ∂μ ≠ ⊤ := by
    rw [MeasureTheory.lintegral_tsum fun i => (hg i).aemeasurable]
    exact hsum
  filter_upwards [MeasureTheory.ae_lt_top (Measurable.tsum hg) h1] with a ha
  exact ha.ne
/-- If the integrals of a sequence of nonnegative functions are summable, the functions tend to
zero almost everywhere. -/
theorem LevyStochCalc.Brownian.Ito.ae_tendsto_zero_of_lintegral_summable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : ℕ → α → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (hsum : ∑' i : ℕ, ∫⁻ a, g i a ∂μ ≠ ⊤) :
    ∀ᵐ a ∂μ, Filter.Tendsto (fun i => g i a) Filter.atTop (𝓝 0) := by
  filter_upwards [ae_tsum_ne_top_of_lintegral_summable hg hsum] with a ha
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top ha
/-- A sequence tending to zero drops below the geometric thresholds along indices that grow. -/
theorem LevyStochCalc.Brownian.Ito.exists_seq_lt_of_tendsto_zero {u : ℕ → ℝ≥0∞}
    (h : Filter.Tendsto u Filter.atTop (𝓝 0)) :
    ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧ ∀ i : ℕ, u (ms i) < ((2 : ℝ≥0∞)⁻¹) ^ i := by
  have hchoice : ∀ i : ℕ, ∃ j : ℕ, i ≤ j ∧ u j < ((2 : ℝ≥0∞)⁻¹) ^ i := by
    intro i
    have hpos : (0 : ℝ≥0∞) < ((2 : ℝ≥0∞)⁻¹) ^ i := by
      refine pos_iff_ne_zero.mpr (pow_ne_zero i ?_)
      simp
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h.eventually (gt_mem_nhds hpos))
    exact ⟨max N i, le_max_right N i, hN (max N i) (le_max_left N i)⟩
  choose ms hge hms using hchoice
  exact ⟨ms, hge, hms⟩
/-- The geometric bound the summability argument uses. -/
theorem LevyStochCalc.Brownian.Ito.tsum_geometric_inv_two_mul_ne_top (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    ∑' i : ℕ, c * ((2 : ℝ≥0∞)⁻¹) ^ i ≠ ⊤ := by
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  refine ne_of_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc) ?_)
  have hne : (1 : ℝ≥0∞) - 2⁻¹ ≠ 0 := by
    rw [Ne, tsub_eq_zero_iff_le]
    exact not_le.mpr (ENNReal.inv_lt_one.mpr (by norm_num))
  exact lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hne)
omit [IsProbabilityMeasure P] in
/-- A finite family of sequences converging in `L²` converges almost everywhere along a common
subsequence. -/
theorem solution {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type*} [Finite ι] {u : ℕ → ι → α → ℝ} {v : ι → α → ℝ}
    (hu : ∀ (i : ℕ) (c : ι), Measurable (u i c)) (hv : ∀ c : ι, Measurable (v c))
    (h : ∀ c : ι, Filter.Tendsto (fun i : ℕ => ∫⁻ a, (‖u i c a - v c a‖₊ : ℝ≥0∞) ^ 2 ∂μ)
      Filter.atTop (𝓝 0)) :
    ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧
      ∀ᵐ a ∂μ, ∀ c : ι, Filter.Tendsto (fun i : ℕ => u (ms i) c a) Filter.atTop (𝓝 (v c a)) := by
  classical
  haveI := Fintype.ofFinite ι
  have hsumTendsto : Filter.Tendsto
      (fun i : ℕ => ∑ c : ι, ∫⁻ a, (‖u i c a - v c a‖₊ : ℝ≥0∞) ^ 2 ∂μ)
      Filter.atTop (𝓝 0) := by
    have hfin := tendsto_finsetSum (Finset.univ : Finset ι) fun c _ => h c
    simpa using hfin
  obtain ⟨ms, hmsge, hmslt⟩ := LevyStochCalc.Brownian.Ito.exists_seq_lt_of_tendsto_zero hsumTendsto
  refine ⟨ms, hmsge, ?_⟩
  rw [MeasureTheory.ae_all_iff]
  intro c
  have hmeasi : ∀ i : ℕ, Measurable fun a : α => (‖u (ms i) c a - v c a‖₊ : ℝ≥0∞) ^ 2 :=
    fun i => ((((hu (ms i) c).sub (hv c)).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hsum : ∑' i : ℕ, ∫⁻ a, (‖u (ms i) c a - v c a‖₊ : ℝ≥0∞) ^ 2 ∂μ ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun i => ?_)
      (lt_top_iff_ne_top.mpr (LevyStochCalc.Brownian.Ito.tsum_geometric_inv_two_mul_ne_top (1 : ℝ≥0∞) (by simp))))
    rw [one_mul]
    refine le_trans ?_ (hmslt i).le
    exact Finset.single_le_sum
      (f := fun c' : ι => ∫⁻ a, (‖u (ms i) c' a - v c' a‖₊ : ℝ≥0∞) ^ 2 ∂μ)
      (fun _ _ => zero_le) (Finset.mem_univ c)
  filter_upwards [LevyStochCalc.Brownian.Ito.ae_tendsto_zero_of_lintegral_summable hmeasi hsum] with a ha
  exact LevyStochCalc.Brownian.Ito.tendsto_of_tendsto_sq_enorm_readable ha
