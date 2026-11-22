-- Prove2me | solution 1 for NemytskiiLebesgue.ae_summable_norm_of_tsum_eLpNorm_ne_top_of_aestronglyMeas
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:35:00.547615+00:00
-- url     : https://prove2.me/submissions/5179c44b-83c1-430e-a69a-5877bebcdecd

module
public import Mathlib.MeasureTheory.Function.UnifTight
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Theorems.Thm_NemytskiiLebesgue_ne_zero_of_ge_one


set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal Topology
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {g : ℕ → Ω → D} (hg : ∀ n : ℕ, AEStronglyMeasurable (g n) μ) (hgp : ∑' n : ℕ, eLpNorm (g n) p μ
      ≠ ⊤) :
    ∀ᵐ ω : Ω ∂μ, Summable (‖g · ω‖) := by
  have minkowski : ∀ N : ℕ, eLpNorm (∑ n ∈ Finset.range N, ‖g n ·‖) p μ ≤ ∑ n ∈ Finset.range N,
    eLpNorm (g n) p μ := by
    have summ : ∀ N : ℕ, eLpNorm (∑ n ∈ Finset.range N, ‖g n ·‖) p μ ≤ ∑ n ∈ Finset.range N,
      eLpNorm (‖g n ·‖) p μ := by
      intro N
      simpa only [Finset.sum_apply, Finset.sum_fn] using
        (eLpNorm_sum_le (f := fun n ω => ‖g n ω‖) (μ := μ) (s := Finset.range N) (fun n _ => (hg n).norm) h1p)
    intro N
    simpa only [eLpNorm_norm _] using summ N
  have finite_integral : ∫⁻ ω : Ω, (∑' n : ℕ, ‖g n ω‖ₑ) ^ p.toReal ∂μ ≤ (∑' n : ℕ, eLpNorm (g n) p
    μ) ^ p.toReal := by
    have integral_le :
      ∀ N : ℕ,
        ∫⁻ ω : Ω, (∑ n ∈ Finset.range N, ‖g n ω‖ₑ) ^ p.toReal ∂μ ≤ (∑ n ∈ Finset.range N, eLpNorm
          (g n) p μ) ^ p.toReal := by
      intro N
      have integral_le_step : eLpNorm (∑ n ∈ Finset.range N, ‖g n ·‖) p μ ≤ ∑ n ∈ Finset.range N,
        eLpNorm (g n) p μ :=
        minkowski N
      have integral_le_step' :
          (∫⁻ ω : Ω, (∑ n ∈ Finset.range N, ‖g n ω‖ₑ) ^ p.toReal ∂μ) ^ (1 / p.toReal) ≤
          ∑ n ∈ Finset.range N, eLpNorm (g n) p μ := by
        convert integral_le_step using 1
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
        · simp [Real.enorm_eq_ofReal (Finset.sum_nonneg ↓↓(norm_nonneg _))]
          simp [ENNReal.ofReal_sum_of_nonneg ↓↓(norm_nonneg _)]
        · exact ne_of_gt (lt_of_lt_of_le zero_lt_one h1p)
        · exact hp
      have integral_le_step'' :
          ∫⁻ ω : Ω, (∑ n ∈ Finset.range N, ‖g n ω‖ₑ) ^ p.toReal ∂μ ≤
          (∑ n ∈ Finset.range N, eLpNorm (g n) p μ) ^ p.toReal := by
        convert ENNReal.rpow_le_rpow integral_le_step' _ using 1
        · rw [←ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt (ENNReal.toReal_pos
          (ne_zero_of_ge_one h1p) hp)), ENNReal.rpow_one]
        · positivity
      exact integral_le_step''
    have integral_le' : ∫⁻ ω : Ω, (∑' n : ℕ, ‖g n ω‖ₑ) ^ p.toReal ∂μ ≤ ∫⁻ ω : Ω, (⨆ N : ℕ, (∑ n ∈
      Finset.range N, ‖g n ω‖ₑ) ^ p.toReal) ∂μ := by
      refine lintegral_mono fun ω : Ω => ?_
      by_cases summmable : Summable (‖g · ω‖ₑ)
      · have integral_le : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, ‖g n ω‖ₑ) ^ p.toReal) atTop
          (𝓝 ((∑' n : ℕ, ‖g n ω‖ₑ) ^ p.toReal)) :=
          ENNReal.continuous_rpow_const.continuousAt.tendsto.comp summmable.hasSum.tendsto_sum_nat
        exact le_of_tendsto integral_le (eventually_atTop.← ⟨0, fun N : ℕ => ↓(le_iSup_of_le N
          le_rfl)⟩)
      · rw [tsum_eq_zero_of_not_summable summmable,
          ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos (ne_zero_of_ge_one h1p) hp)]
        exact zero_le
    nontriviality
    refine integral_le'.trans (le_of_tendsto_of_tendsto'
      (f := fun N => ∫⁻ ω, (∑ n ∈ Finset.range N, ‖g n ω‖ₑ) ^ p.toReal ∂μ)
      (g := fun N => (∑ n ∈ Finset.range N, eLpNorm (g n) p μ) ^ p.toReal)
      (lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_) ?_ integral_le)
    · fun_prop
    · exact Eventually.of_forall ↓(fun hle : · ≤ · =>
          ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (Finset.range_mono hle))
            ENNReal.toReal_nonneg)
    · exact Eventually.of_forall ↓(tendsto_atTop_iSup (fun hle : · ≤ · =>
          ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (Finset.range_mono hle))
            ENNReal.toReal_nonneg))
    · apply ENNReal.continuous_rpow_const.continuousAt.tendsto.comp
      exact ENNReal.summable.hasSum.tendsto_sum_nat
  have finite_ae : ∀ᵐ ω : Ω ∂μ, (∑' n : ℕ, ‖g n ω‖ₑ) ^ p.toReal < ⊤ :=
    have finite_integr : ∫⁻ ω : Ω, (∑' n : ℕ, ‖g n ω‖ₑ) ^ p.toReal ∂μ < ⊤ :=
      lt_of_le_of_lt finite_integral (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hgp)
    ae_lt_top' (by measurability) finite_integr.ne
  filter_upwards [finite_ae] with ω hω
  convert! ENNReal.tsum_coe_ne_top_iff_summable.→ (show (∑' n : ℕ, ‖g n ω‖ₑ) ≠ ⊤ from ?_) using 1
  · ext
    simp [←NNReal.summable_coe]
  · contrapose! hω
    rw [hω, ENNReal.top_rpow_of_pos (ENNReal.toReal_pos (ne_zero_of_ge_one h1p) hp)]
end NemytskiiLebesgue
