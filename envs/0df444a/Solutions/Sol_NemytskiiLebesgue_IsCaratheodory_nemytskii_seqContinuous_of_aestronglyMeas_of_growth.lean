-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.nemytskii_seqContinuous_of_aestronglyMeas_of_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:51.559293+00:00
-- url     : https://prove2.me/submissions/ee88258e-7bf6-4bba-bbd8-fe1aa6a13b37

module
public import Mathlib.MeasureTheory.Function.UnifTight
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Theorems.Thm_NemytskiiLebesgue_memLp_nemytskii_of_growth_of_aestronglyMeasurable
public import Theorems.Thm_NemytskiiLebesgue_convergesTo_of_tendsTo_of_growth_of_aestronglyMeas
public import Theorems.Thm_NemytskiiLebesgue_Filter_Tendsto_exists_fast_subseq
public import Theorems.Thm_NemytskiiLebesgue_ae_summable_norm_of_tsum_eLpNorm_ne_top_of_aestronglyMeas
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_aestronglyMeas_nemytskii_of_aestronglyMeas
public import Theorems.Thm_NemytskiiLebesgue_ne_zero_of_ge_one

section
public section
namespace NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal Topology
private lemma ae_norm_le_add_tsum_dist_of_ae_summable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {g : ℕ → Ω → D} {u : Ω → D}
    (hgu : ∀ᵐ ω : Ω ∂μ, Summable (‖g · ω - u ω‖))
    (n : ℕ) :
    ∀ᵐ ω : Ω ∂μ, ‖g n ω‖ ≤ ‖u ω‖ + ∑' k : ℕ, ‖g k ω - u ω‖ := by
  have ineq : ∀ᵐ ω : Ω ∂μ, ‖g n ω - u ω‖ ≤ ∑' k : ℕ, ‖g k ω - u ω‖ := by
    filter_upwards [hgu] with ω hω using Summable.le_tsum hω n ↓↓(norm_nonneg _)
  filter_upwards [ineq] with ω hω
  simpa using
    le_trans (norm_add_le (u ω) (g n ω - u ω)) <| by
      simpa only [add_le_add_iff_left] using hω
private lemma memLp_norm_add_tsum_dist_of_eastronglyMeas_of_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {g : ℕ → Ω → D} {u : Ω → D}
    (hg : ∀ n : ℕ, AEStronglyMeasurable (g n) μ)
    (hup : MemLp u p μ)
    (hgp : ∑' n : ℕ, eLpNorm (g n - u) p μ ≠ ⊤) :
    MemLp (fun ω : Ω => ‖u ω‖ + ∑' n : ℕ, ‖g n ω - u ω‖) p μ := by
  have summable : ∀ᵐ ω ∂μ, Summable (‖g · ω - u ω‖) :=
    ae_summable_norm_of_tsum_eLpNorm_ne_top_of_aestronglyMeas h1p hp
      (fun n => (hg n).sub hup.aestronglyMeasurable) hgp
  have sum_meas (N : ℕ) :
      AEStronglyMeasurable (fun ω => ∑ n ∈ Finset.range N, ‖g n ω - u ω‖) μ := by
    exact (Finset.range N).aestronglyMeasurable_fun_sum
      (fun n _ => ((hg n).sub hup.aestronglyMeasurable).norm)
  have tsum_meas : AEStronglyMeasurable (fun ω => ∑' n, ‖g n ω - u ω‖) μ :=
    aestronglyMeasurable_of_tendsto_ae _ sum_meas
      (summable.mono fun _ h => h.hasSum.tendsto_sum_nat)
  have eLpNorm_sum : eLpNorm (fun ω : Ω => ∑' n : ℕ, ‖g n ω - u ω‖) p μ ≤ ∑' n : ℕ, eLpNorm (fun ω
    : Ω => ‖g n ω - u ω‖) p μ := by
    have eLpNorm_summ :
      ∀ N : ℕ,
        eLpNorm (fun ω : Ω => ∑ n ∈ Finset.range N, ‖g n ω - u ω‖) p μ ≤
        ∑ n ∈ Finset.range N, eLpNorm (fun ω : Ω => ‖g n ω - u ω‖) p μ := by
      intro N
      have eLpNorm_summm :
        ∀ f : ℕ → Ω → ℝ, (∀ n : ℕ, AEStronglyMeasurable (f n) μ) →
          eLpNorm (fun ω : Ω => ∑ n ∈ Finset.range N, f n ω) p μ ≤
          ∑ n ∈ Finset.range N, eLpNorm (f n) p μ := by
        intro f hf
        simpa only [Finset.sum_apply, Finset.sum_fn] using
          (eLpNorm_sum_le (f := f) (μ := μ) (s := Finset.range N) (fun n _ => hf n) h1p)
      exact eLpNorm_summm _ (hg · |>.sub hup.aestronglyMeasurable |>.norm)
    have eLpNorm_suum : Tendsto (fun N : ℕ => eLpNorm (fun ω : Ω => ∑ n ∈ Finset.range N, ‖g n ω -
      u ω‖) p μ) atTop (𝓝 (eLpNorm (fun ω : Ω => ∑' n : ℕ, ‖g n ω - u ω‖) p μ)) := by
      have eLpNorm_suumm : ∀ᵐ ω : Ω ∂μ, Summable (‖g · ω - u ω‖) := by
        exact summable
      have eLpNorm_suummm : Tendsto (fun N : ℕ => ∫⁻ ω : Ω, ↱(‖∑ n ∈ Finset.range N, ‖g n ω - u ω‖‖
        ^ p.toReal) ∂μ) atTop (𝓝 (∫⁻ ω : Ω, ↱(‖∑' n : ℕ, ‖g n ω - u ω‖‖ ^ p.toReal) ∂μ)) := by
        refine lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
        · intro n
          have eLpNorm_sum : ∀ n : ℕ, AEMeasurable (fun ω : Ω => ‖g n ω - u ω‖) μ :=
            (hg · |>.sub hup.aestronglyMeasurable |>.norm.aemeasurable)
          apply ENNReal.continuous_ofReal.measurable.comp_aemeasurable
          measurability
        · filter_upwards [eLpNorm_suumm] with ω hω
          refine fun n : ℕ => fun m : ℕ => fun hnm : n ≤ m => ENNReal.ofReal_le_ofReal ?_;
          exact Real.rpow_le_rpow (norm_nonneg _) (by
              rw [Real.norm_of_nonneg (Finset.sum_nonneg ↓↓(norm_nonneg _)),
                  Real.norm_of_nonneg (Finset.sum_nonneg ↓↓(norm_nonneg _))]
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm) ↓↓↓(norm_nonneg
                _))
            ENNReal.toReal_nonneg
        · filter_upwards [eLpNorm_suumm] with ω hω
          refine ENNReal.tendsto_ofReal (hω.hasSum.tendsto_sum_nat.norm.rpow tendsto_const_nhds ?_)
          right
          exact (ENNReal.toReal_pos (ne_zero_of_ge_one h1p) hp)
      convert ENNReal.continuous_rpow_const.continuousAt.tendsto.comp eLpNorm_suummm using 2
      any_goals exact p.toReal⁻¹
      · norm_num [eLpNorm, sum_meas]
        split_ifs <;> simp_all [eLpNorm']
        simp [←ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) ENNReal.toReal_nonneg,
          Real.enorm_eq_ofReal_abs]
      · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
        · simp only [one_div, Real.norm_eq_abs, Real.enorm_eq_ofReal_abs,
            abs_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
          congr! 2
          ext ω
          rw [ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg ↓(norm_nonneg _)) ENNReal.toReal_nonneg]
        · exact ne_of_gt (lt_of_lt_of_le zero_lt_one h1p)
        · exact hp
    exact
      le_of_tendsto
        eLpNorm_suum
        (eventually_atTop.← ⟨0, ↓↓(le_trans (by solve_by_elim) (Summable.sum_le_tsum _ ↓↓(by
          positivity) ENNReal.summable))⟩)
  apply hup.norm.add
  refine ⟨tsum_meas, ?_⟩
  apply eLpNorm_sum.trans_lt
  have hnorm (n : ℕ) :
      eLpNorm (fun ω => ‖g n ω - u ω‖) p μ = eLpNorm (g n - u) p μ :=
    eLpNorm_norm (g n - u)
  simp_rw [hnorm]
  exact lt_top_iff_ne_top.mpr hgp
end NemytskiiLebesgue
end
end

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal Topology
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q ≠ ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {uₙ : ℕ → Ω → D} (huₙ : ∀ n : ℕ, AEStronglyMeasurable (uₙ n) μ)
    {u : Ω → D} (hup : MemLp u p μ)
    (huuₙ : uₙ.NemytskiiConvergesTo u p μ) :
    (fun n : ℕ => fun ω : Ω => f ω (uₙ n ω)).NemytskiiConvergesTo (fun ω : Ω => f ω (u ω)) q μ := by
  apply tendsto_of_subseq_tendsto
  intro s hs
  obtain ⟨s', _, hs'⟩ := Filter.Tendsto.exists_fast_subseq (huuₙ.comp hs)
  have tsum_ne_top : ∑' n : ℕ, eLpNorm (uₙ (s (s' n)) - u) p μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hs')
    rw [ENNReal.tsum_geometric]
    simp
  have ae_summable : ∀ᵐ ω : Ω ∂μ, Summable (fun n : ℕ => ‖uₙ (s (s' n)) ω - u ω‖) :=
    ae_summable_norm_of_tsum_eLpNorm_ne_top_of_aestronglyMeas h1p hp
      (fun n : ℕ => (huₙ (s (s' n))).sub hup.aestronglyMeasurable) tsum_ne_top
  have ae_conv_u : ∀ᵐ ω : Ω ∂μ, Tendsto (fun k : ℕ => uₙ (s (s' k)) ω) atTop (𝓝 (u ω)) := by
    filter_upwards [ae_summable] with ω hω using tendsto_iff_norm_sub_tendsto_zero.←
      hω.tendsto_atTop_zero
  have ae_conv_comp : ∀ᵐ ω : Ω ∂μ,
      Tendsto (fun k : ℕ => f ω ((uₙ (s (s' k))) ω)) atTop (𝓝 (f ω (u ω))) := by
    filter_upwards [hf.ae_continuous, ae_conv_u] with ω ω_cont ω_conv
    exact ω_cont.continuousAt.tendsto.comp ω_conv
  have huss' : MemLp (fun ω : Ω => ‖u ω‖ + ∑' n : ℕ, ‖uₙ (s (s' n)) ω - u ω‖) p μ :=
    memLp_norm_add_tsum_dist_of_eastronglyMeas_of_memLp h1p hp (fun n : ℕ => huₙ (s (s' n))) hup
      tsum_ne_top
  have ae_bound_u : ∀ k : ℕ, ∀ᵐ ω : Ω ∂μ,
      ‖uₙ (s (s' k)) ω‖ ≤ ‖u ω‖ + ∑' n : ℕ, ‖uₙ (s (s' n)) ω - u ω‖ :=
    ae_norm_le_add_tsum_dist_of_ae_summable ae_summable
  have ae_bound_comp : ∀ k : ℕ, ∀ᵐ ω : Ω ∂μ,
      ‖f ω (uₙ (s (s' k)) ω)‖ ≤ |a ω| + C * (‖u ω‖ + ∑' n : ℕ, ‖uₙ (s (s' n)) ω - u ω‖) ^ (p /
        q).toReal := by
    intro k
    filter_upwards [hfaCpq, ae_bound_u k] with ω ω_bound _
    calc ‖f ω ((uₙ (s (s' k))) ω)‖ = ‖f ω (uₙ (s (s' k)) ω)‖ := rfl
      _ ≤ |a ω| + C * ‖uₙ (s (s' k)) ω‖ ^ (p / q).toReal := ω_bound _
      _ ≤ |a ω| + C * (‖u ω‖ + ∑' n : ℕ, ‖uₙ (s (s' n)) ω - u ω‖) ^ (p / q).toReal := by gcongr
  have dom_memLp : MemLp (fun ω : Ω => |a ω| + C * (‖u ω‖ + ∑' n : ℕ, ‖uₙ (s (s' n)) ω - u ω‖) ^ (p
    / q).toReal) q μ :=
    have ae_memLp_comp : MemLp (fun ω : Ω => (‖u ω‖ + ∑' n : ℕ, ‖uₙ (s (s' n)) ω - u ω‖) ^ (p /
      q).toReal) q μ := by
      convert huss'.norm_rpow_div (p / q) using 1
      · ext x
        rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (tsum_nonneg ↓(norm_nonneg _)))]
      · rw [ENNReal.div_div_cancel] <;> aesop
    MemLp.add haq.abs (ae_memLp_comp.const_mul C)
  have hfuq : MemLp (fun ω : Ω => f ω (u ω)) q μ :=
    memLp_nemytskii_of_growth_of_aestronglyMeasurable (zero_lt_one.trans_le h1p) hp h1q hq haq hC
      hfaCpq hup
      (hf.aestronglyMeas_nemytskii_of_aestronglyMeas hup.aestronglyMeasurable)
  have comp_meas : ∀ k : ℕ, AEStronglyMeasurable (fun ω => f ω (uₙ (s (s' k)) ω)) μ :=
    fun k => hf.aestronglyMeas_nemytskii_of_aestronglyMeas (huₙ (s (s' k)))
  exact ⟨s', convergesTo_of_tendsTo_of_growth_of_aestronglyMeas h1q hq comp_meas hfuq dom_memLp
    ae_bound_comp ae_conv_comp⟩
end IsCaratheodory
end NemytskiiLebesgue
