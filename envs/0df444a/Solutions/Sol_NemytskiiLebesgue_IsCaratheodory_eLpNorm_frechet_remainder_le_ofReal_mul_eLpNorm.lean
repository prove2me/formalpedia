-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.eLpNorm_frechet_remainder_le_ofReal_mul_eLpNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:40:31.975752+00:00
-- url     : https://prove2.me/submissions/2fd56ac8-7ab9-4edf-bd7c-287af4bde4aa

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Theorems.Thm_NemytskiiLebesgue_eLpNorm_le_eLpNorm_mul_eLpNorm_of_aestronglyMeas
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_aestronglyMeas_frechet_remainder
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_tendsTo_eLpNorm_frechet_ratio_of_ae_tendsTo
public import Theorems.Thm_NemytskiiLebesgue_Filter_Tendsto_extract_fast_subseq_eLpNorm
public import Theorems.Thm_NemytskiiLebesgue_Nat_real_one_div_succ_pos
public import Theorems.Thm_NemytskiiLebesgue_memLp_iff_measurable_and_finite
public import Theorems.Thm_NemytskiiLebesgue_ne_zero_of_ge_one

section
public section
namespace NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology
private lemma ae_summable_rpow_of_tsum_lintegral_finite
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {l : ℕ → Ω → E} (hl : ∀ n : ℕ, AEStronglyMeasurable (l n) μ)
    {p : ℝ} (hlp : ∑' k : ℕ, ∫⁻ ω : Ω, ↱(‖l k ω‖ ^ p) ∂μ ≠ ⊤) :
    ∀ᵐ ω : Ω ∂μ, Summable (‖l · ω‖ ^ p) := by
  have fubini :
      ∫⁻ ω : Ω, ∑' k : ℕ, ↱(‖l k ω‖ ^ p) ∂μ =
      ∑' k : ℕ, ∫⁻ ω : Ω, ↱(‖l k ω‖ ^ p) ∂μ := by
    rw [lintegral_tsum]
    intro n
    exact ((hl n).norm.aemeasurable.pow_const p).ennreal_ofReal
  have fubin : ∀ᵐ ω : Ω ∂μ, ∑' k : ℕ, ↱(‖l k ω‖ ^ p) < ⊤ := by
    have fubi : ∫⁻ ω : Ω, ∑' k : ℕ, ↱(‖l k ω‖ ^ p) ∂μ < ⊤ :=
      fubini ▸ lt_top_iff_ne_top.← hlp
    refine ae_lt_top' ?_ fubi.ne
    apply AEMeasurable.tsum
    exact (ENNReal.continuous_ofReal.measurable.comp_aemeasurable <| hl · |>.norm
      |>.aemeasurable.pow_const p)
  filter_upwards [fubin] with ω hω
  convert ENNReal.summable_toReal _
  rotate_left
  · exact fun k : ℕ => ↱(‖l k ω‖ ^ p)
  · exact ne_of_lt hω
  · rw [ENNReal.toReal_ofReal (by positivity)]
private lemma ae_all_norm_le_tsum_norm_rpow_inv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {p : ℝ} (h1p : 1 ≤ p)
    {l : ℕ → Ω → E} (hlp : ∀ᵐ ω : Ω ∂μ, Summable (‖l · ω‖ ^ p)) :
    ∀ᵐ ω : Ω ∂μ, ∀ n : ℕ, ‖l n ω‖ ≤ (∑' k : ℕ, ‖l k ω‖ ^ p) ^ (1/p) := by
  filter_upwards [hlp] with ω hω
  intro n
  rw [one_div]
  refine le_trans ?_ (Real.rpow_le_rpow (by positivity) (hω.le_tsum n ↓↓(by positivity)) (by
    positivity))
  rw [←Real.rpow_mul (norm_nonneg (l n ω)), mul_inv_cancel₀ (ne_zero_of_ge_one h1p), Real.rpow_one]
private lemma ae_tendsto_zero_of_ae_summable_rpow
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {p : ℝ} (hp : 0 < p)
    {l : ℕ → Ω → E} (hlp : ∀ᵐ ω : Ω ∂μ, Summable (‖l · ω‖ ^ p)) :
    ∀ᵐ ω : Ω ∂μ, Tendsto (l · ω) atTop (𝓝 0) := by
  have norm_zero : ∀ᵐ ω : Ω ∂μ, Tendsto (‖l · ω‖) atTop (𝓝 0) := by
    filter_upwards [hlp] with ω hω
    convert hω.tendsto_atTop_zero.rpow_const _ using 1
    · ext
      rw [←Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ (ne_of_gt hp), Real.rpow_one]
    · simp [hp.ne']
    · right
      exact inv_nonneg.← hp.le
  filter_upwards [norm_zero] with ω hω using tendsto_zero_iff_norm_tendsto_zero.← hω
private lemma exists_exists_strictMono_and_memLp_and_ae_nonneg_and
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {p : ℝ} (hp : 1 ≤ p)
    {l : ℕ → Ω → E} (hl : ∀ n : ℕ, AEStronglyMeasurable (l n) μ)
    (hlp : Tendsto (fun n : ℕ => eLpNorm (l n) ↱p μ) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, ∃ g : Ω → ℝ,
      StrictMono s ∧
      MemLp g ↱p μ ∧
      (0 ≤ᵐ[μ] g) ∧
      (∀ᵐ ω : Ω ∂μ, ∀ n : ℕ, ‖l (s n) ω‖ ≤ g ω) ∧
      (∀ᵐ ω : Ω ∂μ, Tendsto (fun n : ℕ => l (s n) ω) atTop (𝓝 0)) := by
  obtain ⟨s, s_mono, s_eLpNorm⟩ : ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ k : ℕ, eLpNorm (l (s k)) ↱p μ ≤ ↱(1
    / 2 ^ k) :=
    Filter.Tendsto.extract_fast_subseq_eLpNorm hlp
  have hlp : ∑' k : ℕ, ∫⁻ ω, ↱(‖l (s k) ω‖ ^ p) ∂μ ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum
      (g := fun k : ℕ => ↱(1 / 2 ^ k) ^ p) fun k => ?_) ?_)
    · convert ENNReal.rpow_le_rpow (s_eLpNorm k) (by positivity) using 1
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
      · simp [ENNReal.toReal_ofReal (zero_le_one.trans hp), ←ENNReal.rpow_mul]
        simp [←ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by positivity), ne_of_gt
          (zero_lt_one.trans_le hp)]
      · positivity
      · exact ENNReal.ofReal_ne_top
    · have geo_series : ∑' k : ℕ, ↱(1 / 2 ^ k) ^ p = ∑' k : ℕ, ↱((1 / 2 ^ p) ^ k) := by
        refine tsum_congr ↓?_
        rw [ENNReal.ofReal_rpow_of_pos (by positivity)]
        ring_nf
        rw [←Real.rpow_natCast, ←Real.rpow_mul (by positivity), mul_comm, Real.rpow_mul (by
          positivity), Real.inv_rpow zero_le_two]
        norm_num
      rw [geo_series, ←ENNReal.ofReal_tsum_of_nonneg] <;> norm_num
      · intro
        positivity
      · apply inv_lt_one_of_one_lt₀
        rw [abs_of_nonneg (by positivity)]
        apply Real.one_lt_rpow one_lt_two
        positivity
  refine ⟨s, fun ω : Ω => (∑' k : ℕ, ‖l (s k) ω‖ ^ p) ^ (1 / p), s_mono, ?_, ?_, ?_, ?_⟩
  · have g_in_Lp : ∫⁻ ω, ↱((∑' k : ℕ, ‖l (s k) ω‖ ^ p) ^ (1 / p * p)) ∂μ < ⊤ := by
      have g_in_Lp : ∫⁻ ω, ↱(∑' k : ℕ, ‖l (s k) ω‖ ^ p) ∂μ ≤ ∑' k : ℕ, ∫⁻ ω, ↱(‖l (s k) ω‖ ^ p) ∂μ
        := by
        rw [←lintegral_tsum]
        · refine lintegral_mono fun ω : Ω => ?_
          by_cases summabl : Summable (fun k : ℕ => ‖l (s k) ω‖ ^ p)
          · rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
              summabl]
          · rw [tsum_eq_zero_of_not_summable summabl]
            simp
        · intro k
          apply ENNReal.continuous_ofReal.measurable.comp_aemeasurable
          exact (hl (s k)).norm.aemeasurable.pow_const p
      simpa [ne_zero_of_ge_one hp] using lt_of_le_of_lt g_in_Lp (lt_top_iff_ne_top.← hlp)
    have hmeas : AEStronglyMeasurable
        (fun ω => (∑' k : ℕ, ‖l (s k) ω‖ ^ p) ^ (1 / p)) μ := by
      have : ∀ k : ℕ, AEStronglyMeasurable (fun ω : Ω => ‖l (s k) ω‖ ^ p) μ :=
        fun k : ℕ => (hl (s k)).norm.aemeasurable.pow_const p |>.aestronglyMeasurable
      have g_in_Lp : AEStronglyMeasurable (fun ω : Ω => ∑' k : ℕ, ‖l (s k) ω‖ ^ p) μ :=
        have g_in_Lp₁ : ∀ᵐ ω : Ω ∂μ, Summable (fun k : ℕ => ‖l (s k) ω‖ ^ p) := by
          apply_rules [ae_summable_rpow_of_tsum_lintegral_finite]
          exact ↓(hl _)
        have g_in_Lp₂ :
          ∀ᵐ ω : Ω ∂μ,
            Tendsto
              (fun n : ℕ => ∑ k ∈ Finset.range n, ‖l (s k) ω‖ ^ p)
              atTop
              (𝓝 (∑' k : ℕ, ‖l (s k) ω‖ ^ p)) :=
          g_in_Lp₁.mono ↓(·.hasSum.tendsto_sum_nat)
        have g_in_Lp₃ : ∀ n : ℕ, AEStronglyMeasurable (fun ω : Ω => ∑ k ∈ Finset.range n, ‖l (s k)
          ω‖ ^ p) μ := by
          fun_prop
        aestronglyMeasurable_of_tendsto_ae _ g_in_Lp₃ g_in_Lp₂
      exact g_in_Lp.aemeasurable.pow_const (1/p) |>.aestronglyMeasurable
    apply memLp_iff_measurable_and_finite.mpr
    refine ⟨hmeas, ?_⟩
    · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal _ _]
      · apply ENNReal.rpow_lt_top_of_nonneg
        · positivity
        · convert g_in_Lp.ne using 1
          apply lintegral_congr
          intro
          rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (tsum_nonneg ↓(by positivity)) _),
              ENNReal.toReal_ofReal (by positivity),
              ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (tsum_nonneg ↓(by positivity)) _) (by
                positivity),
              ←Real.rpow_mul (tsum_nonneg ↓(by positivity))]
      · positivity
      · exact ENNReal.ofReal_ne_top
  · exact Eventually.of_forall ↓(Real.rpow_nonneg (tsum_nonneg ↓(Real.rpow_nonneg (norm_nonneg _)
    _)) _)
  · exact ae_all_norm_le_tsum_norm_rpow_inv hp (ae_summable_rpow_of_tsum_lintegral_finite (hl <| s
    ·) hlp)
  · apply_rules [ae_tendsto_zero_of_ae_summable_rpow]
    · positivity
    · apply_rules [ae_summable_rpow_of_tsum_lintegral_finite]
      exact ↓(hl _)
end NemytskiiLebesgue
end
end

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)} (hf' : IsCaratheodory f' μ)
    (hff' : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {p q r : ℝ} (h1p : 1 ≤ p) (h1r : 1 ≤ r) (hrpq : Real.HolderTriple r p q)
    {b : Ω → ℝ} (h0b : 0 ≤ᵐ[μ] b) (hbr : MemLp b ↱r μ)
    {C : ℝ} (hC : 0 < C)
    (hf'bCpr : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p / r))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ) :
    ∀ ε > 0, ∃ δ > 0, ∀ l : Ω → ℝ^m,
      MemLp l ↱p μ →
        eLpNorm l ↱p μ ≤ ↱δ →
          eLpNorm (fun ω : Ω => f ω (u ω + l ω) - f ω (u ω) - f' ω (u ω) (l ω)) ↱q μ ≤
          ↱ε * eLpNorm l ↱p μ := by
  intro ε hε
  by_contra! contra
  obtain ⟨l, l_mem, l_small, l_bad⟩ :
    ∃ l : ℕ → Ω → ℝ^m,
      (∀ n : ℕ, MemLp (l n) ↱p μ) ∧
      (∀ n : ℕ, eLpNorm (l n) ↱p μ ≤ ↱(1 / (n + 1))) ∧
      (∀ n : ℕ, ↱ε * eLpNorm (l n) ↱p μ < eLpNorm (fun ω : Ω => f ω (u ω + l n ω) - f ω (u ω) - (f'
        ω (u ω)) (l n ω)) ↱q μ) :=
    ⟨fun n : ℕ => Classical.choose      (contra (1 / (n + 1)) (Nat.real_one_div_succ_pos n)),
     fun n : ℕ => Classical.choose_spec (contra (1 / (n + 1)) (Nat.real_one_div_succ_pos n))
       |>.left,
     fun n : ℕ => Classical.choose_spec (contra (1 / (n + 1)) (Nat.real_one_div_succ_pos n))
       |>.right.left,
     fun n : ℕ => Classical.choose_spec (contra (1 / (n + 1)) (Nat.real_one_div_succ_pos n))
       |>.right.right⟩
  obtain ⟨s, g, s_mono, g_mem, h0g, g_dom, g_tendsto⟩ :
    ∃ s : ℕ → ℕ, ∃ g : Ω → ℝ,
      StrictMono s ∧
      MemLp g ↱p μ ∧
      0 ≤ᵐ[μ] g ∧
      (∀ᵐ ω : Ω ∂μ, ∀ n : ℕ, ‖l (s n) ω‖ ≤ g ω) ∧
      (∀ᵐ ω : Ω ∂μ, Tendsto (fun n : ℕ => l (s n) ω) atTop (𝓝 0)) := by
    apply exists_exists_strictMono_and_memLp_and_ae_nonneg_and
    · exact h1p
    · exact fun n : ℕ => (l_mem n).aestronglyMeasurable
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ ↓zero_le l_small
      simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have ratio_tendsto :
    Tendsto
      (fun n : ℕ => eLpNorm (fun ω : Ω => ‖f ω (u ω + l (s n) ω) - f ω (u ω) - (f' ω (u ω)) (l (s
        n) ω)‖ / ‖l (s n) ω‖) ↱r μ)
      atTop
      (𝓝 0) :=
    hf.tendsTo_eLpNorm_frechet_ratio_of_ae_tendsTo hf' hff' h1p h1r hC h0b hbr hf'bCpr hup
      (MemLp.aestronglyMeasurable <| l_mem <| s ·) h0g g_mem g_dom g_tendsto
  have remainder_tendsto :
    ∀ n : ℕ,
      eLpNorm (fun ω : Ω =>  f ω (u ω + l (s n) ω) - f ω (u ω) - (f' ω (u ω)) (l (s n) ω)) ↱q μ ≤
      eLpNorm (fun ω : Ω => ‖f ω (u ω + l (s n) ω) - f ω (u ω) - (f' ω (u ω)) (l (s n) ω)‖ / ‖l (s
        n) ω‖) ↱r μ *
        eLpNorm (l (s n)) ↱p μ := by
    intro n
    have hl := (l_mem (s n)).aestronglyMeasurable
    have hR := hf.aestronglyMeas_frechet_remainder hf' hup hl
    apply eLpNorm_le_eLpNorm_mul_eLpNorm_of_aestronglyMeas hrpq hl
      (hR.norm.mul hl.norm.aemeasurable.inv.aestronglyMeasurable) hR
    filter_upwards with ω
    by_cases h0 : l (s n) ω = 0 <;> simp [h0]
  have contradicti :
    ∀ᶠ n in atTop,
      eLpNorm (fun ω : Ω => f ω (u ω + l (s n) ω) - f ω (u ω) - (f' ω (u ω)) (l (s n) ω)) ↱q μ ≤
      ↱ε * eLpNorm (l (s n)) ↱p μ := by
    filter_upwards [ratio_tendsto.eventually (gt_mem_nhds <| show 0 < ↱ε from ENNReal.ofReal_pos.←
      hε)]
      with n hn
      using le_trans (remainder_tendsto n) (mul_le_mul_left hn.le _)
  exact (fun ⟨n, hn⟩ => not_le_of_gt (l_bad (s n)) hn) contradicti.exists
end IsCaratheodory
end NemytskiiLebesgue
