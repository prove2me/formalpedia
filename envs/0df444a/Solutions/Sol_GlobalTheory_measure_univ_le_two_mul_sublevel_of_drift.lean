-- Prove2me | solution 1 for GlobalTheory.measure_univ_le_two_mul_sublevel_of_drift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:19:57.426651+00:00
-- url     : https://prove2.me/submissions/a6717dff-074c-42bc-b3f2-56f94d21b5cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasureUnivLeTwoMulSublevelOfDrift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (Y σ : Type) [MeasurableSpace Y] [Fintype σ] [Nonempty σ] (μ : Measure Y)
      (R : Y → Y → Prop) (t : σ → Y → Y) (f : Y → ℝ) (c b : ℝ), (∀ s, Measurable (t s)) →
      (∀ s y y', R y y' → R (t s y) (t s y')) →
      (∀ φ : Y → ℝ≥0∞, Measurable φ → (∀ y y', R y y' → φ y = φ y') →
        ∀ s, ∫⁻ y, φ (t s y) ∂μ = ∫⁻ y, φ y ∂μ) →
      Measurable f → (∀ y, 0 ≤ f y) → (∀ y y', R y y' → f y = f y') → 0 ≤ c → c < 1 → 0 ≤ b →
      (∀ y, ∑ s, f (t s y) ≤ Fintype.card σ * (c * f y + b)) →
      ∃ M : ℝ, μ Set.univ ≤ 2 * μ {y | f y ≤ M}) := by
  intro Y σ _ _ _ μ R t f c b ht hR hinv hf hf0 hfR hc0 hc1 hb hdrift
  classical
  have h1c : 0 < 1 - c := by linarith
  obtain ⟨K, hK, hK0⟩ : ∃ K : ℝ, b = K * (1 - c) ∧ 0 ≤ K :=
    ⟨b / (1 - c), by field_simp, div_nonneg hb h1c.le⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * K + 1 := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; linarith
  refine ⟨M, ?_⟩
  have hN : (0 : ℝ) < Fintype.card σ := by exact_mod_cast Fintype.card_pos
  have hA : MeasurableSet {y | f y ≤ M} := measurableSet_le hf measurable_const
  let g : ℕ → Y → ℝ := fun n =>
    Nat.rec (fun y => if f y ≤ M then 1 else 0)
      (fun _ h y => (Fintype.card σ : ℝ)⁻¹ * ∑ s, h (t s y)) n
  have g0 : ∀ y, g 0 y = if f y ≤ M then 1 else 0 := fun y => rfl
  have gs : ∀ n y, g (n + 1) y = (Fintype.card σ : ℝ)⁻¹ * ∑ s, g n (t s y) := fun n y => rfl
  clear_value g
  have gmeas : ∀ n, Measurable (g n) := by
    intro n
    induction n with
    | zero =>
      rw [show g 0 = _ from funext g0]
      exact Measurable.ite hA measurable_const measurable_const
    | succ n ih =>
      rw [show g (n + 1) = _ from funext (gs n)]
      exact measurable_const.mul (Finset.measurable_sum _ fun s _ => ih.comp (ht s))
  have gnn : ∀ n y, 0 ≤ g n y := by
    intro n
    induction n with
    | zero => intro y; rw [g0]; split_ifs <;> norm_num
    | succ n ih =>
      intro y; rw [gs]
      exact mul_nonneg (inv_nonneg.2 hN.le) (Finset.sum_nonneg fun s _ => ih _)
  have gR : ∀ n y y', R y y' → g n y = g n y' := by
    intro n
    induction n with
    | zero => intro y y' h; rw [g0, g0, hfR y y' h]
    | succ n ih =>
      intro y y' h; rw [gs, gs]
      congr 1
      exact Finset.sum_congr rfl fun s _ => ih _ _ (hR s _ _ h)
  have gint : ∀ n, ∫⁻ y, ENNReal.ofReal (g n y) ∂μ = μ {y | f y ≤ M} := by
    intro n
    induction n with
    | zero =>
      rw [← lintegral_indicator_one hA]
      refine lintegral_congr fun y => ?_
      rw [g0]
      by_cases h : f y ≤ M <;> simp [h, Set.indicator]
    | succ n ih =>
      have hm : Measurable fun y => ENNReal.ofReal (g n y) := (gmeas n).ennreal_ofReal
      have e : ∀ y, ENNReal.ofReal (g (n + 1) y) =
          (Fintype.card σ : ℝ≥0∞)⁻¹ * ∑ s, ENNReal.ofReal (g n (t s y)) := by
        intro y
        rw [gs, ENNReal.ofReal_mul (inv_nonneg.2 hN.le), ENNReal.ofReal_inv_of_pos hN,
          ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg fun s _ => gnn n _]
      simp_rw [e]
      have hN0 : (Fintype.card σ : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
      have hms : ∀ s, Measurable fun y => ENNReal.ofReal (g n (t s y)) :=
        fun s => hm.comp (ht s)
      rw [lintegral_const_mul _ (Finset.measurable_sum _ fun s _ => hms s),
        lintegral_finset_sum _ fun s _ => hms s]
      have : ∀ s, ∫⁻ y, ENNReal.ofReal (g n (t s y)) ∂μ = μ {y | f y ≤ M} := fun s => by
        rw [← ih]
        exact hinv (fun y => ENNReal.ofReal (g n y)) hm
          (fun y y' h => by simp only [gR n y y' h]) s
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, ENNReal.inv_mul_cancel hN0 (ENNReal.natCast_ne_top _), one_mul]
  have glow : ∀ n y, M - (c ^ n * f y + K * (1 - c ^ n)) ≤ M * g n y := by
    intro n
    induction n with
    | zero =>
      intro y; rw [g0]
      have := hf0 y
      split_ifs with h
      · simp [this]
      · simp only [pow_zero, one_mul, sub_self, mul_zero, add_zero]
        linarith [not_le.1 h]
    | succ n ih =>
      intro y
      have hcn : 0 ≤ c ^ n := pow_nonneg hc0 n
      have h1 : ∑ s, (M - (c ^ n * f (t s y) + K * (1 - c ^ n))) ≤ ∑ s, M * g n (t s y) :=
        Finset.sum_le_sum fun s _ => ih _
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        at h1
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
      have h2 := mul_le_mul_of_nonneg_left (hdrift y) hcn
      rw [gs, mul_left_comm, le_inv_mul_iff₀ hN, pow_succ]
      rw [hK] at h2
      rw [← Finset.mul_sum] at h1
      nlinarith
  have hlim : ∀ y, (2⁻¹ : ℝ≥0∞) ≤
      Filter.liminf (fun n => ENNReal.ofReal (g n y)) Filter.atTop := by
    intro y
    refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
    have h0 : Filter.Tendsto (fun n : ℕ => c ^ n * f y) Filter.atTop (𝓝 (0 * f y)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const _
    rw [zero_mul] at h0
    filter_upwards [h0.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with n hn
    have h1 := glow n y
    have h2 : 0 ≤ K * c ^ n := mul_nonneg hK0 (pow_nonneg hc0 n)
    have h3 : M * 2⁻¹ ≤ M * g n y := by nlinarith
    have h4 : (2⁻¹ : ℝ) ≤ g n y := le_of_mul_le_mul_left h3 hM0
    have := ENNReal.ofReal_le_ofReal h4
    rwa [ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat] at this
  have hF : 2⁻¹ * μ Set.univ ≤ μ {y | f y ≤ M} := by
    rw [← lintegral_const]
    refine (lintegral_mono hlim).trans ?_
    refine (lintegral_liminf_le fun n => (gmeas n).ennreal_ofReal).trans ?_
    simp only [gint, Filter.liminf_const, le_refl]
  calc μ Set.univ = 2 * (2⁻¹ * μ Set.univ) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ _ := by gcongr
end GlobalTheory
