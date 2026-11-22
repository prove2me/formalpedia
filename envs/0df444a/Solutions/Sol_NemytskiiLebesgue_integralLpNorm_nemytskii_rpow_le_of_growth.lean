-- Prove2me | solution 1 for NemytskiiLebesgue.integralLpNorm_nemytskii_rpow_le_of_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:36:05.187273+00:00
-- url     : https://prove2.me/submissions/1c6f37e0-dd46-4076-9f78-ec1ad9c23bab

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Vitali
public import Theorems.Thm_NemytskiiLebesgue_integralLpNorm_eq_lintegral_rpow_enorm_toReal
public import Theorems.Thm_NemytskiiLebesgue_ne_zero_of_ge_one


set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal RealInnerProductSpace Topology
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F}
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q ≠ ⊤)
    {a : Ω → ℝ} (haq : AEMeasurable a μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    (u : Ω → D) :
    integralLpNorm (fun ω : Ω => f ω (u ω)) q μ ^ q.toReal ≤
      (2 : ℝ≥0∞) ^ (q.toReal - 1) * integralLpNorm a q μ ^ q.toReal +
      (2 : ℝ≥0∞) ^ (q.toReal - 1) * ↱C ^ q.toReal * integralLpNorm u p μ ^ p.toReal := by
  have integral_bound :
      ∫⁻ ω : Ω, (‖f ω (u ω)‖₊ : ℝ≥0∞) ^ q.toReal ∂μ ≤
      2 ^ (q.toReal - 1) * (∫⁻ ω : Ω, (‖a ω‖₊ : ℝ≥0∞) ^ q.toReal ∂μ) +
        2 ^ (q.toReal - 1) * ↱C ^ q.toReal * (∫⁻ ω : Ω, (‖u ω‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) := by
    have integral_bound :
      ∀ᵐ ω : Ω ∂μ,
        (‖f ω (u ω)‖₊ : ℝ≥0∞) ^ q.toReal ≤
        2 ^ (q.toReal - 1) * (‖a ω‖₊ : ℝ≥0∞) ^ q.toReal +
          2 ^ (q.toReal - 1) * ↱C ^ q.toReal * (‖u ω‖₊ : ℝ≥0∞) ^ p.toReal := by
      have integral_bound :
        ∀ᵐ ω : Ω ∂μ,
          (‖f ω (u ω)‖₊ : ℝ≥0∞) ^ q.toReal ≤
          (2 : ℝ≥0∞) ^ (q.toReal - 1) *
            ((‖a ω‖₊ : ℝ≥0∞) ^ q.toReal + ↱C ^ q.toReal * (‖u ω‖₊ : ℝ≥0∞) ^ p.toReal) := by
        have integral_bound :
          ∀ᵐ ω : Ω ∂μ,
            (‖f ω (u ω)‖₊ : ℝ≥0∞) ^ q.toReal ≤
            (2 : ℝ≥0∞) ^ (q.toReal - 1) *
              ((‖a ω‖₊ : ℝ≥0∞) ^ q.toReal +
                (↱C * (‖u ω‖₊ : ℝ≥0∞) ^ (p / q).toReal) ^ q.toReal) := by
          have integral_bound :
            ∀ᵐ ω : Ω ∂μ,
              (‖f ω (u ω)‖₊ : ℝ≥0∞) ≤
              (‖a ω‖₊ : ℝ≥0∞) + ↱C * (‖u ω‖₊ : ℝ≥0∞) ^ (p / q).toReal := by
            filter_upwards [hfaCpq] with ω hω
            convert ENNReal.ofReal_le_ofReal (hω (u ω)) using 1
            · norm_num [ENNReal.ofReal]
            · rw [ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _)
                _)), ENNReal.ofReal_mul hC]
              rw [←ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by positivity)]
              norm_num [←ENNReal.ofReal_coe_nnreal]
          filter_upwards [integral_bound] with ω hω
          apply le_trans (ENNReal.rpow_le_rpow hω ENNReal.toReal_nonneg)
          have h12 :=
            ENNReal.rpow_arith_mean_le_arith_mean_rpow { 0, 1 } ↓(1 / 2)
              (if · = 0 then (‖a ω‖₊ : ℝ≥0∞) else (↱C * ‖u ω‖₊ ^ (p / q).toReal))
          norm_num at h12
          convert! mul_le_mul_right (h12
            (by rw [ENNReal.mul_inv_cancel] <;> norm_num)
            (show 1 ≤ q.toReal by
              rw [←ENNReal.toReal_one]
              exact ENNReal.toReal_mono hq h1q
            )) (2 ^ q.toReal)
              using 1 <;> ring_nf
          · rw [←ENNReal.mul_rpow_of_nonneg] <;> norm_num
            ring_nf
            simp [mul_assoc, ENNReal.inv_mul_cancel]
          · rw [ENNReal.rpow_add] <;> norm_num
            rw [ENNReal.rpow_neg_one]
            ring_nf
        filter_upwards [integral_bound] with ω hω
        convert hω using 2
        rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg, ←ENNReal.rpow_mul]
        norm_num [hp, hq]
        rw [div_mul_cancel₀ _ (ne_of_gt (ENNReal.toReal_pos (ne_zero_of_ge_one h1q) hq))]
      simpa only [mul_add, mul_assoc] using integral_bound
    apply le_trans (lintegral_mono_ae integral_bound)
    rw [lintegral_add_left']
    · rw [lintegral_const_mul', lintegral_const_mul'] <;> norm_num
      have h1q : 1 ≤ q.toReal := ENNReal.toReal_mono hq h1q
      apply ENNReal.mul_ne_top <;> exact (ENNReal.rpow_ne_top_of_nonneg (by linarith [h1q]) (by
        simp))
    · apply AEMeasurable.const_mul (haq.nnnorm.coe_nnreal_ennreal.pow_const _)
  convert integral_bound using 1
  · rw [integralLpNorm_eq_lintegral_rpow_enorm_toReal]
    · rewrite [←ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt (ENNReal.toReal_pos
      (ne_zero_of_ge_one h1q) hq)), ENNReal.rpow_one]
      rfl
    · aesop
    · exact hq
  · rw [integralLpNorm_eq_lintegral_rpow_enorm_toReal (ne_zero_of_ge_one h1p) hp,
        integralLpNorm_eq_lintegral_rpow_enorm_toReal (ne_zero_of_ge_one h1q) hq]
    · rw [←ENNReal.rpow_mul, ←ENNReal.rpow_mul]
      norm_num [
        show q.toReal ≠ 0 from ne_of_gt (ENNReal.toReal_pos (ne_zero_of_ge_one h1q) hq),
        show p.toReal ≠ 0 from ne_of_gt (ENNReal.toReal_pos (ne_zero_of_ge_one h1p) hp)]
      rfl
end NemytskiiLebesgue
