-- Prove2me | solution 1 for Newton.inner_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:33:51.275162+00:00
-- url     : https://prove2.me/submissions/d3d43a52-5366-47fa-99a2-42e3bd5480c7

import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
import Definitions.Def_Newton_Analysis_Convolution_InnerBound
import Theorems.Thm_Newton_convolution_integrand_decomposition
import Theorems.Thm_Newton_decomposition_exponents_pos
import Theorems.Thm_Newton_lintegral_mul_mul_le_three_holder
import Theorems.Thm_Newton_young_exponent_p_le_r
import Theorems.Thm_Newton_young_exponent_q_le_r
import Theorems.Thm_Newton_young_exponent_to_three_holder


set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f g : (Fin n → ℝ) → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hp_ne_top : p ≠ ⊤) (hq_ne_top : q ≠ ⊤) (hr_ne_top : r ≠ ⊤)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hf : MemLp f p volume) (hg : MemLp g q volume)
    (x : Fin n → ℝ) :
    ∫⁻ y, ‖f y‖₊ * ‖g (x - y)‖₊ ∂volume ≤
      (∫⁻ y, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume)^(1/r.toReal) *
      (eLpNorm f p volume)^(1 - p/r).toReal *
      (eLpNorm g q volume)^(1 - q/r).toReal := by
  -- Essential three-function Hölder part begins here
  have hpos := decomposition_exponents_pos hp hq hr_ne_top
  rcases hpos with ⟨hp_div_pos, hq_div_pos, h1m_le, h1m_le'⟩
  -- Derive three-function Hölder exponent condition from Young's exponent condition
  have h3 := young_exponent_to_three_holder hp hq hr hp_ne_top hq_ne_top hr_ne_top hpqr
  have h_holder :
      ∫⁻ y, ‖f y‖₊ * ‖g (x - y)‖₊ ∂volume ≤
        (∫⁻ y, (‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal) ∂volume)^(1/r.toReal) *
        (∫⁻ y, ‖f y‖₊^p.toReal ∂volume)^((r - p) / (p * r)).toReal *
        (∫⁻ y, ‖g (x - y)‖₊^q.toReal ∂volume)^((r - q) / (q * r)).toReal := by
    -- Prepare three-function Hölder exponent condition from Young's exponent condition
    have h_three_exp :
        1 / r + (r - p) / (p * r) + (r - q) / (q * r) = (1 : ℝ≥0∞) :=
      young_exponent_to_three_holder hp hq hr hp_ne_top hq_ne_top hr_ne_top hpqr
    let F : (Fin n → ℝ) → ℝ≥0∞ :=
      fun y => ‖f y‖₊ ^ (p / r).toReal * ‖g (x - y)‖₊ ^ (q / r).toReal
    let G : (Fin n → ℝ) → ℝ≥0∞ :=
      fun y => ‖f y‖₊ ^ (1 - p / r).toReal
    let H : (Fin n → ℝ) → ℝ≥0∞ :=
      fun y => ‖g (x - y)‖₊ ^ (1 - q / r).toReal
    -- measurability: extract AEMeasurable from MemLp, then closed under nnnorm and rpow
    have hF_ae : AEMeasurable F volume := by
      -- a.e. strong measurability of f and g
      have hf_aesm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
      have hg_aesm : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
      -- a.e. measurability of the ℝ≥0∞-valued norms
      have hf_nnnorm :
          AEMeasurable (fun y : Fin n → ℝ => (‖f y‖₊ : ℝ≥0∞)) volume := by
        simpa [enorm_eq_nnnorm] using hf_aesm.enorm
      have h_sub_meas :
          Measurable fun y : Fin n → ℝ => x - y :=
        measurable_const.sub measurable_id
      have hg_comp_aesm :
          AEStronglyMeasurable (fun y : Fin n → ℝ => g (x - y)) volume := by
        have h_pres : MeasurePreserving (fun y : Fin n → ℝ => x - y) volume volume := by
          have : MeasurePreserving (fun y : Fin n → ℝ => -y) volume volume :=
            Measure.measurePreserving_neg volume
          simpa [Function.comp_def, sub_eq_add_neg] using measurePreserving_add_left volume x |>.comp this
        exact hg_aesm.comp_measurePreserving h_pres
      have hg_nnnorm :
          AEMeasurable (fun y : Fin n → ℝ => (‖g (x - y)‖₊ : ℝ≥0∞)) volume := by
        simpa [enorm_eq_nnnorm] using hg_comp_aesm.enorm
      -- close under rpow and multiplication
      have hF₁ :
          AEMeasurable
            (fun y : Fin n → ℝ =>
              (‖f y‖₊ : ℝ≥0∞) ^ (p / r).toReal) volume :=
        hf_nnnorm.pow_const _
      have hF₂ :
          AEMeasurable
            (fun y : Fin n → ℝ =>
              (‖g (x - y)‖₊ : ℝ≥0∞) ^ (q / r).toReal) volume :=
        hg_nnnorm.pow_const _
      exact hF₁.mul hF₂
    have hG_ae : AEMeasurable G volume := by
      have hf_aesm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
      have hf_nnnorm :
          AEMeasurable (fun y : Fin n → ℝ => (‖f y‖₊ : ℝ≥0∞)) volume := by
        simpa [enorm_eq_nnnorm] using hf_aesm.enorm
      have hG :
          AEMeasurable
            (fun y : Fin n → ℝ =>
              (‖f y‖₊ : ℝ≥0∞) ^ (1 - p / r).toReal) volume :=
        hf_nnnorm.pow_const _
      simpa [G] using hG
    have hH_ae : AEMeasurable H volume := by
      have hg_aesm : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
      have hg_comp_aesm :
          AEStronglyMeasurable (fun y : Fin n → ℝ => g (x - y)) volume := by
        -- x - y = -(y + (-x)) = -(y - x)
        have h_sub : MeasurePreserving (fun y : Fin n → ℝ => y - x) volume volume :=
          measurePreserving_sub_right volume x
        have h_neg : MeasurePreserving (fun y : Fin n → ℝ => -y) volume volume :=
          Measure.measurePreserving_neg volume
        have h_comp : MeasurePreserving (fun y : Fin n → ℝ => x - y) volume volume := by
          have : (fun y : Fin n → ℝ => x - y) = (fun y => -y) ∘ (fun y => y - x) := by
            ext y; simp [neg_sub]
          rw [this]
          exact h_neg.comp h_sub
        exact hg_aesm.comp_measurePreserving h_comp
      have hg_nnnorm :
          AEMeasurable (fun y : Fin n → ℝ => (‖g (x - y)‖₊ : ℝ≥0∞)) volume := by
        simpa [enorm_eq_nnnorm] using hg_comp_aesm.enorm
      have hH :
          AEMeasurable
            (fun y : Fin n → ℝ =>
              (‖g (x - y)‖₊ : ℝ≥0∞) ^ (1 - q / r).toReal) volume :=
        hg_nnnorm.pow_const _
      simpa [H] using hH
    -- Three-factor decomposition of integrand:
    -- ‖f y‖ * ‖g (x - y)‖ = F(y) * G(y) * H(y) (converted from real-valued lemma)
    have h_pointwise :
        ∀ y, ‖f y‖₊ * ‖g (x - y)‖₊ =
          F y * G y * H y := by
      intro y
      -- Get decomposition from real norm version `convolution_integrand_decomposition`,
      -- lift to ℝ≥0∞ using `coe_nnnorm` and `toReal_coe_nnnorm'`
      have h_real :=
        convolution_integrand_decomposition f g p q r hp hq
          hp_ne_top hq_ne_top hr_ne_top hpqr x y
      -- Apply `ENNReal.ofReal` to both sides of `h_real` and rewrite norms to `‖·‖₊`
      have h_real' := congrArg ENNReal.ofReal h_real
      have hf_nonneg : 0 ≤ ‖f y‖ := norm_nonneg _
      have hg_nonneg : 0 ≤ ‖g (x - y)‖ := norm_nonneg _
      -- Auxiliary equations to map each rpow to ENNReal.rpow
      have h_rpow_f_main :
          ENNReal.ofReal (‖f y‖ ^ (p / r).toReal) =
            ENNReal.ofReal ‖f y‖ ^ (p / r).toReal :=
        (ENNReal.ofReal_rpow_of_nonneg hf_nonneg
          (ENNReal.toReal_nonneg (a := p / r))).symm
      have h_rpow_g_main :
          ENNReal.ofReal (‖g (x - y)‖ ^ (q / r).toReal) =
            ENNReal.ofReal ‖g (x - y)‖ ^ (q / r).toReal :=
        (ENNReal.ofReal_rpow_of_nonneg hg_nonneg
          (ENNReal.toReal_nonneg (a := q / r))).symm
      have h_rpow_f_tail :
          ENNReal.ofReal (‖f y‖ ^ (1 - p / r).toReal) =
            ENNReal.ofReal ‖f y‖ ^ (1 - p / r).toReal :=
        (ENNReal.ofReal_rpow_of_nonneg hf_nonneg
          (ENNReal.toReal_nonneg (a := 1 - p / r))).symm
      have h_rpow_g_tail :
          ENNReal.ofReal (‖g (x - y)‖ ^ (1 - q / r).toReal) =
            ENNReal.ofReal ‖g (x - y)‖ ^ (1 - q / r).toReal :=
        (ENNReal.ofReal_rpow_of_nonneg hg_nonneg
          (ENNReal.toReal_nonneg (a := 1 - q / r))).symm
      simp only [F, G, H]
      -- Use the fact that sum of exponents equals 1
      have hr_pos : r ≠ 0 := ne_of_gt (one_pos.trans_le hr)
      have hp_exp : (p / r).toReal + (1 - p / r).toReal = 1 := by
        have h_p_le_r : p ≤ r := young_exponent_p_le_r hq hpqr
        have h_le : p / r ≤ 1 := by
          rw [ENNReal.div_le_iff hr_pos hr_ne_top]
          simp only [one_mul]
          exact h_p_le_r
        have h_ne_top : p / r ≠ ⊤ := ENNReal.div_ne_top hp_ne_top hr_pos
        have h_sub_ne_top : 1 - p / r ≠ ⊤ := by
          exact ne_of_lt (lt_of_le_of_lt tsub_le_self (by simp))
        rw [← ENNReal.toReal_add h_ne_top h_sub_ne_top]
        simp [add_tsub_cancel_of_le h_le]
      have hq_exp : (q / r).toReal + (1 - q / r).toReal = 1 := by
        have h_q_le_r : q ≤ r := young_exponent_q_le_r hp hpqr
        have h_le : q / r ≤ 1 := by
          rw [ENNReal.div_le_iff hr_pos hr_ne_top]
          simp only [one_mul]
          exact h_q_le_r
        have h_ne_top : q / r ≠ ⊤ := ENNReal.div_ne_top hq_ne_top hr_pos
        have h_sub_ne_top : 1 - q / r ≠ ⊤ := by
          exact ne_of_lt (lt_of_le_of_lt tsub_le_self (by simp))
        rw [← ENNReal.toReal_add h_ne_top h_sub_ne_top]
        simp [add_tsub_cancel_of_le h_le]
      -- Simplify using additivity of rpow
      calc (‖f y‖₊ : ℝ≥0∞) * ‖g (x - y)‖₊
          = ‖f y‖₊ ^ (1 : ℝ) * ‖g (x - y)‖₊ ^ (1 : ℝ) := by simp
        _ = ‖f y‖₊ ^ ((p / r).toReal + (1 - p / r).toReal) *
            ‖g (x - y)‖₊ ^ ((q / r).toReal + (1 - q / r).toReal) := by
              rw [hp_exp, hq_exp]
        _ = (‖f y‖₊ ^ (p / r).toReal * ‖f y‖₊ ^ (1 - p / r).toReal) *
            (‖g (x - y)‖₊ ^ (q / r).toReal * ‖g (x - y)‖₊ ^ (1 - q / r).toReal) := by
              rw [ENNReal.rpow_add_of_nonneg _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
                  ENNReal.rpow_add_of_nonneg _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
        _ = ‖f y‖₊ ^ (p / r).toReal * ‖g (x - y)‖₊ ^ (q / r).toReal *
            ‖f y‖₊ ^ (1 - p / r).toReal * ‖g (x - y)‖₊ ^ (1 - q / r).toReal := by
              ring
    -- Apply three-function Hölder inequality to F, G, H here.
    -- Under Young's exponent condition, handle endpoint cases (p = r or q = r) and
    -- strictly interior case (p < r and q < r) separately.
    by_cases hp_eq_r : p = r
    · -- Endpoint case 1: p = r (then q = 1 from Young's condition)
      -- When p = r, we have p/r = 1 so 1 - p/r = 0
      -- Also from Young's condition 1/p + 1/q = 1 + 1/r and p = r, we get 1/q = 1, i.e., q = 1
      have hq_eq_one : q = 1 := by
        have h : 1/p + 1/q = 1 + 1/r := hpqr
        rw [hp_eq_r] at h
        -- h : 1/r + 1/q = 1 + 1/r
        -- Therefore 1/q = 1
        have hr_pos : r ≠ 0 := ne_of_gt (one_pos.trans_le hr)
        have h_inv_r_ne_top : 1/r ≠ ⊤ := ENNReal.div_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤) hr_pos
        have h_add_cancel : 1/r + 1/q = 1/r + 1 := by
          calc 1/r + 1/q = 1 + 1/r := h
            _ = 1/r + 1 := add_comm 1 (1/r)
        -- ENNReal.add_right_inj : a ≠ ⊤ → (a + b = a + c ↔ b = c)
        have h_one_div_q : 1/q = 1 := (ENNReal.add_right_inj h_inv_r_ne_top).mp h_add_cancel
        -- Derive q = 1 from 1/q = 1
        simp only [one_div] at h_one_div_q
        exact ENNReal.inv_eq_one.mp h_one_div_q
      -- Since p/r = 1, we have 1 - p/r = 0
      have hp_div_r_eq_one : p / r = 1 := by
        rw [hp_eq_r]
        exact ENNReal.div_self (ne_of_gt (one_pos.trans_le hr)) hr_ne_top
      have h_one_sub_p_div_r : 1 - p / r = 0 := by simp [hp_div_r_eq_one]
      -- Calculate 1 - q/r when q = 1 and q ≤ r
      have hq_div_r : q / r = 1 / r := by simp [hq_eq_one]
      have h_one_sub_q_div_r : 1 - q / r = 1 - 1 / r := by simp [hq_div_r]
      -- G y = ‖f y‖₊^0 = 1
      have hG_eq_one : ∀ y, G y = 1 := by
        intro y
        simp only [G, h_one_sub_p_div_r, ENNReal.toReal_zero, ENNReal.rpow_zero]
      -- F y = ‖f y‖₊^1 * ‖g (x - y)‖₊^(1/r).toReal = ‖f y‖₊ * ‖g (x - y)‖₊^(1/r).toReal
      have hF_simp : ∀ y, F y = ‖f y‖₊ * ‖g (x - y)‖₊ ^ (1 / r).toReal := by
        intro y
        simp only [F, hp_div_r_eq_one, hq_eq_one, ENNReal.toReal_one, ENNReal.rpow_one,
                   one_div]
      have h_integrand_eq : ∀ y, F y * G y * H y = (‖f y‖₊ : ℝ≥0∞) * ‖g (x - y)‖₊ := by
        intro y
        rw [hG_eq_one y, mul_one]
        simp only [F, H, hp_div_r_eq_one, ENNReal.toReal_one, ENNReal.rpow_one, hq_eq_one]
        -- F y * H y = ‖f y‖₊ * ‖g (x-y)‖₊^(1/r) * ‖g (x-y)‖₊^(1-1/r)
        have hr_pos : r ≠ 0 := ne_of_gt (one_pos.trans_le hr)
        have h1r_add : (1 / r).toReal + (1 - 1 / r).toReal = 1 := by
          have h_le : 1 / r ≤ 1 := by
            rw [ENNReal.div_le_iff hr_pos hr_ne_top]
            simp only [one_mul]
            exact hr
          have h_ne_top : 1 / r ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top hr_pos
          have h_sub_ne_top : 1 - 1 / r ≠ ⊤ := ne_of_lt (lt_of_le_of_lt tsub_le_self (by simp))
          simp only [one_div] at h_ne_top h_sub_ne_top h_le ⊢
          rw [← ENNReal.toReal_add h_ne_top h_sub_ne_top]
          rw [add_tsub_cancel_of_le h_le]
          simp
        calc ‖f y‖₊ * (‖g (x - y)‖₊ : ℝ≥0∞) ^ (1 / r).toReal *
               ‖g (x - y)‖₊ ^ (1 - 1 / r).toReal
            = ‖f y‖₊ * (‖g (x - y)‖₊ ^ (1 / r).toReal * ‖g (x - y)‖₊ ^ (1 - 1 / r).toReal) := by
              ring
          _ = ‖f y‖₊ * ‖g (x - y)‖₊ ^ ((1 / r).toReal + (1 - 1 / r).toReal) := by
              rw [← ENNReal.rpow_add_of_nonneg _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
          _ = ‖f y‖₊ * ‖g (x - y)‖₊ ^ (1 : ℝ) := by rw [h1r_add]
          _ = ‖f y‖₊ * ‖g (x - y)‖₊ := by simp
      have h_exp_zero : ((r - p) / (p * r)).toReal = 0 := by
        rw [hp_eq_r, tsub_self, ENNReal.zero_div, ENNReal.toReal_zero]
      -- Similarly, the exponent of eLpNorm becomes 0
      have h_eLpNorm_exp_zero : (1 - p / r).toReal = 0 := by
        simp only [h_one_sub_p_div_r, ENNReal.toReal_zero]
      -- Simplify the second factor of h_holder to 1
      have h_second_factor_eq_one :
          (∫⁻ y, ‖f y‖₊ ^ p.toReal ∂volume) ^ ((r - p) / (p * r)).toReal = 1 := by
        rw [h_exp_zero, ENNReal.rpow_zero]
      -- Correspondence for hf_pow: (∫⁻ ...)^{(r-p)/(pr)} = eLpNorm^{1-p/r}
      -- When p = r, both sides equal 1
      have h_eLpNorm_factor_eq_one : (eLpNorm f p volume) ^ (1 - p / r).toReal = 1 := by
        rw [h_eLpNorm_exp_zero, ENNReal.rpow_zero]
      -- For p = r case, prove the inequality directly
      -- First prepare a lemma to convert the RHS of h_holder goal to eLpNorm form
      have h_translate : ∫⁻ y, ‖g (x - y)‖₊ ^ q.toReal ∂volume =
          ∫⁻ z, ‖g z‖₊ ^ q.toReal ∂volume :=
        lintegral_sub_left_eq_self (fun z => ‖g z‖₊ ^ q.toReal) x
      have hq_pos : 0 < q.toReal := ENNReal.toReal_pos (ne_of_gt (one_pos.trans_le hq)) hq_ne_top
      have hr_pos : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt (one_pos.trans_le hr)) hr_ne_top
      have hq_le_r : q ≤ r := young_exponent_q_le_r hp hpqr
      have h_exp_eq' : ((r - q) / (q * r)).toReal = (1 - q / r).toReal / q.toReal := by
        rw [ENNReal.toReal_div, ENNReal.toReal_mul]
        rw [ENNReal.toReal_sub_of_le hq_le_r hr_ne_top]
        have h_le : q / r ≤ 1 := by
          rw [ENNReal.div_le_iff (ne_of_gt (one_pos.trans_le hr)) hr_ne_top, one_mul]
          exact hq_le_r
        rw [ENNReal.toReal_sub_of_le h_le (by simp : (1 : ℝ≥0∞) ≠ ⊤)]
        rw [ENNReal.toReal_div, ENNReal.toReal_one]
        have h_qr_ne : q.toReal * r.toReal ≠ 0 := mul_ne_zero (ne_of_gt hq_pos) (ne_of_gt hr_pos)
        field_simp [h_qr_ne, ne_of_gt hq_pos, ne_of_gt hr_pos]
      have h_eLpNorm_eq : eLpNorm g q volume =
          (∫⁻ z, ‖g z‖₊ ^ q.toReal ∂volume) ^ (1 / q.toReal) := by
        unfold eLpNorm eLpNorm'
        have hq_ne_zero : q ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hq)
        simp only [hq_ne_top, hq_ne_zero, ite_false, enorm_eq_nnnorm]
      -- Transform RHS: RHS of h_holder = RHS in eLpNorm form
      have h_rhs_eq : (∫⁻ y, ‖f y‖₊ ^ p.toReal * ‖g (x - y)‖₊ ^ q.toReal) ^ (1 / r.toReal) *
            (∫⁻ y, ‖f y‖₊ ^ p.toReal) ^ ((r - p) / (p * r)).toReal *
          (∫⁻ y, ‖g (x - y)‖₊ ^ q.toReal) ^ ((r - q) / (q * r)).toReal =
          (∫⁻ y, ‖f y‖₊ ^ p.toReal * ‖g (x - y)‖₊ ^ q.toReal) ^ (1 / r.toReal) *
            (eLpNorm f p volume) ^ (1 - p / r).toReal *
          (eLpNorm g q volume) ^ (1 - q / r).toReal := by
        -- Second factor: both equal 1 since p = r
        rw [h_second_factor_eq_one, h_eLpNorm_factor_eq_one]
        -- Transform third factor
        rw [h_translate, h_exp_eq', h_eLpNorm_eq]
        rw [← ENNReal.rpow_mul]
        congr 1
        ring_nf
      rw [h_rhs_eq]
      -- Prove the rest using two-function Hölder inequality
      -- When p = r, (r - p) / (p * r) = 0 so the second factor is 1
      rw [h_eLpNorm_factor_eq_one, mul_one]
      -- Goal: ∫ ‖f‖ * ‖g‖ ≤ (∫ ‖f‖^p * ‖g‖^q)^(1/r) * eLpNorm g q ^ (1 - q/r)
      -- Since p = r, q = 1
      -- ∫ ‖f‖ * ‖g‖ ≤ (∫ ‖f‖^r * ‖g‖)^(1/r) * eLpNorm g 1 ^ (1 - 1/r)
      have hr_pos' : 0 < r := one_pos.trans_le hr
      -- Handle p = 1 case specially (when p = q = r = 1)
      by_cases hp_one : p = 1
      · -- Case p = 1 (i.e., p = q = r = 1)
        -- From hp_eq_r : p = r and hp_one : p = 1, we get r = 1
        rw [hp_one] at hp_eq_r
        -- hp_eq_r : 1 = r, hq_eq_one : q = 1, hp_one : p = 1
        have hr_eq_one : r = 1 := hp_eq_r.symm
        -- Goal: ∫ ‖f‖ * ‖g‖ ≤ (∫ ‖f‖^1 * ‖g‖^1)^1 * (eLpNorm g 1)^0
        --       = ∫ ‖f‖ * ‖g‖ * 1 = ∫ ‖f‖ * ‖g‖
        have hp_toReal : p.toReal = 1 := by rw [hp_one]; simp
        have hq_toReal : q.toReal = 1 := by rw [hq_eq_one]; simp
        have hr_toReal : r.toReal = 1 := by rw [hr_eq_one]; simp
        have h_exp_one : (1 - q / r).toReal = 0 := by
          rw [hq_eq_one, hr_eq_one]
          simp only [ENNReal.div_self one_ne_zero ENNReal.one_ne_top,
                     tsub_self, ENNReal.toReal_zero]
        rw [h_exp_one, ENNReal.rpow_zero, mul_one]
        -- Goal: ∫ ‖f‖ * ‖g‖ ≤ (∫ ‖f‖^1 * ‖g‖^1)^1
        have h_r_inv_eq_one : (1 : ℝ) / r.toReal = 1 := by simp [hr_toReal]
        rw [h_r_inv_eq_one, ENNReal.rpow_one]
        -- Goal: ∫ ‖f‖ * ‖g‖ ≤ ∫ ‖f‖^1 * ‖g‖^1
        apply le_of_eq
        apply lintegral_congr
        intro y
        simp only [hp_toReal, hq_toReal, ENNReal.rpow_one]
      -- For p ≠ 1 case, show 1 < r
      have hr_gt_one : 1 < r := by
        rw [← hp_eq_r]
        have hp_gt_one : 1 < p := lt_of_le_of_ne hp (Ne.symm hp_one)
        exact hp_gt_one
      -- a = ‖f‖ * ‖g‖^{1/r}, b = ‖g‖^{1-1/r}
      let a : (Fin n → ℝ) → ℝ≥0∞ := fun y => ‖f y‖₊ * ‖g (x - y)‖₊ ^ (1/r).toReal
      let b : (Fin n → ℝ) → ℝ≥0∞ := fun y => ‖g (x - y)‖₊ ^ (1 - 1/r).toReal
      -- Show ‖f‖ * ‖g‖ = a * b
      have h_prod_eq : ∀ y, (‖f y‖₊ : ℝ≥0∞) * ‖g (x - y)‖₊ = a y * b y := by
        intro y
        simp only [a, b]
        rw [mul_assoc]
        congr 1
        rw [← ENNReal.rpow_add_of_nonneg _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
        have h_exp_sum : (1/r).toReal + (1 - 1/r).toReal = 1 := by
          have h_le : 1/r ≤ 1 := by
            rw [ENNReal.div_le_iff (ne_of_gt hr_pos') hr_ne_top]
            simp only [one_mul]; exact hr
          have h_ne_top :
            (1 : ℝ≥0∞)/r ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top (ne_of_gt hr_pos')
          rw [ENNReal.toReal_sub_of_le h_le ENNReal.one_ne_top]
          simp only [ENNReal.toReal_one, ENNReal.toReal_div]
          have hr_pos_real : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt hr_pos') hr_ne_top
          field_simp [ne_of_gt hr_pos_real]
          ring
        rw [h_exp_sum, ENNReal.rpow_one]
      -- Apply Hölder inequality
      have h_a_pow : ∀ y, a y ^ r.toReal = ‖f y‖₊ ^ r.toReal * ‖g (x - y)‖₊ := by
        intro y
        simp only [a]
        rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
        congr 1
        rw [← ENNReal.rpow_mul]
        have h_exp : (1/r).toReal * r.toReal = 1 := by
          rw [ENNReal.toReal_div, ENNReal.toReal_one]
          have hr_pos_real : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt hr_pos') hr_ne_top
          field_simp [ne_of_gt hr_pos_real]
        rw [h_exp, ENNReal.rpow_one]
      have h_b_pow : ∀ y, b y ^ (r / (r - 1)).toReal = ‖g (x - y)‖₊ := by
        intro y
        simp only [b]
        rw [← ENNReal.rpow_mul]
        have h_exp : (1 - 1/r).toReal * (r / (r - 1)).toReal = 1 := by
          have h_le : 1/r ≤ 1 := by
            rw [ENNReal.div_le_iff (ne_of_gt hr_pos') hr_ne_top]
            simp only [one_mul]; exact hr
          rw [ENNReal.toReal_sub_of_le h_le ENNReal.one_ne_top]
          rw [ENNReal.toReal_div, ENNReal.toReal_div]
          rw [ENNReal.toReal_sub_of_le (le_of_lt hr_gt_one) hr_ne_top]
          simp only [ENNReal.toReal_one]
          have hr_ne : r.toReal ≠ 0 := ne_of_gt hr_pos
          have hr_sub_ne : r.toReal - 1 ≠ 0 := by
            have h1 : (1 : ℝ≥0∞).toReal < r.toReal :=
              ENNReal.toReal_lt_toReal ENNReal.one_ne_top hr_ne_top |>.mpr hr_gt_one
            simp only [ENNReal.toReal_one] at h1
            linarith
          field_simp [hr_ne, hr_sub_ne]
        rw [h_exp, ENNReal.rpow_one]
      -- From hq_eq_one, q = 1, so ‖g‖^q = ‖g‖
      have h_q_toReal_one : q.toReal = 1 := by rw [hq_eq_one]; simp
      have h_p_eq_r_toReal : p.toReal = r.toReal := by rw [hp_eq_r]
      -- Rewrite integrals
      have h_int_a_pow : ∫⁻ y, a y ^ r.toReal ∂volume =
          ∫⁻ y, ‖f y‖₊ ^ p.toReal * ‖g (x - y)‖₊ ^ q.toReal ∂volume := by
        apply lintegral_congr
        intro y
        rw [h_a_pow, h_p_eq_r_toReal, h_q_toReal_one, ENNReal.rpow_one]
      have h_int_b_pow : ∫⁻ y, b y ^ (r / (r - 1)).toReal ∂volume =
          ∫⁻ y, ‖g (x - y)‖₊ ∂volume := by
        apply lintegral_congr
        intro y
        rw [h_b_pow]
      -- Convert exponent (r-1)/r to the form 1 - q/r
      have h_exp_conv : (1 - q / r).toReal = ((r - 1) / r).toReal := by
        rw [hq_eq_one]
        have h_le : 1 / r ≤ 1 := by
          rw [ENNReal.div_le_iff (ne_of_gt hr_pos') hr_ne_top]
          simp only [one_mul]; exact hr
        have h_le' : 1 ≤ r := hr
        rw [ENNReal.toReal_sub_of_le h_le ENNReal.one_ne_top]
        rw [ENNReal.toReal_div, ENNReal.toReal_div]
        rw [ENNReal.toReal_sub_of_le h_le' hr_ne_top]
        simp only [ENNReal.toReal_one]
        have hr_ne : r.toReal ≠ 0 := ne_of_gt hr_pos
        field_simp [hr_ne]
      -- eLpNorm g 1 = ∫ ‖g‖ (L^1 norm)
      have h_eLpNorm_g_one : eLpNorm g q volume = ∫⁻ z, ‖g z‖₊ ∂volume := by
        rw [hq_eq_one]
        unfold eLpNorm eLpNorm'
        simp only [ENNReal.one_ne_top, reduceIte, ENNReal.toReal_one,
          one_ne_zero, ENNReal.rpow_one, one_div, inv_one, enorm_eq_nnnorm]
      -- Transform the RHS
      calc ∫⁻ y, ‖f y‖₊ * ‖g (x - y)‖₊ ∂volume
          = ∫⁻ y, a y * b y ∂volume := by
            apply lintegral_congr; intro y; exact h_prod_eq y
        _ ≤ (∫⁻ y, a y ^ r.toReal ∂volume) ^ (1/r.toReal) *
            (∫⁻ y, b y ^ (r/(r-1)).toReal ∂volume) ^ ((r-1)/r).toReal := by
            -- Apply two-function Hölder inequality
            have ha_ae : AEMeasurable a volume := by
              simp only [a]
              have hf_aesm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
              have hf_nnnorm : AEMeasurable (fun y => (‖f y‖₊ : ℝ≥0∞)) volume := by
                simpa [enorm_eq_nnnorm] using hf_aesm.enorm
              have hg_aesm : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
              have hg_comp_aesm : AEStronglyMeasurable (fun y => g (x - y)) volume := by
                have h_pres : MeasurePreserving (fun y : Fin n → ℝ => x - y) volume volume := by
                  have : MeasurePreserving (fun y : Fin n → ℝ => -y) volume volume :=
                    Measure.measurePreserving_neg volume
                  simpa [Function.comp_def, sub_eq_add_neg] using measurePreserving_add_left volume x |>.comp this
                exact hg_aesm.comp_measurePreserving h_pres
              have hg_nnnorm : AEMeasurable (fun y => (‖g (x - y)‖₊ : ℝ≥0∞)) volume := by
                simpa [enorm_eq_nnnorm] using hg_comp_aesm.enorm
              exact hf_nnnorm.mul (hg_nnnorm.pow_const _)
            have hb_ae : AEMeasurable b volume := by
              simp only [b]
              have hg_aesm : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
              have hg_comp_aesm : AEStronglyMeasurable (fun y => g (x - y)) volume := by
                have h_pres : MeasurePreserving (fun y : Fin n → ℝ => x - y) volume volume := by
                  have : MeasurePreserving (fun y : Fin n → ℝ => -y) volume volume :=
                    Measure.measurePreserving_neg volume
                  simpa [Function.comp_def, sub_eq_add_neg] using measurePreserving_add_left volume x |>.comp this
                exact hg_aesm.comp_measurePreserving h_pres
              have hg_nnnorm : AEMeasurable (fun y => (‖g (x - y)‖₊ : ℝ≥0∞)) volume := by
                simpa [enorm_eq_nnnorm] using hg_comp_aesm.enorm
              exact hg_nnnorm.pow_const _
            -- Define helper facts at this scope level
            have hr_ne : r.toReal ≠ 0 := ne_of_gt hr_pos
            have hr_sub_ne : r.toReal - 1 ≠ 0 := by
              have h1 : (1 : ℝ≥0∞).toReal < r.toReal :=
                ENNReal.toReal_lt_toReal ENNReal.one_ne_top hr_ne_top |>.mpr hr_gt_one
              simp only [ENNReal.toReal_one] at h1
              linarith
            have hq' : (r / (r - 1)).toReal = r.toReal / (r.toReal - 1) := by
              rw [ENNReal.toReal_div]
              congr 1
              rw [ENNReal.toReal_sub_of_le (le_of_lt hr_gt_one) hr_ne_top]
              simp only [ENNReal.toReal_one]
            have hr_sub_one_pos : 0 < r.toReal - 1 := by
              have h1 : (1 : ℝ≥0∞).toReal < r.toReal :=
                ENNReal.toReal_lt_toReal ENNReal.one_ne_top hr_ne_top |>.mpr hr_gt_one
              simp only [ENNReal.toReal_one] at h1
              linarith
            have hq'_pos : 0 < (r / (r - 1)).toReal := by
              rw [hq']
              exact div_pos hr_pos hr_sub_one_pos
            have h_conj_real : r.toReal.HolderConjugate (r / (r - 1)).toReal := by
              constructor
              · -- p⁻¹ + q⁻¹ = 1⁻¹ = 1
                rw [hq', inv_one]
                field_simp [hr_ne, hr_sub_ne]
                ring
              · exact hr_pos
              · exact hq'_pos
            -- Convert RHS exponent 1/(r/(r-1)) = (r-1)/r of Hölder inequality
            have h_exp_eq'' : (1 / (r / (r - 1)).toReal) = ((r - 1) / r).toReal := by
              rw [hq']
              rw [ENNReal.toReal_div]
              rw [ENNReal.toReal_sub_of_le (le_of_lt hr_gt_one) hr_ne_top]
              simp only [ENNReal.toReal_one]
              field_simp [hr_ne, hr_sub_ne]
            -- Use calc to prove the inequality via Hölder
            calc ∫⁻ y, a y * b y ∂volume
                ≤ (∫⁻ y, a y ^ r.toReal ∂volume) ^ (1/r.toReal) *
                    (∫⁻ y, b y ^ (r/(r-1)).toReal ∂volume) ^ (1/(r/(r-1)).toReal) :=
                  ENNReal.lintegral_mul_le_Lp_mul_Lq volume h_conj_real ha_ae hb_ae
              _ = (∫⁻ y, a y ^ r.toReal ∂volume) ^ (1/r.toReal) *
                    (∫⁻ y, b y ^ (r/(r-1)).toReal ∂volume) ^ ((r-1)/r).toReal := by
                  rw [h_exp_eq'']
        _ = (∫⁻ y, ‖f y‖₊ ^ p.toReal * ‖g (x - y)‖₊ ^ q.toReal ∂volume) ^ (1/r.toReal) *
            (∫⁻ y, ‖g (x - y)‖₊ ∂volume) ^ ((r-1)/r).toReal := by
            rw [h_int_a_pow, h_int_b_pow]
        _ = (∫⁻ y, ‖f y‖₊ ^ p.toReal * ‖g (x - y)‖₊ ^ q.toReal ∂volume) ^ (1/r.toReal) *
            (∫⁻ z, ‖g z‖₊ ∂volume) ^ ((r-1)/r).toReal := by
            -- Translation invariance
            have h_translate' : ∫⁻ y, ‖g (x - y)‖₊ ∂volume = ∫⁻ z, ‖g z‖₊ ∂volume :=
              lintegral_sub_left_eq_self (fun z => (‖g z‖₊ : ℝ≥0∞)) x
            rw [h_translate']
        _ = (∫⁻ y, ‖f y‖₊ ^ p.toReal * ‖g (x - y)‖₊ ^ q.toReal ∂volume) ^ (1/r.toReal) *
            (eLpNorm g q volume) ^ (1 - q/r).toReal := by
            rw [h_exp_conv, h_eLpNorm_g_one]
    · -- Non-endpoint case: p ≠ r
      -- First handle the q = r case (endpoint case 2)
      by_cases hq_eq_r : q = r
      · -- Endpoint case 2: q = r (then p = 1 from Young condition)
        -- From Young condition 1/p + 1/q = 1 + 1/r and q = r, we get 1/p = 1, i.e., p = 1
        have hp_eq_one : p = 1 := by
          have h : 1/p + 1/q = 1 + 1/r := hpqr
          rw [hq_eq_r] at h
          -- h : 1/p + 1/r = 1 + 1/r
          have hr_pos : r ≠ 0 := ne_of_gt (one_pos.trans_le hr)
          have h_inv_r_ne_top : 1/r ≠ ⊤ := ENNReal.div_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤) hr_pos
          have h_add_cancel : 1/p + 1/r = 1 + 1/r := h
          have h_one_div_p : 1/p = 1 := by
            have h' : 1/r + 1/p = 1/r + 1 :=
              by rw [add_comm] at h_add_cancel; rw [h_add_cancel]; ring
            exact (ENNReal.add_right_inj h_inv_r_ne_top).mp h'
          simp only [one_div] at h_one_div_p
          exact ENNReal.inv_eq_one.mp h_one_div_p
        -- Case p = 1, q = r
        -- Goal: ∫ ‖f‖ * ‖g‖ ≤ (∫ ‖f‖^1 * ‖g‖^r)^(1/r) * ‖f‖_1^(1-1/r) * ‖g‖_r^0
        have hr_pos' : 0 < r := one_pos.trans_le hr
        have hr_pos : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt hr_pos') hr_ne_top
        -- Since q = r, (r - q) / (q * r) = 0
        have h_r_sub_q_zero : r - q = 0 := by rw [hq_eq_r]; simp
        have h_exp_zero : ((r - q) / (q * r)).toReal = 0 := by
          rw [h_r_sub_q_zero, ENNReal.zero_div, ENNReal.toReal_zero]
        rw [h_exp_zero, ENNReal.rpow_zero, mul_one]
        -- Goal: ∫ ‖f‖ * ‖g‖ ≤ (∫ ‖f‖^1 * ‖g‖^r)^(1/r) * ‖f‖_1^(1-1/r)
        -- Since p = 1, p/r = 1/r, and 1 - p/r = 1 - 1/r = (r-1)/r
        have hp_toReal : p.toReal = 1 := by rw [hp_eq_one]; simp
        have hq_toReal : q.toReal = r.toReal := by rw [hq_eq_r]
        -- Consider 1 < r case (if r = 1, then p = q = r = 1 already handled in p = r case)
        by_cases hr_eq_one : r = 1
        · -- If r = 1, then q = 1 and p = 1, leading to p = r, a contradiction
          rw [hr_eq_one] at hq_eq_r
          -- q = 1, p = 1 but p ≠ r = 1 is a contradiction
          rw [hp_eq_one, hr_eq_one] at hp_eq_r
          exact absurd rfl hp_eq_r
        -- Since r ≠ 1, we have 1 < r
        have hr_gt_one : 1 < r := lt_of_le_of_ne hr (Ne.symm hr_eq_one)
        -- Apply Hölder with a = ‖g‖ * ‖f‖^{1/r}, b = ‖f‖^{1-1/r}
        let a : (Fin n → ℝ) → ℝ≥0∞ := fun y => ‖g (x - y)‖₊ * ‖f y‖₊ ^ (1/r).toReal
        let b : (Fin n → ℝ) → ℝ≥0∞ := fun y => ‖f y‖₊ ^ (1 - 1/r).toReal
        have h_prod_eq : ∀ y, (‖f y‖₊ : ℝ≥0∞) * ‖g (x - y)‖₊ = a y * b y := by
          intro y
          simp only [a, b]
          rw [mul_comm (‖f y‖₊ : ℝ≥0∞) _, mul_assoc]
          congr 1
          rw [← ENNReal.rpow_add_of_nonneg _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
          have h_exp_sum : (1/r).toReal + (1 - 1/r).toReal = 1 := by
            have h_le : 1/r ≤ 1 := by
              rw [ENNReal.div_le_iff (ne_of_gt hr_pos') hr_ne_top]
              simp only [one_mul]; exact hr
            have h_ne_top : (1 : ℝ≥0∞)/r ≠ ⊤ :=
              ENNReal.div_ne_top ENNReal.one_ne_top (ne_of_gt hr_pos')
            rw [ENNReal.toReal_sub_of_le h_le ENNReal.one_ne_top]
            simp only [ENNReal.toReal_one, ENNReal.toReal_div]
            field_simp [ne_of_gt hr_pos]
            ring
          rw [h_exp_sum, ENNReal.rpow_one]
        have h_a_pow : ∀ y, a y ^ r.toReal = ‖g (x - y)‖₊ ^ r.toReal * ‖f y‖₊ := by
          intro y
          simp only [a]
          rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
          congr 1
          rw [← ENNReal.rpow_mul]
          have h_exp : (1/r).toReal * r.toReal = 1 := by
            rw [ENNReal.toReal_div, ENNReal.toReal_one]
            field_simp [ne_of_gt hr_pos]
          rw [h_exp, ENNReal.rpow_one]
        have h_b_pow : ∀ y, b y ^ (r / (r - 1)).toReal = ‖f y‖₊ := by
          intro y
          simp only [b]
          rw [← ENNReal.rpow_mul]
          have h_exp : (1 - 1/r).toReal * (r / (r - 1)).toReal = 1 := by
            have h_le : 1/r ≤ 1 := by
              rw [ENNReal.div_le_iff (ne_of_gt hr_pos') hr_ne_top]
              simp only [one_mul]; exact hr
            rw [ENNReal.toReal_sub_of_le h_le ENNReal.one_ne_top]
            rw [ENNReal.toReal_div, ENNReal.toReal_div]
            rw [ENNReal.toReal_sub_of_le (le_of_lt hr_gt_one) hr_ne_top]
            simp only [ENNReal.toReal_one]
            have hr_ne : r.toReal ≠ 0 := ne_of_gt hr_pos
            have hr_sub_ne : r.toReal - 1 ≠ 0 := by
              have h1 : (1 : ℝ≥0∞).toReal < r.toReal :=
                ENNReal.toReal_lt_toReal ENNReal.one_ne_top hr_ne_top |>.mpr hr_gt_one
              simp only [ENNReal.toReal_one] at h1
              linarith
            field_simp [hr_ne, hr_sub_ne]
          rw [h_exp, ENNReal.rpow_one]
        have h_int_a_pow : ∫⁻ y, a y ^ r.toReal ∂volume =
            ∫⁻ y, ‖f y‖₊ ^ p.toReal * ‖g (x - y)‖₊ ^ q.toReal ∂volume := by
          apply lintegral_congr
          intro y
          rw [h_a_pow, hp_toReal, hq_toReal, ENNReal.rpow_one, mul_comm]
        have h_int_b_pow : ∫⁻ y, b y ^ (r / (r - 1)).toReal ∂volume =
            ∫⁻ y, ‖f y‖₊ ∂volume := by
          apply lintegral_congr
          intro y
          rw [h_b_pow]
        have h_eLpNorm_f_one : eLpNorm f p volume = ∫⁻ z, ‖f z‖₊ ∂volume := by
          rw [hp_eq_one]
          unfold eLpNorm eLpNorm'
          simp only [ENNReal.one_ne_top, reduceIte, ENNReal.toReal_one,
            one_ne_zero, ENNReal.rpow_one, one_div, inv_one, enorm_eq_nnnorm]
        -- Convert exponents
        have h_exp_conv : (1 - p / r).toReal = ((r - 1) / r).toReal := by
          rw [hp_eq_one]
          have h_le : 1 / r ≤ 1 := by
            rw [ENNReal.div_le_iff (ne_of_gt hr_pos') hr_ne_top]
            simp only [one_mul]; exact hr
          rw [ENNReal.toReal_sub_of_le h_le ENNReal.one_ne_top]
          rw [ENNReal.toReal_div, ENNReal.toReal_div]
          rw [ENNReal.toReal_sub_of_le hr hr_ne_top]
          simp only [ENNReal.toReal_one]
          have hr_ne : r.toReal ≠ 0 := ne_of_gt hr_pos
          field_simp [hr_ne]
        -- Apply Hölder inequality
        have ha_ae : AEMeasurable a volume := by
          simp only [a]
          have hg_aesm : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
          have hg_comp_aesm : AEStronglyMeasurable (fun y => g (x - y)) volume := by
            have h_pres : MeasurePreserving (fun y : Fin n → ℝ => x - y) volume volume := by
              have : MeasurePreserving (fun y : Fin n → ℝ => -y) volume volume :=
                Measure.measurePreserving_neg volume
              simpa [Function.comp_def, sub_eq_add_neg] using measurePreserving_add_left volume x |>.comp this
            exact hg_aesm.comp_measurePreserving h_pres
          have hg_nnnorm : AEMeasurable (fun y => (‖g (x - y)‖₊ : ℝ≥0∞)) volume := by
            simpa [enorm_eq_nnnorm] using hg_comp_aesm.enorm
          have hf_aesm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
          have hf_nnnorm : AEMeasurable (fun y => (‖f y‖₊ : ℝ≥0∞)) volume := by
            simpa [enorm_eq_nnnorm] using hf_aesm.enorm
          exact hg_nnnorm.mul (hf_nnnorm.pow_const _)
        have hb_ae : AEMeasurable b volume := by
          simp only [b]
          have hf_aesm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
          have hf_nnnorm : AEMeasurable (fun y => (‖f y‖₊ : ℝ≥0∞)) volume := by
            simpa [enorm_eq_nnnorm] using hf_aesm.enorm
          exact hf_nnnorm.pow_const _
        have hr_ne : r.toReal ≠ 0 := ne_of_gt hr_pos
        have hr_sub_ne : r.toReal - 1 ≠ 0 := by
          have h1 : (1 : ℝ≥0∞).toReal < r.toReal :=
            ENNReal.toReal_lt_toReal ENNReal.one_ne_top hr_ne_top |>.mpr hr_gt_one
          simp only [ENNReal.toReal_one] at h1
          linarith
        have hq' : (r / (r - 1)).toReal = r.toReal / (r.toReal - 1) := by
          rw [ENNReal.toReal_div]
          congr 1
          rw [ENNReal.toReal_sub_of_le (le_of_lt hr_gt_one) hr_ne_top]
          simp only [ENNReal.toReal_one]
        have hr_sub_one_pos : 0 < r.toReal - 1 := by
          have h1 : (1 : ℝ≥0∞).toReal < r.toReal :=
            ENNReal.toReal_lt_toReal ENNReal.one_ne_top hr_ne_top |>.mpr hr_gt_one
          simp only [ENNReal.toReal_one] at h1
          linarith
        have hq'_pos : 0 < (r / (r - 1)).toReal := by
          rw [hq']
          exact div_pos hr_pos hr_sub_one_pos
        have h_conj_real : r.toReal.HolderConjugate (r / (r - 1)).toReal := by
          constructor
          · rw [hq', inv_one]
            field_simp [hr_ne, hr_sub_ne]
            ring
          · exact hr_pos
          · exact hq'_pos
        have h_exp_eq'' : (1 / (r / (r - 1)).toReal) = ((r - 1) / r).toReal := by
          rw [hq']
          rw [ENNReal.toReal_div]
          rw [ENNReal.toReal_sub_of_le (le_of_lt hr_gt_one) hr_ne_top]
          simp only [ENNReal.toReal_one]
          field_simp [hr_ne, hr_sub_ne]
        -- Convert exponents: ((r - p) / (p * r)).toReal = ((r - 1) / r).toReal (since p = 1)
        have h_exp_conv' : ((r - p) / (p * r)).toReal = ((r - 1) / r).toReal := by
          rw [hp_eq_one]
          simp only [one_mul]
        calc ∫⁻ y, ‖f y‖₊ * ‖g (x - y)‖₊ ∂volume
            = ∫⁻ y, a y * b y ∂volume := by
              apply lintegral_congr; intro y; exact h_prod_eq y
          _ ≤ (∫⁻ y, a y ^ r.toReal ∂volume) ^ (1/r.toReal) *
              (∫⁻ y, b y ^ (r/(r-1)).toReal ∂volume) ^ ((r-1)/r).toReal := by
              calc ∫⁻ y, a y * b y ∂volume
                  ≤ (∫⁻ y, a y ^ r.toReal ∂volume) ^ (1/r.toReal) *
                      (∫⁻ y, b y ^ (r/(r-1)).toReal ∂volume) ^ (1/(r/(r-1)).toReal) :=
                    ENNReal.lintegral_mul_le_Lp_mul_Lq volume h_conj_real ha_ae hb_ae
                _ = (∫⁻ y, a y ^ r.toReal ∂volume) ^ (1/r.toReal) *
                      (∫⁻ y, b y ^ (r/(r-1)).toReal ∂volume) ^ ((r-1)/r).toReal := by
                    rw [h_exp_eq'']
          _ = (∫⁻ y, ‖f y‖₊ ^ p.toReal * ‖g (x - y)‖₊ ^ q.toReal ∂volume) ^ (1/r.toReal) *
              (∫⁻ y, ‖f y‖₊ ∂volume) ^ ((r-1)/r).toReal := by
              rw [h_int_a_pow, h_int_b_pow]
          _ = (∫⁻ y, ‖f y‖₊ ^ p.toReal * ‖g (x - y)‖₊ ^ q.toReal ∂volume) ^ (1/r.toReal) *
              (∫⁻ y, ‖f y‖₊ ^ p.toReal ∂volume) ^ ((r - p) / (p * r)).toReal := by
              rw [h_exp_conv']
              congr 2
              apply lintegral_congr
              intro y
              rw [hp_toReal, ENNReal.rpow_one]
      -- Case q ≠ r (true non-endpoint case)
      let P : ℝ≥0∞ := r
      let Q : ℝ≥0∞ := (p * r) / (r - p)
      let R : ℝ≥0∞ := (q * r) / (r - q)
      -- Verify exponent conditions for P, Q, R
      have hP_ne_top : P ≠ ⊤ := hr_ne_top
      have hQ_ne_top : Q ≠ ⊤ := by
        simp only [Q]
        apply ENNReal.div_ne_top
        · exact ENNReal.mul_ne_top hp_ne_top hr_ne_top
        · intro h
          have h_sub_zero : r - p = 0 := h
          have hp_le_r : p ≤ r := young_exponent_p_le_r hq hpqr
          have h_ge : r ≤ p := tsub_eq_zero_iff_le.mp h_sub_zero
          have h_eq : p = r := le_antisymm hp_le_r h_ge
          exact hp_eq_r h_eq
      have hR_ne_top : R ≠ ⊤ := by
        simp only [R]
        apply ENNReal.div_ne_top
        · exact ENNReal.mul_ne_top hq_ne_top hr_ne_top
        · intro h
          have h_sub_zero : r - q = 0 := h
          have hq_le_r : q ≤ r := young_exponent_q_le_r hp hpqr
          have h_ge : r ≤ q := tsub_eq_zero_iff_le.mp h_sub_zero
          have h_eq : q = r := le_antisymm hq_le_r h_ge
          exact hq_eq_r h_eq
      have hPQR : 1/P + 1/Q + 1/R = 1 := by
        simp only [P, Q, R]
        -- 1/r + (r-p)/(pr) + (r-q)/(qr) = 1 is obtained from h_three_exp
        have h1 : (1 : ℝ≥0∞) / r = 1 / r := rfl
        have h_r_sub_p_ne_zero : r - p ≠ 0 := by
          intro h
          have h_ge : r ≤ p := tsub_eq_zero_iff_le.mp h
          have hp_le_r : p ≤ r := young_exponent_p_le_r hq hpqr
          exact hp_eq_r (le_antisymm hp_le_r h_ge)
        have h_r_sub_q_ne_zero : r - q ≠ 0 := by
          intro h
          have h_ge : r ≤ q := tsub_eq_zero_iff_le.mp h
          have hq_le_r : q ≤ r := young_exponent_q_le_r hp hpqr
          have hq_eq_r' : q = r := le_antisymm hq_le_r h_ge
          exact hq_eq_r hq_eq_r'
        have hp_ne_zero : p ≠ 0 := ne_of_gt (one_pos.trans_le hp)
        have hq_ne_zero : q ≠ 0 := ne_of_gt (one_pos.trans_le hq)
        have hr_ne_zero : r ≠ 0 := ne_of_gt (one_pos.trans_le hr)
        have h_pr_ne_zero : p * r ≠ 0 := mul_ne_zero hp_ne_zero hr_ne_zero
        have h_qr_ne_zero : q * r ≠ 0 := mul_ne_zero hq_ne_zero hr_ne_zero
        have h2 : (1 : ℝ≥0∞) / ((p * r) / (r - p)) = (r - p) / (p * r) := by
          rw [one_div, ENNReal.inv_div]
          · right; exact ENNReal.mul_ne_top hp_ne_top hr_ne_top
          · right; exact h_pr_ne_zero
        have h3 : (1 : ℝ≥0∞) / ((q * r) / (r - q)) = (r - q) / (q * r) := by
          rw [one_div, ENNReal.inv_div]
          · right; exact ENNReal.mul_ne_top hq_ne_top hr_ne_top
          · right; exact h_qr_ne_zero
        rw [h1, h2, h3]
        exact h_three_exp
      calc ∫⁻ y, ‖f y‖₊ * ‖g (x - y)‖₊ ∂volume
          = ∫⁻ y, F y * G y * H y ∂volume := by
            apply lintegral_congr
            intro y
            exact h_pointwise y
        _ ≤ (∫⁻ y, F y ^ P.toReal ∂volume) ^ (1/P.toReal) *
            (∫⁻ y, G y ^ Q.toReal ∂volume) ^ (1/Q.toReal) *
            (∫⁻ y, H y ^ R.toReal ∂volume) ^ (1/R.toReal) := by
          exact lintegral_mul_mul_le_three_holder
            hPQR hP_ne_top hQ_ne_top hR_ne_top hF_ae hG_ae hH_ae
        _ = (∫⁻ y, ‖f y‖₊ ^ p.toReal * ‖g (x - y)‖₊ ^ q.toReal ∂volume) ^ (1/r.toReal) *
            (∫⁻ y, ‖f y‖₊ ^ p.toReal ∂volume) ^ ((r - p) / (p * r)).toReal *
            (∫⁻ y, ‖g (x - y)‖₊ ^ q.toReal ∂volume) ^ ((r - q) / (q * r)).toReal := by
          simp only [P, Q, R]
          congr 1
          · congr 1
            -- Show (∫ F^r)^(1/r) = (∫ ‖f‖^p * ‖g‖^q)^(1/r)
            · congr 1
              apply lintegral_congr
              intro y
              simp only [F]
              rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
              congr 1
              · rw [← ENNReal.rpow_mul, ENNReal.toReal_div]
                congr 1
                have hr_ne : r.toReal ≠ 0 :=
                  ne_of_gt (ENNReal.toReal_pos (ne_of_gt (one_pos.trans_le hr)) hr_ne_top)
                field_simp [hr_ne]
              · rw [← ENNReal.rpow_mul, ENNReal.toReal_div]
                congr 1
                have hr_ne : r.toReal ≠ 0 :=
                  ne_of_gt (ENNReal.toReal_pos (ne_of_gt (one_pos.trans_le hr)) hr_ne_top)
                field_simp [hr_ne]
            -- Show (∫ G^Q)^(1/Q) = (∫ ‖f‖^p)^((r-p)/(pr))
            · have h_Q_inv : (1 : ℝ) / Q.toReal = ((r - p) / (p * r)).toReal := by
                simp only [Q]
                rw [ENNReal.toReal_div, ENNReal.toReal_mul]
                rw [ENNReal.toReal_sub_of_le (young_exponent_p_le_r hq hpqr) hr_ne_top]
                have hr_ne : r.toReal ≠ 0 :=
                  ne_of_gt (ENNReal.toReal_pos (ne_of_gt (one_pos.trans_le hr)) hr_ne_top)
                have hp_lt_r : p < r := lt_of_le_of_ne (young_exponent_p_le_r hq hpqr) hp_eq_r
                have h_sub_ne : r.toReal - p.toReal ≠ 0 := by
                  have h : p.toReal < r.toReal :=
                    ENNReal.toReal_lt_toReal hp_ne_top hr_ne_top |>.mpr hp_lt_r
                  linarith
                have h_pr_ne : p.toReal * r.toReal ≠ 0 := mul_ne_zero
                  (ne_of_gt (ENNReal.toReal_pos (ne_of_gt (one_pos.trans_le hp)) hp_ne_top))
                  hr_ne
                rw [ENNReal.toReal_div, ENNReal.toReal_mul]
                rw [ENNReal.toReal_sub_of_le (young_exponent_p_le_r hq hpqr) hr_ne_top]
                field_simp [h_pr_ne, h_sub_ne]
              rw [h_Q_inv]
              congr 1
              -- Show (∫ G^Q) = (∫ ‖f‖^p)
              apply lintegral_congr
              intro y
              simp only [G]
              rw [← ENNReal.rpow_mul]
              congr 1
              -- Show (1 - p/r).toReal * ((pr)/(r-p)).toReal = p.toReal
              have hp_le_r : p ≤ r := young_exponent_p_le_r hq hpqr
              have h_le : p / r ≤ 1 := by
                rw [ENNReal.div_le_iff (ne_of_gt (one_pos.trans_le hr)) hr_ne_top, one_mul]
                exact hp_le_r
              rw [ENNReal.toReal_sub_of_le h_le (by simp : (1 : ℝ≥0∞) ≠ ⊤)]
              rw [ENNReal.toReal_div, ENNReal.toReal_one]
              rw [ENNReal.toReal_div, ENNReal.toReal_mul]
              rw [ENNReal.toReal_sub_of_le hp_le_r hr_ne_top]
              have hr_ne : r.toReal ≠ 0 :=
                ne_of_gt (ENNReal.toReal_pos (ne_of_gt (one_pos.trans_le hr)) hr_ne_top)
              have hp_lt_r : p < r := lt_of_le_of_ne hp_le_r hp_eq_r
              have h_sub_ne : r.toReal - p.toReal ≠ 0 := by
                have h : p.toReal < r.toReal :=
                  ENNReal.toReal_lt_toReal hp_ne_top hr_ne_top |>.mpr hp_lt_r
                linarith
              field_simp [hr_ne, h_sub_ne]
          -- Show (∫ H^R)^(1/R) = (∫ ‖g‖^q)^((r-q)/(qr))
          · have hq_le_r : q ≤ r := young_exponent_q_le_r hp hpqr
            have hq_lt_r : q < r := lt_of_le_of_ne hq_le_r hq_eq_r
            have h_R_inv : (1 : ℝ) / R.toReal = ((r - q) / (q * r)).toReal := by
              simp only [R]
              rw [ENNReal.toReal_div, ENNReal.toReal_mul]
              rw [ENNReal.toReal_sub_of_le hq_le_r hr_ne_top]
              have hr_ne : r.toReal ≠ 0 :=
                ne_of_gt (ENNReal.toReal_pos (ne_of_gt (one_pos.trans_le hr)) hr_ne_top)
              have h_sub_ne : r.toReal - q.toReal ≠ 0 := by
                have h : q.toReal < r.toReal :=
                  ENNReal.toReal_lt_toReal hq_ne_top hr_ne_top |>.mpr hq_lt_r
                linarith
              have h_qr_ne : q.toReal * r.toReal ≠ 0 := mul_ne_zero
                (ne_of_gt (ENNReal.toReal_pos (ne_of_gt (one_pos.trans_le hq)) hq_ne_top))
                hr_ne
              rw [ENNReal.toReal_div, ENNReal.toReal_mul]
              rw [ENNReal.toReal_sub_of_le hq_le_r hr_ne_top]
              field_simp [h_qr_ne, h_sub_ne]
            rw [h_R_inv]
            congr 1
            -- Show (∫ H^R) = (∫ ‖g‖^q)
            apply lintegral_congr
            intro y
            simp only [H]
            rw [← ENNReal.rpow_mul]
            congr 1
            have h_le : q / r ≤ 1 := by
              rw [ENNReal.div_le_iff (ne_of_gt (one_pos.trans_le hr)) hr_ne_top, one_mul]
              exact hq_le_r
            rw [ENNReal.toReal_sub_of_le h_le (by simp : (1 : ℝ≥0∞) ≠ ⊤)]
            rw [ENNReal.toReal_div, ENNReal.toReal_one]
            rw [ENNReal.toReal_div, ENNReal.toReal_mul]
            rw [ENNReal.toReal_sub_of_le hq_le_r hr_ne_top]
            have hr_ne : r.toReal ≠ 0 :=
              ne_of_gt (ENNReal.toReal_pos (ne_of_gt (one_pos.trans_le hr)) hr_ne_top)
            have h_sub_ne : r.toReal - q.toReal ≠ 0 := by
              have h : q.toReal < r.toReal :=
                ENNReal.toReal_lt_toReal hq_ne_top hr_ne_top |>.mpr hq_lt_r
              linarith
            field_simp [hr_ne, h_sub_ne]
  -- The rest follows from the definition of eLpNorm
  -- (∫ ‖f‖₊^p)^{(r-p)/(pr)} = ‖f‖_p^{(r-p)/r} = ‖f‖_p^{1-p/r}
  have hf_pow :
      (∫⁻ y, ‖f y‖₊^p.toReal ∂volume)^((r - p) / (p * r)).toReal =
        (eLpNorm f p volume)^(1 - p/r).toReal := by
    -- Use the definition eLpNorm f p = (∫ ‖f‖₊^p)^{1/p}
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (one_pos.trans_le hp)) hp_ne_top
    have hr_pos : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt (one_pos.trans_le hr)) hr_ne_top
    have hp_le_r : p ≤ r := young_exponent_p_le_r hq hpqr
    -- Since (r-p)/(pr) = (1-p/r)/p, we have (∫ ‖f‖^p)^{(r-p)/(pr)} = (∫ ‖f‖^p)^{(1-p/r)/p}
    -- = ((∫ ‖f‖^p)^{1/p})^{1-p/r} = ‖f‖_p^{1-p/r}
    have h_exp_eq : ((r - p) / (p * r)).toReal = (1 - p/r).toReal / p.toReal := by
      rw [ENNReal.toReal_div, ENNReal.toReal_mul]
      rw [ENNReal.toReal_sub_of_le hp_le_r hr_ne_top]
      have h_le : p / r ≤ 1 := by
        rw [ENNReal.div_le_iff (ne_of_gt (one_pos.trans_le hr)) hr_ne_top, one_mul]
        exact hp_le_r
      rw [ENNReal.toReal_sub_of_le h_le (by simp : (1 : ℝ≥0∞) ≠ ⊤)]
      rw [ENNReal.toReal_div, ENNReal.toReal_one]
      have h_pr_ne : p.toReal * r.toReal ≠ 0 := by
        exact mul_ne_zero (ne_of_gt hp_pos) (ne_of_gt hr_pos)
      field_simp [h_pr_ne, ne_of_gt hp_pos, ne_of_gt hr_pos]
    -- Definition of eLpNorm: eLpNorm f p = (∫ ‖f‖^p)^{1/p}
    have hp_ne_zero : p ≠ 0 := ne_of_gt (one_pos.trans_le hp)
    have h_eLpNorm_eq :
        eLpNorm f p volume = (∫⁻ y, (‖f y‖₊ : ℝ≥0∞)^p.toReal ∂volume)^(1/p.toReal) := by
      unfold eLpNorm eLpNorm'
      simp only [one_div, hp_ne_top, reduceIte, hp_ne_zero, ↓reduceIte, enorm_eq_nnnorm]
    rw [h_exp_eq, h_eLpNorm_eq]
    -- Goal: (∫ ‖f‖^p)^((1-p/r)/p) = ((∫ ‖f‖^p)^(1/p))^(1-p/r)
    -- Use rpow_mul: x^(a/b) = (x^(1/b))^a when written correctly
    have h_exp_rearrange : (1 - p/r).toReal / p.toReal = 1/p.toReal * (1 - p/r).toReal := by
      ring
    rw [h_exp_rearrange]
    rw [← ENNReal.rpow_mul]
  have hg_pow :
      (∫⁻ y, ‖g (x - y)‖₊^q.toReal ∂volume)^((r - q) / (q * r)).toReal =
        (eLpNorm g q volume)^(1 - q/r).toReal := by
    -- Use translation invariance: ∫ ‖g(x-y)‖^q dy = ∫ ‖g(z)‖^q dz
    have hq_pos : 0 < q.toReal := ENNReal.toReal_pos (ne_of_gt (one_pos.trans_le hq)) hq_ne_top
    have hr_pos : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt (one_pos.trans_le hr)) hr_ne_top
    have hq_le_r : q ≤ r := young_exponent_q_le_r hp hpqr
    have h_translate : ∫⁻ y, ‖g (x - y)‖₊^q.toReal ∂volume = ∫⁻ z, ‖g z‖₊^q.toReal ∂volume :=
      lintegral_sub_left_eq_self (fun z => (‖g z‖₊ : ℝ≥0∞)^q.toReal) x
    rw [h_translate]
    -- The rest is similar to hf_pow
    have h_exp_eq : ((r - q) / (q * r)).toReal = (1 - q/r).toReal / q.toReal := by
      rw [ENNReal.toReal_div, ENNReal.toReal_mul]
      rw [ENNReal.toReal_sub_of_le hq_le_r hr_ne_top]
      have h_le : q / r ≤ 1 := by
        rw [ENNReal.div_le_iff (ne_of_gt (one_pos.trans_le hr)) hr_ne_top, one_mul]
        exact hq_le_r
      rw [ENNReal.toReal_sub_of_le h_le (by simp : (1 : ℝ≥0∞) ≠ ⊤)]
      rw [ENNReal.toReal_div, ENNReal.toReal_one]
      have h_qr_ne : q.toReal * r.toReal ≠ 0 := by
        exact mul_ne_zero (ne_of_gt hq_pos) (ne_of_gt hr_pos)
      field_simp [h_qr_ne, ne_of_gt hq_pos, ne_of_gt hr_pos]
    have hq_ne_zero : q ≠ 0 := ne_of_gt (one_pos.trans_le hq)
    have h_eLpNorm_eq :
        eLpNorm g q volume = (∫⁻ z, (‖g z‖₊ : ℝ≥0∞)^q.toReal ∂volume)^(1/q.toReal) := by
      unfold eLpNorm eLpNorm'
      simp only [hq_ne_top, hq_ne_zero, ite_false, enorm_eq_nnnorm]
    rw [h_exp_eq, h_eLpNorm_eq]
    have h_exp_rearrange : (1 - q/r).toReal / q.toReal = 1/q.toReal * (1 - q/r).toReal := by
      ring
    rw [h_exp_rearrange]
    rw [← ENNReal.rpow_mul]
  -- Substitute everything to reach conclusion
  -- Rewrite RHS of h_holder using hf_pow, hg_pow to match the goal
  calc ∫⁻ y, ‖f y‖₊ * ‖g (x - y)‖₊ ∂volume
      ≤ (∫⁻ y, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume)^(1/r.toReal) *
          (∫⁻ y, ‖f y‖₊^p.toReal ∂volume)^((r - p) / (p * r)).toReal *
        (∫⁻ y, ‖g (x - y)‖₊^q.toReal ∂volume)^((r - q) / (q * r)).toReal := h_holder
    _ = (∫⁻ y, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume)^(1/r.toReal) *
          (eLpNorm f p volume)^(1 - p/r).toReal *
        (eLpNorm g q volume)^(1 - q/r).toReal := by
          rw [hf_pow, hg_pow]
end Newton
