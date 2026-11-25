-- Prove2me | solution 1 for Newton.eLpNorm_norm_integral_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:09:51.353367+00:00
-- url     : https://prove2.me/submissions/cd122371-ee59-4345-a487-6d3291943394

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
import Theorems.Thm_Newton_lp_duality_norm_le_of_pairing_bound
import Theorems.Thm_Newton_conjugate_exponent_formula
import Theorems.Thm_Newton_holder_kernel_pairing_bound


set_option autoImplicit false
open scoped ENNReal
open MeasureTheory Real Topology
open Newton
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Newton
theorem _root_.solution
    [SFinite μ] [SFinite ν]
    (p : ℝ≥0∞) (hp : 1 < p) (hp_ne_top : p ≠ ∞)
    {F : α → β → E}
    (hF_meas : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hF_prod : Integrable (Function.uncurry F) (μ.prod ν))
    (hF_memLp : ∀ᵐ y ∂ν, MemLp (fun x => F x y) p μ)
    (hF_norm : Integrable (fun y => (eLpNorm (fun x => F x y) p μ).toReal) ν) :
    eLpNorm (fun x => ‖∫ y, F x y ∂ν‖) p μ < ∞ := by
  have hp_ne_zero : p ≠ 0 := by
    have : (0 : ℝ≥0∞) < p := lt_trans (by simp) hp
    exact ne_of_gt this
  have hp_lt_top : p < ∞ := lt_of_le_of_ne le_top hp_ne_top
  have h_integral_meas :
      AEStronglyMeasurable (fun x => ∫ y, F x y ∂ν) μ := by
    simpa using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := μ) (ν := ν) (f := Function.uncurry F) hF_meas)
  have h_norm_meas :
      AEStronglyMeasurable (fun x => ‖∫ y, F x y ∂ν‖) μ :=
    h_integral_meas.norm
  -- Extract the slice-wise information supplied by the product integrability assumption.
  have h_prod_info :=
    (integrable_prod_iff (μ := μ) (ν := ν)
      (f := Function.uncurry F) hF_meas).mp hF_prod
  have hF_int_left :
      ∀ᵐ x ∂μ, Integrable (fun y => F x y) ν := by
    simpa [Function.uncurry] using h_prod_info.1
  have h_majorant_int :
      Integrable (fun x => ∫ y, ‖F x y‖ ∂ν) μ := by
    simpa [Function.uncurry] using h_prod_info.2
  -- Pointwise domination by the integral of fibrewise norms.
  have h_pointwise :
      (fun x => ‖∫ y, F x y ∂ν‖)
        ≤ᵐ[μ]
          fun x => ∫ y, ‖F x y‖ ∂ν := by
    refine hF_int_left.mono ?_
    intro x hx
    have hx_bound :=
      norm_integral_le_integral_norm (μ := ν) (f := fun y => F x y)
    simpa using hx_bound
  -- Basic integrability of the norm of the fibrewise integral.
  have h_norm_integrable : Integrable (fun x => ‖∫ y, F x y ∂ν‖) μ := by
    refine Integrable.mono' h_majorant_int h_norm_meas ?_
    exact h_pointwise.mono fun _ ha => by simpa using ha
  -- Introduce the auxiliary notation that will be used in the duality argument.
  set g : α → ℝ := fun x => ‖∫ y, F x y ∂ν‖
  have hg_meas : AEStronglyMeasurable g μ := h_norm_meas
  have hg_int : Integrable g μ := by simpa [g] using h_norm_integrable
  obtain ⟨q, hpq, -⟩ :=
    conjugate_exponent_formula (p := p) hp hp_lt_top
  have hq_gt_one : 1 < q := by
    rcases hpq with hpq | hpq
    · rcases hpq with ⟨hp_eq, _⟩
      simp [hp_eq] at hp
    · rcases hpq with hpq | hpq
      · rcases hpq with ⟨hp_eq, _⟩
        simpa [hp_eq] using hp_lt_top.ne
      · rcases hpq with ⟨_, _, hq, _, _⟩
        exact hq
  set B : ℝ := ∫ y, (eLpNorm (fun x => F x y) p μ).toReal ∂ν
  have hB_nonneg : 0 ≤ B :=
    integral_nonneg fun _ => ENNReal.toReal_nonneg
  -- Pairing estimate coming from Hölder on each fibre.
  have h_pairing_bound :
      ∀ φ : α → ℝ,
        MemLp φ q μ →
        (eLpNorm φ q μ).toReal ≤ 1 →
        Integrable (fun x => g x * φ x) μ →
        |∫ x, g x * φ x ∂μ| ≤ B := by
    intro φ hφ_mem hφ_norm _hφ_int
    have h_est :=
      holder_kernel_pairing_bound (μ := μ) (ν := ν)
        (p := p) (q := q) hpq
        hF_meas hF_prod hF_memLp hF_norm hφ_mem
    have h_mul : (eLpNorm φ q μ).toReal * B ≤ B := by
      have := mul_le_mul_of_nonneg_right hφ_norm hB_nonneg
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    exact h_est.trans h_mul
  -- Deduce the finiteness of the `L^p` norm from the pairing bounds.
  set pr : ℝ := p.toReal with hpr
  have hp_ne_top : p ≠ ∞ := hp_ne_top
  have hp_toReal_pos : 0 < pr := by
    simpa [pr] using ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have hp_toReal_gt_one : 1 < pr :=
    by
      have :=
        (ENNReal.toReal_lt_toReal (a := (1 : ℝ≥0∞)) (b := p) (by simp) hp_ne_top).2 hp
      simpa [pr, hpr] using this
  have hp_toReal_ge_one : 1 ≤ pr := hp_toReal_gt_one.le
  have hp_toReal_ne_one : pr ≠ 1 := ne_of_gt hp_toReal_gt_one
  have hp_toReal_sub_pos : 0 < pr - 1 := by
    have := sub_pos.mpr hp_toReal_gt_one
    simpa using this
  have hp_toReal_sub_ne_zero : pr - 1 ≠ 0 := by
    have := sub_ne_zero_of_ne hp_toReal_ne_one
    simpa using this
  set qr : ℝ := q.toReal with hqr
  have hq_ne_zero : q ≠ 0 := by
    have : (0 : ℝ≥0∞) < q := lt_of_lt_of_le
      (by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)) hq_gt_one.le
    exact ne_of_gt this
  have hq_ne_top : q ≠ ∞ := by
    rcases hpq with hpq₁ | hpq₂ | hpq₃
    · rcases hpq₁ with ⟨hp_eq, _⟩
      have : False := by simp [hp_eq] at hp
      exact this.elim
    · rcases hpq₂ with ⟨hp_eq, hq_eq⟩
      have : False := by simp [hq_eq] at hq_gt_one
      exact this.elim
    · rcases hpq₃ with ⟨_, _, _, hq_lt_top, _⟩
      exact ne_of_lt hq_lt_top
  have hq_toReal_pos : 0 < qr := by
    simpa [qr, hqr] using ENNReal.toReal_pos hq_ne_zero hq_ne_top
  have hq_toReal_ne_zero : qr ≠ 0 := ne_of_gt hq_toReal_pos
  have hq_toReal_nonneg : 0 ≤ qr := hq_toReal_pos.le
  have hp_inv_ne_top : p⁻¹ ≠ ∞ := by
    simpa using (ENNReal.inv_ne_top).2 hp_ne_zero
  have hq_inv_ne_top : q⁻¹ ≠ ∞ := by
    simpa using (ENNReal.inv_ne_top).2 hq_ne_zero
  have hpq_sum : 1 / p + 1 / q = 1 := by
    rcases hpq with hpq₁ | hpq₂ | hpq₃
    · rcases hpq₁ with ⟨hp_eq, _⟩
      have : False := by simp [hp_eq] at hp
      exact this.elim
    · rcases hpq₂ with ⟨hp_eq, hq_eq⟩
      have : False := by simp [hq_eq] at hq_gt_one
      exact this.elim
    · rcases hpq₃ with ⟨_, _, _, _, hpq_sum⟩
      exact hpq_sum
  have hpq_toReal : (1 / pr) + (1 / qr) = 1 := by
    have h_toReal := congrArg ENNReal.toReal hpq_sum
    have h_inv_pr : (p⁻¹).toReal = 1 / pr := by simp [pr, one_div]
    have h_inv_qr : (q⁻¹).toReal = 1 / qr := by simp [qr, one_div]
    have h_split := ENNReal.toReal_add hp_inv_ne_top hq_inv_ne_top
    simpa [one_div, h_split, h_inv_pr, h_inv_qr] using h_toReal
  have h_pow_identity : (pr - 1) * qr = pr := by
    have h_mul := congrArg (fun t : ℝ => t * (pr * qr)) hpq_toReal
    have h_pr_ne_zero : pr ≠ 0 := ne_of_gt hp_toReal_pos
    have h_qr_ne_zero : qr ≠ 0 := hq_toReal_ne_zero
    have h_left : (1 / pr + 1 / qr) * (pr * qr) = pr + qr := by
      have h₁ : pr⁻¹ * (pr * qr) = qr := by
        simp [h_pr_ne_zero]
      have h₂ : qr⁻¹ * (pr * qr) = pr := by
        simp [h_qr_ne_zero, mul_comm]
      calc
        (1 / pr + 1 / qr) * (pr * qr)
            = pr⁻¹ * (pr * qr) + qr⁻¹ * (pr * qr) := by
              simp [add_mul]
        _ = qr + pr := by simp [h₁, h₂]
        _ = pr + qr := by simp [add_comm]
    have h_mul' : pr + qr = pr * qr := by
      simpa [← h_left] using h_mul
    have h_diff := congrArg (fun t : ℝ => t - qr) h_mul'
    have h_fact : pr * qr - qr = (pr - 1) * qr := by ring
    simpa [h_fact, add_comm, add_left_comm, add_assoc] using h_diff.symm
  have h_qr_minus_one : qr - 1 = 1 / (pr - 1) := by
    have h_pr_sub_ne_zero : pr - 1 ≠ 0 := hp_toReal_sub_ne_zero
    have h_mul : (qr - 1) * (pr - 1) = 1 := by
      calc
        (qr - 1) * (pr - 1)
            = qr * (pr - 1) - 1 * (pr - 1) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (sub_mul qr (1 : ℝ) (pr - 1))
        _ = (pr - 1) * qr - (pr - 1) := by simp [mul_comm]
        _ = pr - (pr - 1) := by simp [h_pow_identity]
        _ = 1 := by
          simp [sub_eq_add_neg, add_comm]
    have h_one : (1 : ℝ) = (pr - 1) * (1 / (pr - 1)) := by
      simp [div_eq_mul_inv, h_pr_sub_ne_zero]
    have h_eq :
        (qr - 1) * (pr - 1) = (1 / (pr - 1)) * (pr - 1) := by
      simpa [mul_comm] using h_mul.trans h_one
    have h_cancel := mul_right_cancel₀ h_pr_sub_ne_zero h_eq
    simpa [div_eq_mul_inv] using h_cancel
  have h_qr_div_pr : qr / pr = 1 / (pr - 1) := by
    have h_pr_ne_zero : pr ≠ 0 := ne_of_gt hp_toReal_pos
    have h_pr_sub_ne_zero : pr - 1 ≠ 0 := hp_toReal_sub_ne_zero
    have h_div := congrArg (fun t : ℝ => t / pr) h_pow_identity
    have h_mul : (pr - 1) * (qr / pr) = 1 := by
      simpa [div_eq_mul_inv, h_pr_ne_zero, mul_comm, mul_left_comm, mul_assoc] using h_div
    have h_eq :
        (pr - 1) * (qr / pr) = (pr - 1) * (1 / (pr - 1)) := by
      have h_one : (1 : ℝ) = (pr - 1) * (1 / (pr - 1)) := by
        simp [div_eq_mul_inv, h_pr_sub_ne_zero]
      exact h_mul.trans h_one
    exact mul_left_cancel₀ h_pr_sub_ne_zero h_eq
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x => norm_nonneg _
  have hg_abs : ∀ x, |g x| = g x := fun x => abs_of_nonneg (hg_nonneg x)
  have hg_norm : ∀ x, ‖g x‖ = g x := by intro x; simp [Real.norm_eq_abs, hg_abs x]
  -- Truncate the fibrewise norm in order to build admissible dual test functions
  -- whose `L^q` norms will be uniformly bounded.
  let trunc : ℕ → α → ℝ := fun N x => min (g x) (N : ℝ)
  have htrunc_le : ∀ N x, trunc N x ≤ g x := by
    intro N x; exact min_le_left _ _
  have htrunc_bdd : ∀ N x, trunc N x ≤ N := by
    intro N x
    have hle : trunc N x ≤ (N : ℝ) := min_le_right _ _
    simpa using hle
  have htrunc_nonneg : ∀ N x, 0 ≤ trunc N x := by
    intro N x
    have hgx_nonneg : 0 ≤ g x := hg_nonneg x
    have hN_nonneg : 0 ≤ (N : ℝ) := by
      exact (Nat.cast_nonneg N : 0 ≤ (N : ℝ))
    exact le_min hgx_nonneg hN_nonneg
  -- The precise control on the norm of `trunc N x` will be used when forming
  -- the candidate dual elements based on powers of the truncations.
  have htrunc_norm : ∀ N x, ‖trunc N x‖ = trunc N x := by
    intro N x
    have hnonneg : 0 ≤ trunc N x := htrunc_nonneg N x
    simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have htrunc_meas : ∀ N : ℕ, AEStronglyMeasurable (trunc N) μ := by
    intro N
    have hcont : Continuous fun t : ℝ => min t (N : ℝ) :=
      continuous_id.min continuous_const
    exact hcont.comp_aestronglyMeasurable hg_meas
  have htrunc_int : ∀ N : ℕ, Integrable (trunc N) μ := by
    intro N
    refine
      hg_int.mono' (htrunc_meas N) ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    have hx_le : trunc N x ≤ g x := htrunc_le N x
    have hx_nonneg : 0 ≤ trunc N x := htrunc_nonneg N x
    have hg_nonneg' : 0 ≤ g x := hg_nonneg x
    have hle_norm : ‖trunc N x‖ ≤ g x := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hx_nonneg, abs_of_nonneg hg_nonneg'] using hx_le
    simpa using hle_norm
  have hpr_sub_nonneg : 0 ≤ pr - 1 := sub_nonneg.mpr hp_toReal_ge_one
  have htrunc_pow_bound :
      ∀ N x, (trunc N x) ^ pr ≤ (N : ℝ) ^ (pr - 1) * trunc N x := by
    intro N x
    have hx_nonneg : 0 ≤ trunc N x := htrunc_nonneg N x
    have hx_le_N : trunc N x ≤ (N : ℝ) := htrunc_bdd N x
    by_cases hzero : trunc N x = 0
    · have hpow_zero : (trunc N x) ^ pr = 0 := by
        have hpr_ne_zero : pr ≠ 0 := ne_of_gt hp_toReal_pos
        simpa [hzero] using Real.zero_rpow hpr_ne_zero
      have hright_zero : (N : ℝ) ^ (pr - 1) * trunc N x = 0 := by
        simp [hzero]
      simp [hpow_zero, hright_zero]
    · have hx_pos : 0 < trunc N x :=
        lt_of_le_of_ne hx_nonneg (by simpa [eq_comm] using hzero)
      have hx_pow_le : (trunc N x) ^ (pr - 1) ≤ (N : ℝ) ^ (pr - 1) :=
        Real.rpow_le_rpow hx_nonneg hx_le_N hpr_sub_nonneg
      have hsum : (pr - 1) + 1 = pr := by ring
      have hpow_eq : (trunc N x) ^ pr = (trunc N x) ^ (pr - 1) * trunc N x := by
        have := Real.rpow_add hx_pos (pr - 1) 1
        simpa [hsum, Real.rpow_one, mul_comm, mul_left_comm, mul_assoc]
          using this
      have hx_nonneg' : 0 ≤ trunc N x := hx_nonneg
      have hmul_le := mul_le_mul_of_nonneg_right hx_pow_le hx_nonneg'
      simpa [hpow_eq]
        using hmul_le
  have htrunc_pow_integrable :
      ∀ N : ℕ, Integrable (fun x => (trunc N x) ^ pr) μ := by
    intro N
    set C : ℝ := (N : ℝ) ^ (pr - 1) with hC
    have hC_nonneg : 0 ≤ C := by
      simpa [hC] using Real.rpow_nonneg (show 0 ≤ (N : ℝ) from Nat.cast_nonneg _) (pr - 1)
    have h_major_int : Integrable (fun x => C * trunc N x) μ :=
      (htrunc_int N).const_mul C
    have h_pow_meas_norm :
        AEStronglyMeasurable (fun x => ‖trunc N x‖ ^ pr) μ := by
      have h_cont : Continuous fun t : ℝ => |t| ^ pr :=
        (continuous_abs).rpow_const
          (by intro _; exact Or.inr (le_of_lt hp_toReal_pos))
      have := h_cont.comp_aestronglyMeasurable ((htrunc_meas N).norm)
      simpa [Real.norm_eq_abs] using this
    have h_pow_meas :
        AEStronglyMeasurable (fun x => (trunc N x) ^ pr) μ := by
      refine h_pow_meas_norm.congr ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      have hx_nonneg : 0 ≤ trunc N x := htrunc_nonneg N x
      simp [Real.norm_eq_abs, abs_of_nonneg hx_nonneg]
    have h_bound :
        ∀ᵐ x ∂μ, ‖(trunc N x) ^ pr‖ ≤ C * trunc N x := by
      refine Filter.Eventually.of_forall ?_
      intro x
      have hx_nonneg : 0 ≤ trunc N x := htrunc_nonneg N x
      have hpow_le := htrunc_pow_bound N x
      have hnorm_pow : ‖(trunc N x) ^ pr‖ = (trunc N x) ^ pr := by
        have := Real.rpow_nonneg hx_nonneg pr
        simp [Real.norm_eq_abs, abs_of_nonneg this]
      simpa [hnorm_pow] using hpow_le
    have := Integrable.mono' h_major_int h_pow_meas h_bound
    simpa
  have htrunc_lintegral_lt_top :
      ∀ N : ℕ, (∫⁻ x, ‖trunc N x‖ₑ ^ pr ∂μ) < ∞ := by
    intro N
    have h_int := (htrunc_pow_integrable N).hasFiniteIntegral
    have h_abs_eq :
        ∀ x, ‖(trunc N x) ^ pr‖ₑ = ‖trunc N x‖ₑ ^ pr := by
      intro x
      have hx_nonneg : 0 ≤ trunc N x := htrunc_nonneg N x
      have hpow_nonneg : 0 ≤ (trunc N x) ^ pr := Real.rpow_nonneg hx_nonneg _
      have hnorm : ‖trunc N x‖ = trunc N x := by
        simp [Real.norm_eq_abs, abs_of_nonneg hx_nonneg]
      simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg hx_nonneg,
        abs_of_nonneg hpow_nonneg, ENNReal.ofReal_rpow_of_nonneg hx_nonneg hp_toReal_pos.le]
    simpa [HasFiniteIntegral, h_abs_eq]
      using h_int
  have htrunc_mem : ∀ N : ℕ, MemLp (trunc N) p μ := by
    intro N
    refine ⟨htrunc_meas N, ?_⟩
    exact
      (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (μ := μ) (p := p) (f := trunc N) hp_ne_zero hp_ne_top).2
          (htrunc_lintegral_lt_top N)
  have hq_gt_one' : 1 ≤ q := hq_gt_one.le
  have h_trunc_pairing_bound :
      ∀ N φ,
        MemLp φ q μ →
        (eLpNorm φ q μ).toReal ≤ 1 →
        Integrable (fun x => trunc N x * φ x) μ →
        |∫ x, trunc N x * φ x ∂μ| ≤ B := by
    intro N φ hφ_mem hφ_norm hφ_int
    -- Rescale the test function so that the pairing against `g` coincides with the
    -- pairing against the truncated function.
    let coeff : α → ℝ := fun x => min (1 : ℝ) ((N : ℝ) / g x)
    let φ' : α → ℝ := fun x => coeff x * φ x
    have hcoeff_aemeas : AEMeasurable coeff μ := by
      have h_one : AEMeasurable (fun _ : α => (1 : ℝ)) μ := aemeasurable_const
      have h_div : AEMeasurable (fun x : α => (N : ℝ) / g x) μ :=
        (aemeasurable_const : AEMeasurable (fun _ : α => (N : ℝ)) μ).div
          (hg_meas.aemeasurable)
      simpa [coeff] using h_one.min h_div
    have hcoeff_meas : AEStronglyMeasurable coeff μ := hcoeff_aemeas.aestronglyMeasurable
    have hφ_meas : AEStronglyMeasurable φ μ := hφ_mem.aestronglyMeasurable
    have hφ'_meas : AEStronglyMeasurable φ' μ :=
      hcoeff_meas.mul hφ_meas
    have hcoeff_nonneg : ∀ x, 0 ≤ coeff x := by
      intro x
      by_cases hle : (N : ℝ) / g x ≤ 1
      · have hdiv_nonneg : 0 ≤ (N : ℝ) / g x :=
          div_nonneg (show 0 ≤ (N : ℝ) from by exact_mod_cast (Nat.zero_le N))
            (hg_nonneg x)
        simp [coeff, hle, hdiv_nonneg]
      · have hge : 1 ≤ (N : ℝ) / g x := le_of_not_ge hle
        simp [coeff, hge]
    have hcoeff_le_one : ∀ x, coeff x ≤ 1 := by
      intro x; exact min_le_left _ _
    have hcoeff_abs_le_one : ∀ x, |coeff x| ≤ 1 := by
      intro x
      have hnonneg := hcoeff_nonneg x
      have := hcoeff_le_one x
      simpa [abs_of_nonneg hnonneg]
    have hφ'_le : ∀ x, ‖φ' x‖ ≤ ‖φ x‖ := by
      intro x
      have hnonneg := hcoeff_nonneg x
      have hbound := hcoeff_abs_le_one x
      have hprod :=
        mul_le_mul_of_nonneg_right hbound (abs_nonneg (φ x))
      have : |coeff x| * |φ x| ≤ |φ x| := by
        simpa using hprod
      simpa [φ', Real.norm_eq_abs, abs_mul] using this
    have hφ'_mem : MemLp φ' q μ :=
      MemLp.mono hφ_mem hφ'_meas
        (Filter.Eventually.of_forall hφ'_le)
    have h_eLp_le : eLpNorm φ' q μ ≤ eLpNorm φ q μ :=
      eLpNorm_mono fun x => hφ'_le x
    have hφ'_norm : (eLpNorm φ' q μ).toReal ≤ 1 := by
      have h_lt_top : eLpNorm φ q μ < ∞ := hφ_mem.2
      have hφ'_lt_top : eLpNorm φ' q μ < ∞ := hφ'_mem.2
      have h_toReal_le :=
        (ENNReal.toReal_le_toReal hφ'_lt_top.ne h_lt_top.ne).mpr h_eLp_le
      exact h_toReal_le.trans hφ_norm
    have hcoeff_mul : ∀ x, g x * coeff x = trunc N x := by
      intro x
      dsimp [coeff, trunc]
      by_cases hg0 : g x = 0
      · simp [hg0]
      · have hg_pos : 0 < g x := lt_of_le_of_ne (hg_nonneg x)
          (by simpa [eq_comm] using hg0)
        by_cases hle : g x ≤ (N : ℝ)
        · have hmin : min (1 : ℝ) ((N : ℝ) / g x) = 1 := by
            have hge : 1 ≤ (N : ℝ) / g x := (one_le_div hg_pos).2 hle
            exact min_eq_left hge
          have htrunc : min (g x) (N : ℝ) = g x := min_eq_left hle
          simp [hmin, htrunc]
        · have hgt : (N : ℝ) < g x := lt_of_not_ge hle
          have hle' : (N : ℝ) / g x ≤ 1 := (div_le_one hg_pos).2 hgt.le
          have hmin : min (1 : ℝ) ((N : ℝ) / g x) = (N : ℝ) / g x :=
            min_eq_right hle'
          have htrunc : min (g x) (N : ℝ) = (N : ℝ) :=
            min_eq_right hgt.le
          have hg_ne : g x ≠ 0 := hg0
          have hcalc : g x * ((N : ℝ) / g x) = (N : ℝ) := by
            calc
              g x * ((N : ℝ) / g x)
                  = g x * ((N : ℝ) * (g x)⁻¹) := by simp [div_eq_mul_inv]
              _ = (g x * (g x)⁻¹) * (N : ℝ) := by ac_rfl
              _ = 1 * (N : ℝ) := by simp [hg_ne]
              _ = (N : ℝ) := by simp
          simpa [hmin, htrunc] using hcalc
    have hφ'_integrand_eq :
        (fun x => g x * φ' x) = fun x => trunc N x * φ x := by
      funext x
      simp [φ', mul_comm, mul_left_comm, hcoeff_mul]
    have hφ'_integrable : Integrable (fun x => g x * φ' x) μ := by
      simpa [hφ'_integrand_eq] using hφ_int
    have h_integral_eq :
        ∫ x, g x * φ' x ∂μ = ∫ x, trunc N x * φ x ∂μ := by
      simp [hφ'_integrand_eq]
    have h_bound :=
      h_pairing_bound (φ := φ') hφ'_mem hφ'_norm hφ'_integrable
    have h_abs_eq : |∫ x, trunc N x * φ x ∂μ| = |∫ x, g x * φ' x ∂μ| := by
      simp [h_integral_eq]
    simpa [φ', h_abs_eq] using h_bound
  have h_trunc_norm_le : ∀ N : ℕ,
      (eLpNorm (trunc N) p μ).toReal ≤ B := by
    intro N
    refine
      lp_duality_norm_le_of_pairing_bound (μ := μ)
        (p := p) (q := q) hp hq_gt_one hpq (f := trunc N) (htrunc_mem N) ?_
    intro φ hφ_mem hφ_norm hφ_int
    simpa using h_trunc_pairing_bound N φ hφ_mem hφ_norm hφ_int
  -- Having obtained uniform bounds on the `L^p` norms of the truncations, it remains
  -- to pass to the limit and deduce the desired finiteness for `g`.
  have h_trunc_eLp_le :
      ∀ N : ℕ, eLpNorm (trunc N) p μ ≤ ENNReal.ofReal B := by
    intro N
    have h_fin : eLpNorm (trunc N) p μ ≠ ∞ := (htrunc_mem N).2.ne
    have hB_fin : ENNReal.ofReal B ≠ ∞ := by simp
    refine (ENNReal.toReal_le_toReal h_fin hB_fin).1 ?_
    simpa [ENNReal.toReal_ofReal hB_nonneg] using h_trunc_norm_le N
  have h_goal : eLpNorm g p μ ≤ ENNReal.ofReal B := by
    -- Choose a measurable non-negative representative of `g`.
    set gTilde := hg_meas.aemeasurable.mk g with hgTilde_def
    set g0 : α → ℝ := fun x => max (gTilde x) 0 with hg0_def
    have hg_ae' : g =ᵐ[μ] gTilde := hg_meas.aemeasurable.ae_eq_mk
    have hg0_ae : g =ᵐ[μ] g0 :=
      hg_ae'.mono fun x hx => by
        have hx_nonneg : 0 ≤ g x := hg_nonneg x
        have hx_nonneg' : 0 ≤ gTilde x := by simpa [hx] using hx_nonneg
        have hmax : max (g x) 0 = g x := by simpa [max_eq_left] using hx_nonneg
        simp [g0, hx, hx_nonneg']
    have h_eLp_congr : eLpNorm g p μ = eLpNorm g0 p μ :=
      eLpNorm_congr_ae hg0_ae
    have hgTilde_meas : Measurable gTilde := hg_meas.aemeasurable.measurable_mk
    have hg0_meas : Measurable g0 := hgTilde_meas.max measurable_const
    have hg0_nonneg : ∀ x, 0 ≤ g0 x := by
      intro x; exact le_max_right _ _
    -- Truncate the measurable representative and compare with the original truncations.
    let trunc0 : ℕ → α → ℝ := fun N x => min (g0 x) (N : ℝ)
    have h_trunc_ae : ∀ N, trunc N =ᵐ[μ] trunc0 N := by
      intro N
      exact hg0_ae.mono (by intro x hx; simp [trunc, trunc0, hx])
    have h_trunc0_meas : ∀ N, Measurable (trunc0 N) := by
      intro N; exact (hg0_meas.min measurable_const)
    have h_trunc0_nonneg : ∀ N x, 0 ≤ trunc0 N x := by
      intro N x; dsimp [trunc0]
      have hN_nonneg : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
      exact le_min (hg0_nonneg x) hN_nonneg
    have h_trunc0_le : ∀ N x, trunc0 N x ≤ g0 x := by
      intro N x; dsimp [trunc0]; exact min_le_left _ _
    have h_trunc0_eLp_le : ∀ N : ℕ,
        eLpNorm (trunc0 N) p μ ≤ ENNReal.ofReal B := by
      intro N
      have h_bound := h_trunc_eLp_le N
      have h_eq :
          eLpNorm (trunc N) p μ = eLpNorm (trunc0 N) p μ :=
        eLpNorm_congr_ae (μ := μ) (p := p)
          (f := trunc N) (g := trunc0 N) (h_trunc_ae N)
      simpa [h_eq] using h_bound
    -- Work with the `L^p` densities of the truncations.
    set F0 : ℕ → α → ℝ≥0∞ := fun N x => ‖trunc0 N x‖ₑ ^ pr
      with hF0_def
    have hF0_meas : ∀ N, Measurable (F0 N) := by
      intro N
      have h_abs : Measurable fun x => |trunc0 N x| :=
        ((_root_.continuous_abs : Continuous fun t : ℝ => |t|).measurable.comp
          (h_trunc0_meas N))
      have h_enorm : Measurable fun x => ‖trunc0 N x‖ₑ := by
        simpa [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs, Function.comp_def] using
          (ENNReal.measurable_ofReal.comp h_abs)
      have h_pow :
          Measurable fun x => ‖trunc0 N x‖ₑ ^ pr :=
        (ENNReal.continuous_rpow_const (y := pr)).measurable.comp h_enorm
      simpa [F0, hF0_def] using h_pow
    have hF0_mono : Monotone F0 := by
      intro m n hmn x
      have h_trunc_le : trunc0 m x ≤ trunc0 n x := by
        dsimp [trunc0]
        exact min_le_min le_rfl (by exact_mod_cast hmn)
      have h_nonneg_m : 0 ≤ trunc0 m x := h_trunc0_nonneg m x
      have h_nonneg_n : 0 ≤ trunc0 n x := h_trunc0_nonneg n x
      have : ENNReal.ofReal (trunc0 m x) ≤ ENNReal.ofReal (trunc0 n x) :=
        ENNReal.ofReal_le_ofReal h_trunc_le
      have h_le_enorm : ‖trunc0 m x‖ₑ ≤ ‖trunc0 n x‖ₑ := by
        simpa [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs,
          abs_of_nonneg h_nonneg_m, abs_of_nonneg h_nonneg_n]
          using this
      exact ENNReal.rpow_le_rpow h_le_enorm hp_toReal_pos.le
    have hF0_iSup :
        (fun x => ‖g0 x‖ₑ ^ pr) = fun x => ⨆ N, F0 N x := by
      funext x
      have h_le : ∀ N, F0 N x ≤ ‖g0 x‖ₑ ^ pr := by
        intro N
        have h_trunc_le' : trunc0 N x ≤ g0 x := h_trunc0_le N x
        have h_nonneg_N : 0 ≤ trunc0 N x := h_trunc0_nonneg N x
        have h_nonneg_g0 : 0 ≤ g0 x := hg0_nonneg x
        have : ENNReal.ofReal (trunc0 N x) ≤ ENNReal.ofReal (g0 x) :=
          ENNReal.ofReal_le_ofReal h_trunc_le'
        have h_base : ‖trunc0 N x‖ₑ ≤ ‖g0 x‖ₑ := by
          simpa [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs,
            abs_of_nonneg h_nonneg_N, abs_of_nonneg h_nonneg_g0]
            using this
        exact ENNReal.rpow_le_rpow h_base hp_toReal_pos.le
      apply le_antisymm
      · obtain ⟨N, hN⟩ := exists_nat_ge (g0 x)
        have h_min : min (g0 x) (N : ℝ) = g0 x := by
          exact min_eq_left (by exact_mod_cast hN)
        have h_trunc_eq : trunc0 N x = g0 x := by simp [trunc0, h_min]
        refine le_iSup_of_le N ?_
        have h_nonneg : 0 ≤ g0 x := hg0_nonneg x
        simp [F0, h_trunc_eq, Real.enorm_eq_ofReal_abs, abs_of_nonneg h_nonneg]
      · exact iSup_le h_le
    have h_lintegral_eq :
        ∫⁻ x, ‖g0 x‖ₑ ^ pr ∂μ = ⨆ N, ∫⁻ x, F0 N x ∂μ := by
      simpa [hF0_iSup] using
        MeasureTheory.lintegral_iSup (μ := μ) hF0_meas hF0_mono
    have h_int_eq :
        ∀ N : ℕ, ∫⁻ x, F0 N x ∂μ = (eLpNorm (trunc0 N) p μ) ^ pr := by
      intro N
      set A := ∫⁻ x, ‖trunc0 N x‖ₑ ^ pr ∂μ
      have h_eLp :=
        MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
          (μ := μ) (p := p) (f := trunc0 N)
          (hp_ne_zero := hp_ne_zero) (hp_ne_top := hp_ne_top)
      have h_pr_ne_zero : pr ≠ 0 := ne_of_gt hp_toReal_pos
      have h_mul : pr⁻¹ * pr = 1 := by
        simp [h_pr_ne_zero]
      have hA : eLpNorm (trunc0 N) p μ = A ^ (1 / pr) := by
        simpa [F0, hF0_def, A] using h_eLp
      have hA_inv : eLpNorm (trunc0 N) p μ = A ^ pr⁻¹ := by
        simpa [one_div] using hA
      have h_left : (A ^ pr⁻¹) ^ pr = A := by
        have h_rpow := (ENNReal.rpow_mul A pr⁻¹ pr).symm
        simpa [h_mul] using h_rpow
      have hA_pow : (eLpNorm (trunc0 N) p μ) ^ pr = A := by
        simpa [hA_inv] using h_left
      simpa [F0, hF0_def, A] using hA_pow.symm
    have h_int_le :
        ∫⁻ x, ‖g0 x‖ₑ ^ pr ∂μ ≤ (ENNReal.ofReal B) ^ pr := by
      calc
        ∫⁻ x, ‖g0 x‖ₑ ^ pr ∂μ
            = ⨆ N, ∫⁻ x, F0 N x ∂μ := h_lintegral_eq
        _ ≤ (ENNReal.ofReal B) ^ pr :=
          iSup_le fun N => by
            have h_le := ENNReal.rpow_le_rpow (h_trunc0_eLp_le N) hp_toReal_pos.le
            simpa [h_int_eq N] using h_le
    have h_bound_lt_top : (ENNReal.ofReal B) ^ pr < ∞ := by
      have : (ENNReal.ofReal B) < ∞ := by simp
      exact ENNReal.rpow_lt_top_of_nonneg hp_toReal_pos.le this.ne
    have h_int_lt_top :
        (∫⁻ x, ‖g0 x‖ₑ ^ pr ∂μ) < ∞ := lt_of_le_of_lt h_int_le h_bound_lt_top
    have h_eLp_repr :=
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm
        (μ := μ) (p := p) (f := g0)
        (hp_ne_zero := hp_ne_zero) (hp_ne_top := hp_ne_top)
    have h_eLp_value : eLpNorm g0 p μ =
        (∫⁻ x, ‖g0 x‖ₑ ^ pr ∂μ) ^ pr⁻¹ := by
      simpa [F0, hF0_def, one_div] using h_eLp_repr
    have h_inv_nonneg : 0 ≤ pr⁻¹ := by
      have h_pos : 0 < pr⁻¹ := by
        simpa [one_div] using inv_pos.mpr hp_toReal_pos
      exact h_pos.le
    have h_pow_le :=
      ENNReal.rpow_le_rpow h_int_le h_inv_nonneg
    have h_pow_eq :
        ((ENNReal.ofReal B) ^ pr) ^ pr⁻¹ = ENNReal.ofReal B := by
      have h_pr_ne_zero : pr ≠ 0 := ne_of_gt hp_toReal_pos
      have h_mul : pr * pr⁻¹ = 1 := by
        simp [h_pr_ne_zero]
      have h_rpow :=
        (ENNReal.rpow_mul (ENNReal.ofReal B) pr pr⁻¹).symm
      have h_rpow' :
          ((ENNReal.ofReal B) ^ pr) ^ pr⁻¹
            = (ENNReal.ofReal B) ^ 1 := by
        simpa [h_mul] using h_rpow
      simpa using h_rpow'
    have h_goal0 : eLpNorm g0 p μ ≤ ENNReal.ofReal B := by
      have h_base : (∫⁻ x, ‖g0 x‖ₑ ^ pr ∂μ) ^ pr⁻¹
          ≤ ((ENNReal.ofReal B) ^ pr) ^ pr⁻¹ := h_pow_le
      simpa [h_eLp_value, h_pow_eq] using h_base
    simpa [h_eLp_congr] using h_goal0
  have h_fin : eLpNorm g p μ < ∞ := lt_of_le_of_lt h_goal (by simp)
  simpa [g] using h_fin
end Newton
