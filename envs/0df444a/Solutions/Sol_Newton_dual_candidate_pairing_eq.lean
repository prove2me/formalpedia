-- Prove2me | solution 1 for Newton.dual_candidate_pairing_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:39:35.926721+00:00
-- url     : https://prove2.me/submissions/65e17fcb-e17c-4e33-8a07-5185e0c6ef3d

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality
import Theorems.Thm_Newton_lp_duality_pairing
import Theorems.Thm_Newton_dual_candidate_memLp

set_option autoImplicit false
open scoped ENNReal
open MeasureTheory Real Topology
open Newton
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Newton
theorem _root_.solution
    (p q : ℝ≥0∞) (hp : 1 < p) (hq : 1 < q)
    (hpq : IsConjugateExponent p q)
    {f : α → ℝ}
    (hf : MemLp f p μ)
    (hf_norm : (eLpNorm f p μ).toReal = 1) :
    (∫ x, f x *
        (Real.sign (f x) * |f x| ^ (p.toReal - 1)) ∂μ)
      =
        (eLpNorm f p μ).toReal *
          (eLpNorm (fun x => Real.sign (f x) * |f x| ^ (p.toReal - 1)) q μ).toReal ∧
      (eLpNorm (fun x => Real.sign (f x) * |f x| ^ (p.toReal - 1)) q μ).toReal = 1 := by
  set pr : ℝ := p.toReal with hpr
  set g : α → ℝ := fun x => Real.sign (f x) * |f x| ^ (pr - 1) with hg_def
  have hp_ne_zero : p ≠ 0 :=
    by
      have : (0 : ℝ≥0∞) < 1 := by simp
      exact ne_of_gt (lt_trans this hp)
  have hp_ne_top : p ≠ ∞ := by
    rcases hpq with h | h | h
    · rcases h with ⟨hp_eq, _⟩
      have : False := by simp [hp_eq] at hp
      exact this.elim
    · rcases h with ⟨hp_eq, hq_eq⟩
      have : False := by simp [hq_eq] at hq
      exact this.elim
    · rcases h with ⟨_, hp_lt_top, _, _, _⟩
      exact ne_of_lt hp_lt_top
  have hpq_sum : 1 / p + 1 / q = 1 := by
    obtain ⟨hp_eq, _⟩ | h := hpq
    · have : False := by simp [hp_eq] at hp
      exact (False.elim this : 1 / p + 1 / q = 1)
    · obtain ⟨hp_eq, hq_eq⟩ | h := h
      · have : False := by simp [hq_eq] at hq
        exact (False.elim this : 1 / p + 1 / q = 1)
      · rcases h with ⟨_, _, _, _, hpq_sum⟩
        exact hpq_sum
  have p_inv_add : p⁻¹ + q⁻¹ = 1 := by simpa [one_div] using hpq_sum
  haveI : ENNReal.HolderTriple p q 1 :=
    ⟨by simp [p_inv_add, inv_one]⟩
  have g_mem : MemLp g q μ := by
    simpa [g, hg_def, pr, hpr]
      using dual_candidate_memLp (μ := μ) (p := p) (q := q) hp hq hpq hf
  have h_integrable : Integrable (fun x => f x * g x) μ :=
    MeasureTheory.MemLp.integrable_mul (p := p) (q := q) (μ := μ)
      (f := fun x => f x) (g := g) hf g_mem
  have h_holder :=
    lp_duality_pairing (μ := μ) (p := p) (q := q) hp hq hpq hf g_mem
  -- The equality statement should refine Hölder's inequality using the unit-norm hypothesis.
  -- Further analytic work is required to upgrade the inequality `h_holder` to an equality.
  -- The key ingredients prepared above: `g_mem`, `h_integrable`, and `hf_norm`.
  have hq_ne_zero : q ≠ 0 :=
    by
      have hq_pos : (0 : ℝ≥0∞) < q := lt_trans (by simp) hq
      exact ne_of_gt hq_pos
  have hq_ne_top : q ≠ ∞ := by
    rcases hpq with hpq₁ | hpq₂ | hpq₃
    · rcases hpq₁ with ⟨hp_eq, _⟩
      have : False := by simp [hp_eq] at hp
      exact this.elim
    · rcases hpq₂ with ⟨hp_eq, hq_eq⟩
      have : False := by simp [hq_eq] at hq
      exact this.elim
    · rcases hpq₃ with ⟨_, _, _, hq_lt_top, _⟩
      exact ne_of_lt hq_lt_top
  set qr : ℝ := q.toReal with hqr
  have hpr_pos : 0 < pr := by
    simpa [pr] using ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have hpr_ne_zero : pr ≠ 0 := ne_of_gt hpr_pos
  have hpr_gt_one : 1 < pr :=
    by
      have :=
        (ENNReal.toReal_lt_toReal (a := (1 : ℝ≥0∞)) (b := p) (by simp) hp_ne_top).2 hp
      simpa [pr, hpr] using this
  have hpr_ge_one : 1 ≤ pr := hpr_gt_one.le
  have hpr_ne_one : pr ≠ 1 := by
    intro h_eq
    have : 1 < 1 := by simp [h_eq] at hpr_gt_one
    exact lt_irrefl _ this
  have hpr_sub_ne_zero : pr - 1 ≠ 0 := by
    have : pr ≠ 1 := hpr_ne_one
    simpa [sub_eq_zero] using this
  have hqr_pos : 0 < qr := by
    simpa [qr, hqr] using ENNReal.toReal_pos hq_ne_zero hq_ne_top
  have hqr_ne_zero : qr ≠ 0 := ne_of_gt hqr_pos
  have hqr_nonneg : 0 ≤ qr := hqr_pos.le
  have hpq_sum : 1 / p + 1 / q = 1 := by
    obtain ⟨hp_eq, _⟩ | h := hpq
    · have : False := by simp [hp_eq] at hp
      exact (False.elim this : 1 / p + 1 / q = 1)
    · obtain ⟨hp_eq, hq_eq⟩ | h := h
      · have : False := by simp [hq_eq] at hq
        exact (False.elim this : 1 / p + 1 / q = 1)
      · rcases h with ⟨_, _, _, _, hpq_sum⟩
        exact hpq_sum
  have hp_inv_ne_top : p⁻¹ ≠ ∞ := by
    simpa using (ENNReal.inv_ne_top).2 hp_ne_zero
  have hq_inv_ne_top : q⁻¹ ≠ ∞ := by
    simpa using (ENNReal.inv_ne_top).2 hq_ne_zero
  have h_inv_toReal : (1 / pr) + (1 / qr) = 1 := by
    have h_toReal := congrArg ENNReal.toReal hpq_sum
    have h_inv_pr : (p⁻¹).toReal = 1 / pr := by simp [pr, one_div]
    have h_inv_qr : (q⁻¹).toReal = 1 / qr := by simp [qr, one_div]
    have h_split := ENNReal.toReal_add hp_inv_ne_top hq_inv_ne_top
    simpa [one_div, h_split, h_inv_pr, h_inv_qr] using h_toReal
  have h_pow_identity : (pr - 1) * qr = pr := by
    have h_mul_pr := congrArg (fun t : ℝ => pr * t) h_inv_toReal
    have h_simplify : (1 : ℝ) + pr / qr = pr := by
      simpa [mul_add, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, hpr_ne_zero]
        using h_mul_pr
    have h_pr_div_qr : pr / qr = pr - 1 := (eq_sub_iff_add_eq').2 h_simplify
    have := congrArg (fun t : ℝ => t * qr) h_pr_div_qr
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, hqr_ne_zero] using this.symm
  -- pointwise description of the Hölder extremiser product
  have h_fg_pointwise : ∀ x, f x * g x = |f x| ^ pr := by
    intro x
    by_cases hfx : f x = 0
    · have hsign : Real.sign (f x) = 0 := by simp [hfx]
      simp [g, hfx, Real.zero_rpow hpr_sub_ne_zero, Real.zero_rpow hpr_ne_zero]
    · have hsign_mul_self : Real.sign (f x) * f x = |f x| := by
        obtain hx | hx | hx := lt_trichotomy (f x) 0
        · simp [Real.sign_of_neg hx, abs_of_neg hx, mul_comm]
        · exact (hfx hx).elim
        · simp [Real.sign_of_pos hx, abs_of_pos hx, mul_comm]
      have h_abs_pos : 0 < |f x| := abs_pos.mpr hfx
      have hsum : 1 + (pr - 1) = pr := by ring
      calc
        f x * g x
            = f x * (Real.sign (f x) * |f x| ^ (pr - 1)) := by simp [g]
        _ = (Real.sign (f x) * f x) * |f x| ^ (pr - 1) := by
              ring_nf
        _ = |f x| * |f x| ^ (pr - 1) := by simp [hsign_mul_self]
        _ = |f x| ^ (1 : ℝ) * |f x| ^ (pr - 1) := by simp [Real.rpow_one]
        _ = |f x| ^ pr := by
              have h_add := (Real.rpow_add h_abs_pos 1 (pr - 1)).symm
              simpa [hsum] using h_add
  have h_fg_eq :
      (fun x => f x * g x) =ᵐ[μ] fun x => |f x| ^ pr :=
    Filter.Eventually.of_forall h_fg_pointwise
  have h_abs_pow_integrable : Integrable (fun x => |f x| ^ pr) μ :=
    h_integrable.congr h_fg_eq
  have h_integral_eq :
      (∫ x, f x * g x ∂μ) = ∫ x, |f x| ^ pr ∂μ :=
    integral_congr_ae h_fg_eq
  set A : ℝ := ∫ x, |f x| ^ pr ∂μ with hA
  have hA_nonneg : 0 ≤ A :=
    integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
  -- express the `L^p` norm in terms of `A`
  have h_eLpNorm_f :
      eLpNorm f p μ = ENNReal.ofReal (A ^ pr⁻¹) := by
    have :=
      MemLp.eLpNorm_eq_integral_rpow_norm (μ := μ) (f := f) hp_ne_zero hp_ne_top hf
    simpa [A, pr, hpr, Real.norm_eq_abs] using this
  have h_toReal_f : (eLpNorm f p μ).toReal = A ^ pr⁻¹ := by
    have h := congrArg ENNReal.toReal h_eLpNorm_f
    have hA_pow_nonneg : 0 ≤ A ^ pr⁻¹ := Real.rpow_nonneg hA_nonneg _
    simpa [hA_pow_nonneg] using h
  have hA_pow_eq_one : A ^ pr⁻¹ = 1 := by simpa [h_toReal_f] using hf_norm
  have hmul : pr⁻¹ * pr = 1 := by
    field_simp [hpr_ne_zero]
  have hA_eq_one : A = 1 := by
    have hpow := Real.rpow_mul hA_nonneg pr⁻¹ pr
    have hpow' : A = (A ^ pr⁻¹) ^ pr := by simpa [hmul, Real.rpow_one] using hpow
    calc
      A = (A ^ pr⁻¹) ^ pr := hpow'
      _ = 1 ^ pr := by simp [hA_pow_eq_one]
      _ = 1 := by simp
  -- describe the `L^q` norm of the dual candidate in terms of `A`
  have h_norm_abs : ∀ x, ‖g x‖ = |f x| ^ (pr - 1) := by
    intro x
    by_cases hfx : f x = 0
    · have hf_abs : |f x| = 0 := by simp [hfx]
      simp [g, hfx, Real.zero_rpow hpr_sub_ne_zero]
    · have hsign_abs : |Real.sign (f x)| = 1 := by
        rcases Real.sign_apply_eq_of_ne_zero (f x) hfx with hsign | hsign
        · simp [hsign]
        · simp [hsign]
      set t : ℝ := |f x| ^ (pr - 1) with ht
      have ht_nonneg : 0 ≤ t := by simpa [ht] using Real.rpow_nonneg (abs_nonneg _) _
      have ht_abs : |t| = t := abs_of_nonneg ht_nonneg
      have hcalc_abs : |g x| = |Real.sign (f x)| * |t| := by
        simp [g, ht, abs_mul]
      have hcalc_abs' : |g x| = |Real.sign (f x)| * t := by
        simpa [ht_abs] using hcalc_abs
      have hcalc : ‖g x‖ = |Real.sign (f x)| * t := by
        simpa [Real.norm_eq_abs] using hcalc_abs'
      simpa [hsign_abs, ht] using hcalc
  have h_g_pow_eq : ∀ x, ‖g x‖ ^ qr = |f x| ^ pr := by
    intro x
    have hx_norm : ‖g x‖ = |f x| ^ (pr - 1) := h_norm_abs x
    have hpow := (Real.rpow_mul (abs_nonneg (f x)) (pr - 1) qr).symm
    simpa [hx_norm, h_pow_identity] using hpow
  have h_g_pow_fun :
      (fun x => ‖g x‖ ^ qr) = fun x => |f x| ^ pr := funext h_g_pow_eq
  have h_abs_ae : (fun x => |g x| ^ qr) =ᵐ[μ] fun x => |f x| ^ pr :=
    Filter.Eventually.of_forall fun x =>
      by simpa [Real.norm_eq_abs] using h_g_pow_eq x
  have h_abs_integral_eq : ∫ x, |g x| ^ qr ∂μ = ∫ x, |f x| ^ pr ∂μ :=
    integral_congr_ae h_abs_ae
  set B : ℝ := ∫ x, ‖g x‖ ^ qr ∂μ with hB
  have hB_eq_A : B = A := by
    calc
      B = ∫ x, |g x| ^ qr ∂μ := by simp [B, Real.norm_eq_abs]
      _ = ∫ x, |f x| ^ pr ∂μ := h_abs_integral_eq
      _ = A := by simp [A]
  have hB_nonneg : 0 ≤ B :=
    calc
      0 ≤ ∫ x, |g x| ^ qr ∂μ :=
        integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
      _ = B := by simp [B, Real.norm_eq_abs]
  have h_eLpNorm_g :
      eLpNorm g q μ = ENNReal.ofReal (B ^ qr⁻¹) := by
    have :=
      MemLp.eLpNorm_eq_integral_rpow_norm (μ := μ) (f := g) hq_ne_zero hq_ne_top g_mem
    simpa [B, qr, hqr, Real.norm_eq_abs] using this
  have h_toReal_g : (eLpNorm g q μ).toReal = B ^ qr⁻¹ := by
    have h := congrArg ENNReal.toReal h_eLpNorm_g
    have hB_pow_nonneg : 0 ≤ B ^ qr⁻¹ := Real.rpow_nonneg hB_nonneg _
    simpa [hB_pow_nonneg] using h
  have h_integral_one : (∫ x, f x * g x ∂μ) = 1 := by
    simp [h_integral_eq, A, hA_eq_one]
  have h_norm_g_one : (eLpNorm g q μ).toReal = 1 := by
    simp [h_toReal_g, hB_eq_A, hA_eq_one]
  have h_norm_f_one : (eLpNorm f p μ).toReal = 1 := hf_norm
  refine ⟨?_, h_norm_g_one⟩
  simpa [h_integral_one, h_norm_f_one, h_norm_g_one]
end Newton
