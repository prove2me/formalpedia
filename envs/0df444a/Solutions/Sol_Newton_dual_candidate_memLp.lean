-- Prove2me | solution 1 for Newton.dual_candidate_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:07:21.257208+00:00
-- url     : https://prove2.me/submissions/48c4bebf-453c-46b5-bd07-0a9c4a94bf3e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Holder
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_Duality

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
    (hf : MemLp f p μ) :
    MemLp (fun x => Real.sign (f x) * |f x| ^ (p.toReal - 1)) q μ := by
  set pr : ℝ := p.toReal with hpr
  have hp_ne_zero : p ≠ 0 := by
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
  have hpr_pos : 0 < pr := by
    simpa [pr] using ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have hpr_gt_one : 1 < pr := by
    have :=
      (ENNReal.toReal_lt_toReal (a := (1 : ℝ≥0∞)) (b := p) (by simp) hp_ne_top).2 hp
    simpa [pr, hpr] using this
  have hpr_ge_one : 1 ≤ pr := hpr_gt_one.le
  have hpr_ne_one : pr ≠ 1 := by
    intro h
    have hp_ofReal : ENNReal.ofReal pr = p := by
      simpa [pr] using ENNReal.ofReal_toReal hp_ne_top
    have hp_eq_one : p = 1 := by
      have : 1 = p := by simpa [h] using hp_ofReal
      exact this.symm
    have : (1 : ℝ≥0∞) < 1 := by simp [hp_eq_one] at hp
    exact lt_irrefl _ this
  -- Reduce the goal to the integrability of `|f|` raised to the conjugate exponent.
  -- Introduce the canonical dual candidate `g` and relate its norm to a simpler power.
  set g : α → ℝ := fun x => Real.sign (f x) * |f x| ^ (pr - 1)
  have hpr_sub_ne_zero : pr - 1 ≠ 0 := sub_ne_zero_of_ne hpr_ne_one
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
        simpa [ht_abs]
          using hcalc_abs
      have hcalc : ‖g x‖ = |Real.sign (f x)| * t := by
        simpa [Real.norm_eq_abs] using hcalc_abs'
      simpa [hsign_abs, ht] using hcalc
  have h_norm_abs_ae : ∀ᵐ x ∂μ, ‖g x‖ = |f x| ^ (pr - 1) :=
    Filter.Eventually.of_forall h_norm_abs
  have h_abs_norm : ∀ x, ‖|f x| ^ (pr - 1)‖ = |f x| ^ (pr - 1) := by
    intro x
    have hpow_nonneg : 0 ≤ |f x| ^ (pr - 1) := Real.rpow_nonneg (abs_nonneg _) _
    simp [Real.norm_eq_abs, hpow_nonneg]
  have h_abs_norm_ae : ∀ᵐ x ∂μ, ‖|f x| ^ (pr - 1)‖ = |f x| ^ (pr - 1) :=
    Filter.Eventually.of_forall h_abs_norm
  -- basic properties of the conjugate exponent `q`
  have hq_ne_zero : q ≠ 0 := by
    have hlt : (0 : ℝ≥0∞) < q := lt_of_le_of_lt (by simp : (0 : ℝ≥0∞) ≤ 1) hq
    exact ne_of_gt hlt
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
  -- collect the real exponents
  set qr : ℝ := q.toReal with hqr
  have hqr_pos : 0 < qr := by
    simpa [qr, hqr] using ENNReal.toReal_pos hq_ne_zero hq_ne_top
  have hqr_nonneg : 0 ≤ qr := hqr_pos.le
  -- obtain the real form of the conjugate relation
  have hpq_sum : 1 / p + 1 / q = 1 := by
    rcases hpq with hpq₁ | hpq₂ | hpq₃
    · rcases hpq₁ with ⟨hp_eq, _⟩
      have : False := by simp [hp_eq] at hp
      exact this.elim
    · rcases hpq₂ with ⟨hp_eq, hq_eq⟩
      have : False := by simp [hq_eq] at hq
      exact this.elim
    · rcases hpq₃ with ⟨_, _, _, _, hpq_sum⟩
      exact hpq_sum
  have hp_inv_ne_top : p⁻¹ ≠ ∞ := by
    simpa using (ENNReal.inv_ne_top).2 hp_ne_zero
  have hq_inv_ne_top : q⁻¹ ≠ ∞ := by
    simpa using (ENNReal.inv_ne_top).2 hq_ne_zero
  have h_inv_toReal : (1 / pr) + (1 / qr) = 1 := by
    have h_toReal := congrArg ENNReal.toReal hpq_sum
    have h_inv_pr : (p⁻¹).toReal = 1 / pr := by
      simp [pr, one_div]
    have h_inv_qr : (q⁻¹).toReal = 1 / qr := by
      simp [qr, one_div]
    have h_split := ENNReal.toReal_add hp_inv_ne_top hq_inv_ne_top
    simpa [one_div, h_split, h_inv_pr, h_inv_qr] using h_toReal
  have hpr_ne_zero : pr ≠ 0 := ne_of_gt hpr_pos
  have hqr_ne_zero : qr ≠ 0 := ne_of_gt hqr_pos
  have h_pow_identity : (pr - 1) * qr = pr := by
    have h_mul_pr := congrArg (fun t : ℝ => pr * t) h_inv_toReal
    have h_simplify : (1 : ℝ) + pr / qr = pr := by
      simpa [mul_add, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, hpr_ne_zero]
        using h_mul_pr
    have h_pr_div_qr : pr / qr = pr - 1 := (eq_sub_iff_add_eq').2 h_simplify
    have := congrArg (fun t : ℝ => t * qr) h_pr_div_qr
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, hqr_ne_zero] using this.symm
  -- show the sign factor is measurable and hence AE strongly measurable
  have h_sign_measurable : Measurable fun x : ℝ => Real.sign x := by
    have h_neg : MeasurableSet {x : ℝ | x < 0} :=
      measurableSet_lt measurable_id measurable_const
    have h_pos : MeasurableSet {x : ℝ | 0 < x} :=
      measurableSet_lt measurable_const measurable_id
    have h_pos_fun : Measurable fun x : ℝ => if 0 < x then (1 : ℝ) else 0 :=
      (measurable_const : Measurable fun _ : ℝ => (1 : ℝ)).ite h_pos measurable_const
    have h_total : Measurable fun x : ℝ => if x < 0 then (-1 : ℝ) else if 0 < x then 1 else 0 :=
      (measurable_const : Measurable fun _ : ℝ => (-1 : ℝ)).ite h_neg h_pos_fun
    simpa [Real.sign] using h_total
  have hf_aestrong : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have hf_aemeasurable : AEMeasurable f μ := hf_aestrong.aemeasurable
  have h_sign_aemeasurable : AEMeasurable (fun x => Real.sign (f x)) μ :=
    h_sign_measurable.comp_aemeasurable hf_aemeasurable
  have h_sign_aestrong : AEStronglyMeasurable (fun x => Real.sign (f x)) μ :=
    h_sign_aemeasurable.aestronglyMeasurable
  -- measurability of the power factor
  have h_abs_pow_cont : Continuous fun x : ℝ => |x| ^ (pr - 1) :=
    (continuous_abs).rpow_const (by intro _; exact Or.inr (sub_nonneg.mpr hpr_ge_one))
  have h_abs_pow_aestrong : AEStronglyMeasurable (fun x => |f x| ^ (pr - 1)) μ :=
    h_abs_pow_cont.comp_aestronglyMeasurable hf_aestrong
  have h_g_aestrong : AEStronglyMeasurable g μ :=
    h_sign_aestrong.mul h_abs_pow_aestrong
  -- identify the lintegral of `g`
  have hf_lintegral_fin : ∫⁻ x, ‖f x‖ₑ ^ pr ∂μ < ∞ :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := μ) (p := p)
      (f := f) hp_ne_zero hp_ne_top hf.eLpNorm_lt_top
  have h_integrand_eq : ∀ᵐ x ∂μ, ‖g x‖ₑ ^ qr = ‖f x‖ₑ ^ pr := by
    refine h_norm_abs_ae.mono ?_
    intro x hx
    have hg_abs : |g x| = |f x| ^ (pr - 1) := by
      simpa [Real.norm_eq_abs] using hx
    have h_base_nonneg : 0 ≤ |f x| := abs_nonneg _
    have h_abs_eq : |g x| ^ qr = |f x| ^ ((pr - 1) * qr) := by
      have := Real.rpow_mul h_base_nonneg (pr - 1) qr
      simpa [hg_abs, mul_comm, mul_left_comm, mul_assoc] using this.symm
    have h_abs_pow : |g x| ^ qr = |f x| ^ pr := by
      simpa [h_pow_identity] using h_abs_eq
    have h_left : ‖g x‖ₑ ^ qr = ENNReal.ofReal (|g x| ^ qr) := by
      simpa [Real.enorm_eq_ofReal_abs] using
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hqr_nonneg
    have h_right : ‖f x‖ₑ ^ pr = ENNReal.ofReal (|f x| ^ pr) := by
      simpa [Real.enorm_eq_ofReal_abs] using
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hpr_pos.le
    simpa [h_left, h_right] using congrArg ENNReal.ofReal h_abs_pow
  have hg_lintegral_fin : ∫⁻ x, ‖g x‖ₑ ^ qr ∂μ < ∞ := by
    have h_eq := lintegral_congr_ae h_integrand_eq
    simpa [h_eq] using hf_lintegral_fin
  have hg_eLpNorm_lt_top : eLpNorm g q μ < ∞ :=
    (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (μ := μ) (p := q)
        (f := g) hq_ne_zero hq_ne_top).2 hg_lintegral_fin
  exact ⟨h_g_aestrong, hg_eLpNorm_lt_top⟩
end Newton
