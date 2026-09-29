-- Prove2me | solution 1 for LanglandsTunnell.whittaker_ode_exists_sub_log_mul_sqrt_bound_near_zero_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5da8d9eb-d8fa-5efc-bdd7-a39d9144e5fb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_whittaker_ode_exists_sub_log_mul_sqrt_bound_near_zero_of_zero

set_option autoImplicit false

noncomputable section

open Real Filter Topology MeasureTheory Set intervalIntegral

namespace LanglandsTunnell
namespace Frob0

variable {g h q : ℝ → ℂ}

theorem g_sub (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (h y / y) y) (hhc : ContinuousOn h (Ioi 0))
    {t y₀ : ℝ} (ht : 0 < t) (hty : t ≤ y₀) :
    g y₀ - g t = ∫ s in t..y₀, h s / s := by
  have hcont : ContinuousOn (fun s : ℝ => h s / (s : ℂ)) (Icc t y₀) :=
    (hhc.mono fun s hs => ht.trans_le hs.1).div (Complex.continuous_ofReal.continuousOn)
      fun s hs => Complex.ofReal_ne_zero.mpr (ht.trans_le hs.1).ne'
  rw [integral_eq_sub_of_hasDerivAt]
  · intro s hs
    rw [uIcc_of_le hty] at hs
    exact hg s (ht.trans_le hs.1)
  · exact (hcont.intervalIntegrable_of_Icc hty)

theorem h_sub (hh : ∀ y : ℝ, 0 < y → HasDerivAt h (q y * g y) y) (hqc : ContinuousOn q (Ioi 0))
    (hgc : ContinuousOn g (Ioi 0)) {t y₀ : ℝ} (ht : 0 < t) (hty : t ≤ y₀) :
    h y₀ - h t = ∫ s in t..y₀, q s * g s := by
  have hcont : ContinuousOn (fun s : ℝ => q s * g s) (Icc t y₀) :=
    (hqc.mono fun s hs => ht.trans_le hs.1).mul (hgc.mono fun s hs => ht.trans_le hs.1)
  rw [integral_eq_sub_of_hasDerivAt]
  · intro s hs
    rw [uIcc_of_le hty] at hs
    exact hh s (ht.trans_le hs.1)
  · exact (hcont.intervalIntegrable_of_Icc hty)

theorem integral_log_div_le {s y₀ : ℝ} (hs : 0 < s) (hsy : s ≤ y₀) :
    ∫ r in s..y₀, (Real.log y₀ - Real.log r) ≤ y₀ := by
  have hy₀ : 0 < y₀ := hs.trans_le hsy
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_log',
    intervalIntegral.integral_const, integral_log, smul_eq_mul]
  have h2 : s * Real.log s - s * Real.log y₀ ≤ 0 := by
    rw [← mul_sub, ← Real.log_div hs.ne' hy₀.ne']
    exact mul_nonpos_of_nonneg_of_nonpos hs.le (Real.log_nonpos (div_pos hs hy₀).le ((div_le_one hy₀).mpr hsy))
  nlinarith [h2]

theorem log_div_le_two_sqrt {t y₀ : ℝ} (ht : 0 < t) (hty : t ≤ y₀) (hy₀1 : y₀ ≤ 1) :
    t * (Real.log y₀ - Real.log t) ≤ 2 * Real.sqrt t := by
  have hy₀ : 0 < y₀ := ht.trans_le hty
  rw [← Real.log_div hy₀.ne' ht.ne']
  have hu : 0 < y₀ / t := div_pos hy₀ ht
  have h1 : Real.log (y₀ / t) ≤ 2 * Real.sqrt (y₀ / t) := by
    have := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hu)
    rw [Real.log_sqrt hu.le] at this
    nlinarith [Real.sqrt_nonneg (y₀ / t)]
  have key : t * Real.sqrt (y₀ / t) = Real.sqrt (y₀ * t) := by
    rw [show t * Real.sqrt (y₀ / t) = Real.sqrt (t ^ 2) * Real.sqrt (y₀ / t) by rw [Real.sqrt_sq ht.le],
      ← Real.sqrt_mul (sq_nonneg t)]
    congr 1
    field_simp
  calc t * Real.log (y₀ / t) ≤ t * (2 * Real.sqrt (y₀ / t)) := mul_le_mul_of_nonneg_left h1 ht.le
    _ = 2 * Real.sqrt (y₀ * t) := by rw [← key]; ring
    _ ≤ 2 * Real.sqrt t := by
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
        nlinarith

end LanglandsTunnell.Frob0

end

noncomputable section

open Real Filter Topology MeasureTheory Set intervalIntegral

namespace LanglandsTunnell
namespace Frob0

variable {g h q : ℝ → ℂ}

section Core

variable (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (h y / y) y) (hh : ∀ y : ℝ, 0 < y → HasDerivAt h (q y * g y) y)
  (hqc : ContinuousOn q (Ioi 0)) {Q y₀ : ℝ} (hQ : 0 ≤ Q) (hy₀ : 0 < y₀) (hy₀1 : y₀ ≤ 1)
  (hq : ∀ y : ℝ, 0 < y → y ≤ y₀ → ‖q y‖ ≤ Q) (hsmall : Q * y₀ ≤ 1 / 2)

include hg in
theorem g_cont : ContinuousOn g (Ioi 0) := fun y hy => (hg y hy).continuousAt.continuousWithinAt

include hh in
theorem h_cont : ContinuousOn h (Ioi 0) := fun y hy => (hh y hy).continuousAt.continuousWithinAt

theorem norm_g_le (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (h y / y) y) (hhc : ContinuousOn h (Ioi 0))
    {t y₀ X : ℝ} (ht : 0 < t) (hX : ∀ s ∈ Icc t y₀, ‖h s‖ ≤ X) {s : ℝ} (hs : s ∈ Icc t y₀) :
    ‖g s‖ ≤ ‖g y₀‖ + X * (Real.log y₀ - Real.log s) := by
  have hs0 : 0 < s := ht.trans_le hs.1
  rw [← Real.log_div (hs0.trans_le hs.2).ne' hs0.ne']
  have e := g_sub hg hhc hs0 hs.2
  have hbound : ‖∫ r in s..y₀, h r / r‖ ≤ ∫ r in s..y₀, X * r⁻¹ := by
    refine norm_integral_le_of_norm_le hs.2 ?_ ?_
    · refine Filter.Eventually.of_forall fun r hr => ?_
      have hr0 : 0 < r := hs0.trans hr.1
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hX r ⟨hs.1.trans hr.1.le, hr.2⟩) (inv_nonneg.mpr hr0.le)
    · exact (intervalIntegrable_inv (fun r hr => by rw [uIcc_of_le hs.2] at hr; exact (hs0.trans_le hr.1).ne')
        continuousOn_id).const_mul X
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hs0 (hs0.trans_le hs.2)] at hbound
  calc ‖g s‖ = ‖g y₀ - (g y₀ - g s)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖g y₀‖ + ‖g y₀ - g s‖ := norm_sub_le _ _
    _ ≤ ‖g y₀‖ + X * Real.log (y₀ / s) := by rw [e]; linarith [hbound]

include hg hh hqc hQ hy₀ hy₀1 hq hsmall in

theorem bound (t : ℝ) (ht : 0 < t) (hty : t ≤ y₀) :
    ‖h t‖ ≤ 2 * (‖h y₀‖ + Q * y₀ * ‖g y₀‖) ∧
      ‖g t‖ ≤ ‖g y₀‖ + 2 * (‖h y₀‖ + Q * y₀ * ‖g y₀‖) * (Real.log y₀ - Real.log t) := by
  have hgc := g_cont hg
  have hhc := h_cont hh

  obtain ⟨s₀, hs₀, hmax⟩ := (isCompact_Icc (a := t) (b := y₀)).exists_isMaxOn ⟨t, le_rfl, hty⟩
    ((continuous_norm.comp_continuousOn (hhc.mono fun s hs => ht.trans_le hs.1)))
  set X : ℝ := ‖h s₀‖ with hXdef
  have hX : ∀ s ∈ Icc t y₀, ‖h s‖ ≤ X := fun s hs => hmax hs
  have hX0 : 0 ≤ X := norm_nonneg _
  set A : ℝ := ‖h y₀‖ + Q * y₀ * ‖g y₀‖ with hAdef

  have hgs : ∀ s ∈ Icc t y₀, ‖g s‖ ≤ ‖g y₀‖ + X * (Real.log y₀ - Real.log s) := fun s hs => norm_g_le hg hhc ht hX hs

  have hs₀0 : 0 < s₀ := ht.trans_le hs₀.1
  have e := h_sub hh hqc hgc hs₀0 hs₀.2
  have hint : ‖∫ r in s₀..y₀, q r * g r‖ ≤ ∫ r in s₀..y₀, Q * (‖g y₀‖ + X * (Real.log y₀ - Real.log r)) := by
    refine norm_integral_le_of_norm_le hs₀.2 ?_ ?_
    · refine Filter.Eventually.of_forall fun r hr => ?_
      have hr0 : 0 < r := hs₀0.trans hr.1
      rw [norm_mul]
      exact mul_le_mul (hq r hr0 hr.2) (hgs r ⟨hs₀.1.trans hr.1.le, hr.2⟩) (norm_nonneg _) hQ
    · exact (intervalIntegrable_const.add
        ((intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_log').const_mul X)).const_mul Q
  have hI : ∫ r in s₀..y₀, Q * (‖g y₀‖ + X * (Real.log y₀ - Real.log r)) ≤ Q * ‖g y₀‖ * y₀ + Q * X * y₀ := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
    · have h1 := integral_log_div_le hs₀0 hs₀.2
      have h2 : (y₀ - s₀) * ‖g y₀‖ ≤ y₀ * ‖g y₀‖ := by nlinarith [norm_nonneg (g y₀), hs₀0]
      nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hQ hX0), mul_le_mul_of_nonneg_left h2 hQ]
    · exact (intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_log').const_mul X
  have hXle : X ≤ A + Q * y₀ * X := by
    have : ‖h s₀‖ ≤ ‖h y₀‖ + ‖h y₀ - h s₀‖ := by
      calc ‖h s₀‖ = ‖h y₀ - (h y₀ - h s₀)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    rw [e] at this
    nlinarith [this, hint, hI]
  have hX2 : X ≤ 2 * A := by nlinarith [hXle, hsmall, hX0]
  refine ⟨(hX t ⟨le_rfl, hty⟩).trans hX2, (hgs t ⟨le_rfl, hty⟩).trans ?_⟩
  have hlog : 0 ≤ Real.log y₀ - Real.log t := sub_nonneg.mpr (Real.log_le_log ht hty)
  nlinarith [mul_le_mul_of_nonneg_right hX2 hlog]

end Core

end LanglandsTunnell.Frob0

end

noncomputable section

open Real Filter Topology MeasureTheory Set intervalIntegral

namespace LanglandsTunnell
namespace Frob0

variable {g h q : ℝ → ℂ}

section Limits

variable (hg : ∀ y : ℝ, 0 < y → HasDerivAt g (h y / y) y) (hh : ∀ y : ℝ, 0 < y → HasDerivAt h (q y * g y) y)
  (hqc : ContinuousOn q (Ioi 0)) {Q y₀ : ℝ} (hQ : 0 ≤ Q) (hy₀ : 0 < y₀) (hy₀1 : y₀ ≤ 1)
  (hq : ∀ y : ℝ, 0 < y → y ≤ y₀ → ‖q y‖ ≤ Q) (hsmall : Q * y₀ ≤ 1 / 2)

theorem intervalIntegrable_of_bound {F : ℝ → ℂ} {B : ℝ → ℝ} {y₀ : ℝ} (hy₀ : 0 < y₀)
    (hF : ContinuousOn F (Ioc 0 y₀)) (hB : IntervalIntegrable B volume 0 y₀)
    (hle : ∀ s ∈ Ioc 0 y₀, ‖F s‖ ≤ B s) : IntervalIntegrable F volume 0 y₀ := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hy₀.le] at hB ⊢
  refine Integrable.mono' hB (hF.aestronglyMeasurable measurableSet_Ioc) ?_
  exact (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hle)

include hg hh hqc hQ hy₀ hy₀1 hq hsmall in

theorem core : ∃ (a b : ℂ) (K : ℝ), ∀ t : ℝ, 0 < t → t ≤ y₀ →
    ‖h t - b‖ ≤ K * Real.sqrt t ∧ ‖g t - (a + b * (Real.log t : ℂ))‖ ≤ K * Real.sqrt t := by
  have hgc := g_cont hg
  have hhc := h_cont hh
  set A : ℝ := ‖h y₀‖ + Q * y₀ * ‖g y₀‖ with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hbd := bound hg hh hqc hQ hy₀ hy₀1 hq hsmall

  set B₁ : ℝ → ℝ := fun s => Q * (‖g y₀‖ + 2 * A * (Real.log y₀ - Real.log s)) with hB₁
  have hB₁i : ∀ a b : ℝ, IntervalIntegrable B₁ volume a b := fun a b =>
    (intervalIntegrable_const.add
      ((intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_log').const_mul (2 * A))).const_mul Q
  have hqg_le : ∀ s ∈ Ioc 0 y₀, ‖q s * g s‖ ≤ B₁ s := by
    intro s hs
    rw [norm_mul]
    exact mul_le_mul (hq s hs.1 hs.2) (hbd s hs.1 hs.2).2 (norm_nonneg _) hQ
  have hqgc : ContinuousOn (fun s => q s * g s) (Ioc 0 y₀) :=
    (hqc.mono fun s hs => hs.1).mul (hgc.mono fun s hs => hs.1)
  have hqgi : IntervalIntegrable (fun s => q s * g s) volume 0 y₀ := intervalIntegrable_of_bound hy₀ hqgc (hB₁i 0 y₀) hqg_le

  set b : ℂ := h y₀ - ∫ s in (0 : ℝ)..y₀, q s * g s with hbdef
  have hb_eq : ∀ t : ℝ, 0 < t → t ≤ y₀ → h t - b = ∫ s in (0 : ℝ)..t, q s * g s := by
    intro t ht hty
    have e := h_sub hh hqc hgc ht hty
    have sub1 : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) y₀ := by
      rw [uIcc_of_le ht.le, uIcc_of_le hy₀.le]; exact Icc_subset_Icc le_rfl hty
    have sub2 : uIcc t y₀ ⊆ uIcc (0 : ℝ) y₀ := by
      rw [uIcc_of_le hty, uIcc_of_le hy₀.le]; exact Icc_subset_Icc ht.le le_rfl
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hqgi.mono_set sub1) (hqgi.mono_set sub2)
    rw [hbdef, ← hadd, ← e]
    ring
  set K₁ : ℝ := Q * ‖g y₀‖ + 2 * A * Q * 3 with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hb_bd : ∀ t : ℝ, 0 < t → t ≤ y₀ → ‖h t - b‖ ≤ K₁ * Real.sqrt t := by
    intro t ht hty
    rw [hb_eq t ht hty]
    have h1 : ‖∫ s in (0 : ℝ)..t, q s * g s‖ ≤ ∫ s in (0 : ℝ)..t, B₁ s :=
      norm_integral_le_of_norm_le ht.le (Filter.Eventually.of_forall fun s hs => hqg_le s ⟨hs.1, hs.2.trans hty⟩) (hB₁i 0 t)
    have h2 : ∫ s in (0 : ℝ)..t, B₁ s = Q * (‖g y₀‖ * t + 2 * A * (t * (Real.log y₀ - Real.log t) + t)) := by
      rw [hB₁, intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const
        ((intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_log').const_mul (2 * A)),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_log',
        intervalIntegral.integral_const, integral_log]
      simp only [sub_zero, smul_eq_mul, Real.log_zero, mul_zero]
      ring
    have h3 := log_div_le_two_sqrt ht hty hy₀1
    have h4 : t ≤ Real.sqrt t := by
      have hst := Real.sqrt_le_sqrt (hty.trans hy₀1)
      rw [Real.sqrt_one] at hst
      nlinarith [Real.mul_self_sqrt ht.le, Real.sqrt_nonneg t]
    rw [h2] at h1
    refine h1.trans ?_
    rw [hK₁]
    have := norm_nonneg (g y₀)
    nlinarith [mul_le_mul_of_nonneg_left h4 (mul_nonneg hQ this), mul_le_mul_of_nonneg_left h3 (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hA0) hQ),
      mul_le_mul_of_nonneg_left h4 (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hA0) hQ)]

  set φ : ℝ → ℂ := fun s => g s - b * (Real.log s : ℂ) with hφdef
  have hφd : ∀ s : ℝ, 0 < s → HasDerivAt φ ((h s - b) / s) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => (Real.log s : ℂ)) ((s : ℂ)⁻¹) s := by
      simpa using (Real.hasDerivAt_log hs.ne').ofReal_comp
    have h2 := (hg s hs).sub (h1.const_mul b)
    convert h2 using 1 <;> try with_reducible_and_instances rfl
    rw [sub_div, div_eq_mul_inv b]
  have hφ'c : ContinuousOn (fun s => (h s - b) / (s : ℂ)) (Ioc 0 y₀) :=
    ((hhc.mono fun s hs => hs.1).sub continuousOn_const).div Complex.continuous_ofReal.continuousOn
      fun s hs => Complex.ofReal_ne_zero.mpr hs.1.ne'
  set B₂ : ℝ → ℝ := fun s => K₁ * s ^ (-(1 / 2 : ℝ)) with hB₂
  have hB₂i : ∀ c : ℝ, IntervalIntegrable B₂ volume 0 c := fun c =>
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul K₁
  have hφ'_le : ∀ s ∈ Ioc 0 y₀, ‖(h s - b) / (s : ℂ)‖ ≤ B₂ s := by
    intro s hs
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.1, hB₂]
    have hs2 : Real.sqrt s / s = s ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hs.1.le, div_eq_mul_inv, ← Real.rpow_neg_one,
        ← Real.rpow_neg hs.1.le, ← Real.rpow_add hs.1]
      norm_num
    calc ‖h s - b‖ / s ≤ K₁ * Real.sqrt s / s := div_le_div_of_nonneg_right (hb_bd s hs.1 hs.2) hs.1.le
      _ = K₁ * s ^ (-(1 / 2 : ℝ)) := by rw [mul_div_assoc, hs2]
  have hφ'i : IntervalIntegrable (fun s => (h s - b) / (s : ℂ)) volume 0 y₀ :=
    intervalIntegrable_of_bound hy₀ hφ'c (hB₂i y₀) hφ'_le
  set a : ℂ := φ y₀ - ∫ s in (0 : ℝ)..y₀, (h s - b) / (s : ℂ) with hadef
  have hφ_sub : ∀ t : ℝ, 0 < t → t ≤ y₀ → φ y₀ - φ t = ∫ s in t..y₀, (h s - b) / (s : ℂ) := by
    intro t ht hty
    rw [integral_eq_sub_of_hasDerivAt]
    · intro s hs
      rw [uIcc_of_le hty] at hs
      exact hφd s (ht.trans_le hs.1)
    · have sub2 : uIcc t y₀ ⊆ uIcc (0 : ℝ) y₀ := by
        rw [uIcc_of_le hty, uIcc_of_le hy₀.le]; exact Icc_subset_Icc ht.le le_rfl
      exact hφ'i.mono_set sub2
  have ha_eq : ∀ t : ℝ, 0 < t → t ≤ y₀ → φ t - a = ∫ s in (0 : ℝ)..t, (h s - b) / (s : ℂ) := by
    intro t ht hty
    have sub1 : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) y₀ := by
      rw [uIcc_of_le ht.le, uIcc_of_le hy₀.le]; exact Icc_subset_Icc le_rfl hty
    have sub2 : uIcc t y₀ ⊆ uIcc (0 : ℝ) y₀ := by
      rw [uIcc_of_le hty, uIcc_of_le hy₀.le]; exact Icc_subset_Icc ht.le le_rfl
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hφ'i.mono_set sub1) (hφ'i.mono_set sub2)
    rw [hadef, ← hadd, ← hφ_sub t ht hty]
    ring
  refine ⟨a, b, 2 * K₁, fun t ht hty => ⟨(hb_bd t ht hty).trans ?_, ?_⟩⟩
  · nlinarith [Real.sqrt_nonneg t]
  · have hφt : g t - (a + b * (Real.log t : ℂ)) = φ t - a := by rw [hφdef]; ring
    rw [hφt, ha_eq t ht hty]
    have h1 : ‖∫ s in (0 : ℝ)..t, (h s - b) / (s : ℂ)‖ ≤ ∫ s in (0 : ℝ)..t, B₂ s :=
      norm_integral_le_of_norm_le ht.le (Filter.Eventually.of_forall fun s hs => hφ'_le s ⟨hs.1, hs.2.trans hty⟩) (hB₂i t)
    have h2 : ∫ s in (0 : ℝ)..t, B₂ s = 2 * K₁ * Real.sqrt t := by
      rw [hB₂, intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
      rw [Real.zero_rpow (by norm_num), sub_zero, Real.sqrt_eq_rpow]
      norm_num
      ring
    rw [h2] at h1
    exact h1

end Limits

end LanglandsTunnell.Frob0

end

noncomputable section

open Real Filter Topology MeasureTheory Set intervalIntegral

namespace LanglandsTunnell
namespace Frob0

section Subst

variable (κ : ℝ) (f : ℝ → ℂ)
  (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
  (hfeq : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv f) y
          + (1 / 4 - (0 : ℂ) ^ 2 + 2 * (π : ℂ) * ((κ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)

def gOf (y : ℝ) : ℂ := ((Real.sqrt y : ℝ) : ℂ)⁻¹ * f y

def hOf (y : ℝ) : ℂ := ((Real.sqrt y : ℝ) : ℂ) * (deriv f y - f y / (2 * (y : ℂ)))

def qOf (y : ℝ) : ℂ := -(2 * (π : ℂ) * (κ : ℂ)) + 4 * (π : ℂ) ^ 2 * (y : ℂ)

theorem hasDerivAt_sqrtC {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => ((Real.sqrt t : ℝ) : ℂ)) ((((Real.sqrt y : ℝ) : ℂ))⁻¹ / 2) y := by
  have h := (Real.hasDerivAt_sqrt hy.ne').ofReal_comp
  convert h using 1
  push_cast
  ring

include hf in
theorem hasDerivAt_gOf {y : ℝ} (hy : 0 < y) : HasDerivAt (gOf f) (hOf f y / y) y := by
  have hS : ((Real.sqrt y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  have hS2 : ((Real.sqrt y : ℝ) : ℂ) ^ 2 = (y : ℂ) := by rw [← Complex.ofReal_pow, Real.sq_sqrt hy.le]
  have hfd : HasDerivAt f (deriv f y) y := (hf.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have h := hfd.div (hasDerivAt_sqrtC hy) hS
  have hfun : gOf f = fun t => f t / ((Real.sqrt t : ℝ) : ℂ) := funext fun t => by rw [gOf, inv_mul_eq_div]
  rw [hfun]
  refine h.congr_deriv ?_
  rw [hOf, ← hS2]
  field_simp

include hf hf' hfeq in
theorem hasDerivAt_hOf {y : ℝ} (hy : 0 < y) : HasDerivAt (hOf f) (qOf κ y * gOf f y) y := by
  have hS : ((Real.sqrt y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  have hS2 : ((Real.sqrt y : ℝ) : ℂ) ^ 2 = (y : ℂ) := by rw [← Complex.ofReal_pow, Real.sq_sqrt hy.le]
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hfd : HasDerivAt f (deriv f y) y := (hf.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have hfd' : HasDerivAt (deriv f) (deriv (deriv f) y) y := (hf'.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have hid : HasDerivAt (fun t : ℝ => (2 : ℂ) * (t : ℂ)) 2 y := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul (2 : ℂ)
  have h := (hasDerivAt_sqrtC hy).mul (hfd'.sub (hfd.div hid (mul_ne_zero two_ne_zero hy0)))
  refine h.congr_deriv ?_
  have e := hfeq y hy
  simp only [Pi.sub_apply, Pi.div_apply]

  set S : ℂ := ((Real.sqrt y : ℝ) : ℂ) with hSdef
  rw [qOf, gOf, ← hS2]
  rw [← hS2] at e
  have hS3 : S ^ 3 * S⁻¹ = S ^ 2 := by field_simp
  have hS5 : S ^ 5 * S⁻¹ = S ^ 4 := by field_simp
  field_simp
  linear_combination (4 : ℂ) * e + (8 * f y * (π : ℂ) * (κ : ℂ)) * hS3 - (16 * f y * (π : ℂ) ^ 2) * hS5

theorem norm_qOf_le {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) : ‖qOf κ y‖ ≤ 2 * π * |κ| + 4 * π ^ 2 := by
  rw [qOf]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      Complex.norm_two, abs_of_pos Real.pi_pos]
  · rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, abs_of_pos hy, show ‖(4 : ℂ)‖ = 4 by norm_num]
    nlinarith [Real.pi_pos, sq_nonneg π]

end Subst

end LanglandsTunnell.Frob0

end

open Real Complex Filter Topology

open LanglandsTunnell.Frob0 in

theorem solution
    (κ : ℝ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - (0 : ℂ) ^ 2 + 2 * (π : ℂ) * ((κ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) :
    ∃ (a b : ℂ) (δ : ℝ), 0 < δ ∧
      (∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖f y - (a + b * (Real.log y : ℂ)) * (Real.sqrt y : ℂ)‖ ≤ C * y ^ (1 / 2 + δ)) ∧
      (b = 0 →
        Tendsto (fun y : ℝ => ((Real.sqrt y : ℝ) : ℂ)⁻¹ * f y) (𝓝[>] 0) (𝓝 a) ∧
        Tendsto (fun y : ℝ => ((Real.sqrt y : ℝ) : ℂ) * (deriv f y - f y / (2 * (y : ℂ)))) (𝓝[>] 0) (𝓝 0)) := by

  set Q : ℝ := 2 * π * |κ| + 4 * π ^ 2 with hQdef
  have hQ1 : 1 ≤ Q := by
    have : (3 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
    nlinarith [abs_nonneg κ, Real.pi_pos]
  have hQ0 : 0 ≤ Q := by linarith
  set y₀ : ℝ := 1 / (2 * Q) with hy₀def
  have hy₀ : 0 < y₀ := by rw [hy₀def]; positivity
  have hy₀1 : y₀ ≤ 1 := by
    rw [hy₀def, div_le_one (by positivity)]; linarith
  have hsmall : Q * y₀ ≤ 1 / 2 := by rw [hy₀def]; field_simp; linarith
  have hg := fun y (hy : 0 < y) => hasDerivAt_gOf f hf hy
  have hh := fun y (hy : 0 < y) => hasDerivAt_hOf κ f hf hf' hfeq hy
  have hqc : ContinuousOn (qOf κ) (Set.Ioi 0) := by
    unfold qOf; fun_prop
  have hq : ∀ y : ℝ, 0 < y → y ≤ y₀ → ‖qOf κ y‖ ≤ Q := fun y hy hyy => norm_qOf_le κ hy (hyy.trans hy₀1)
  obtain ⟨a, b, K, hK⟩ := core hg hh hqc hQ0 hy₀ hy₀1 hq hsmall

  have hfc : ContinuousOn f (Set.Ioi 0) := hf.continuousOn
  set F : ℝ → ℂ := fun y => f y - (a + b * (Real.log y : ℂ)) * (Real.sqrt y : ℂ) with hFdef
  have hFc : ContinuousOn F (Set.Icc y₀ 1) := by
    refine (hfc.mono fun y hy => hy₀.trans_le hy.1).sub (ContinuousOn.mul ?_ ?_)
    · exact continuousOn_const.add (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
        (Real.continuousOn_log.mono fun y hy => (hy₀.trans_le hy.1).ne')))
    · exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := y₀) (b := 1)).exists_bound_of_continuousOn hFc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y₀ ⟨le_rfl, hy₀1⟩)
  refine ⟨a, b, 1 / 2, by norm_num, ⟨max K (M / y₀), fun y hy hy1 => ?_⟩, fun hb => ⟨?_, ?_⟩⟩
  · have hexp : (y : ℝ) ^ ((1 / 2 + 1 / 2 : ℝ)) = y := by norm_num
    rw [hexp]
    rcases le_or_gt y y₀ with hyy | hyy
    ·
      have h2 := (hK y hy hyy).2
      have hS : ((Real.sqrt y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
      have hid : f y - (a + b * (Real.log y : ℂ)) * (Real.sqrt y : ℂ) = (Real.sqrt y : ℂ) * (gOf f y - (a + b * (Real.log y : ℂ))) := by
        rw [gOf]; field_simp
      rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg y)]
      calc Real.sqrt y * ‖gOf f y - (a + b * (Real.log y : ℂ))‖ ≤ Real.sqrt y * (K * Real.sqrt y) :=
            mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg y)
        _ = K * y := by rw [mul_left_comm, Real.mul_self_sqrt hy.le]
        _ ≤ max K (M / y₀) * y := mul_le_mul_of_nonneg_right (le_max_left _ _) hy.le
    ·
      have h1 : ‖F y‖ ≤ M := hM y ⟨hyy.le, hy1⟩
      calc ‖f y - (a + b * (Real.log y : ℂ)) * (Real.sqrt y : ℂ)‖ = ‖F y‖ := rfl
        _ ≤ M := h1
        _ = (M / y₀) * y₀ := by field_simp
        _ ≤ (M / y₀) * y := mul_le_mul_of_nonneg_left hyy.le (div_nonneg hM0 hy₀.le)
        _ ≤ max K (M / y₀) * y := mul_le_mul_of_nonneg_right (le_max_right _ _) hy.le
  ·
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : Tendsto (fun y : ℝ => K * Real.sqrt y) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun y : ℝ => Real.sqrt y) (𝓝[>] 0) (𝓝 0) := by
        simpa using tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (0 : ℝ)) (Real.continuous_sqrt.tendsto 0)
      simpa using h0.const_mul K
    refine squeeze_zero' (Filter.Eventually.of_forall fun y => norm_nonneg _) ?_ hsq
    filter_upwards [Ioc_mem_nhdsGT hy₀] with y hy
    have h2 := (hK y hy.1 hy.2).2
    rw [hb, zero_mul, add_zero] at h2
    exact h2
  ·
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : Tendsto (fun y : ℝ => K * Real.sqrt y) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun y : ℝ => Real.sqrt y) (𝓝[>] 0) (𝓝 0) := by
        simpa using tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (0 : ℝ)) (Real.continuous_sqrt.tendsto 0)
      simpa using h0.const_mul K
    refine squeeze_zero' (Filter.Eventually.of_forall fun y => norm_nonneg _) ?_ hsq
    filter_upwards [Ioc_mem_nhdsGT hy₀] with y hy
    have h1 := (hK y hy.1 hy.2).1
    rw [hb] at h1
    exact h1

end S_LanglandsTunnell_whittaker_ode_exists_sub_log_mul_sqrt_bound_near_zero_of_zero
end P2MW
export P2MW.S_LanglandsTunnell_whittaker_ode_exists_sub_log_mul_sqrt_bound_near_zero_of_zero (solution)
