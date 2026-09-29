-- Prove2me | solution 1 for LanglandsTunnell.exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/df4a9afc-0a48-514e-b5a3-a063b3fd6728

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin

set_option autoImplicit false

open MeasureTheory Set Real

noncomputable section

namespace Z0RC

theorem integral_rpow_mul_exp_neg_mul_sq {B q : ℝ} (hB : 0 < B) (hq : -1 < q) :
    ∫ x in Ioi (0:ℝ), x ^ q * rexp (-B * x ^ 2) = B ^ (-(q + 1) / 2) * (1 / 2) * Real.Gamma ((q + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := q) (b := B) two_pos hq hB
  simp_rw [Real.rpow_two] at h
  exact h

theorem integrableOn_rpow_mul_exp_neg_div_sq {c r : ℝ} (hc : 0 < c) (hr : r < -1) :
    IntegrableOn (fun y : ℝ => y ^ r * rexp (-(c * (y ^ 2)⁻¹))) (Ioi 0) := by
  have hf : IntegrableOn (fun u : ℝ => u ^ (-r - 2) * rexp (-c * u ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hc (by linarith)
  have h := (integrableOn_Ioi_comp_rpow_iff (fun u : ℝ => u ^ (-r - 2) * rexp (-c * u ^ 2))
    (p := (-1 : ℝ)) (by norm_num)).mpr hf
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : 0 < x := hx
  show (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • ((x ^ (-1 : ℝ)) ^ (-r - 2) * rexp (-c * (x ^ (-1 : ℝ)) ^ 2)) =
    x ^ r * rexp (-(c * (x ^ 2)⁻¹))
  rw [smul_eq_mul, abs_neg, abs_one, one_mul, ← Real.rpow_mul hx0.le, Real.rpow_neg_one, inv_pow,
    ← mul_assoc, ← Real.rpow_add hx0]
  congr 1
  · norm_num
  · congr 1; ring

theorem rpow_le_rpow_add_rpow_neg {w r M : ℝ} (hw : 0 < w) (hM : |r| ≤ M) : w ^ r ≤ w ^ M + w ^ (-M) := by
  have hr1 : r ≤ M := (le_abs_self r).trans hM
  have hr2 : -M ≤ r := by have := neg_abs_le r; linarith
  rcases le_or_gt 1 w with h1 | h1
  · have : w ^ r ≤ w ^ M := Real.rpow_le_rpow_of_exponent_le h1 hr1
    linarith [Real.rpow_nonneg hw.le (-M)]
  · have : w ^ r ≤ w ^ (-M) := Real.rpow_le_rpow_of_exponent_ge hw h1.le hr2
    linarith [Real.rpow_nonneg hw.le M]

theorem integrableOn_rpow_mul_torusGauss {b : ℝ} (hb : 0 < b) (r : ℝ) :
    IntegrableOn (fun w : ℝ => w ^ r * rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2)))) (Ioi 0) := by
  set M : ℝ := max |r| 2 with hM
  have hM2 : (2 : ℝ) ≤ M := le_max_right _ _
  have hMr : |r| ≤ M := le_max_left _ _
  have h1 : IntegrableOn (fun w : ℝ => w ^ M * rexp (-(π * b) * w ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq (by positivity) (by linarith)
  have h2 : IntegrableOn (fun w : ℝ => w ^ (-M) * rexp (-(π * (w ^ 2)⁻¹))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_div_sq Real.pi_pos (by linarith)
  refine Integrable.mono' (h1.add h2) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun w hw => ?_) measurableSet_Ioi
    have hw : (0 : ℝ) < w := hw
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl hw.ne')).mul
      ((Real.continuous_exp.continuousAt).comp
        (((continuousAt_inv₀ (by positivity)).comp (continuousAt_pow _ 2)).add
          ((continuous_const.mul (continuous_pow 2)).continuousAt) |>.const_mul π |>.neg))).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun w (hw : 0 < w) => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hw.le _) (Real.exp_nonneg _))]
    have hE1 : rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2))) ≤ rexp (-(π * b) * w ^ 2) :=
      Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, inv_nonneg.2 (sq_nonneg w)])
    have hE2 : rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2))) ≤ rexp (-(π * (w ^ 2)⁻¹)) := by
      refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le))
      exact le_add_of_nonneg_right (by positivity)
    have hw1 := rpow_le_rpow_add_rpow_neg hw hMr
    have hE0 : 0 ≤ rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2))) := Real.exp_nonneg _
    calc w ^ r * rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2)))
        ≤ (w ^ M + w ^ (-M)) * rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2))) := mul_le_mul_of_nonneg_right hw1 hE0
      _ = w ^ M * rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2))) + w ^ (-M) * rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2))) := by ring
      _ ≤ w ^ M * rexp (-(π * b) * w ^ 2) + w ^ (-M) * rexp (-(π * (w ^ 2)⁻¹)) :=
          add_le_add (mul_le_mul_of_nonneg_left hE1 (Real.rpow_nonneg hw.le _))
            (mul_le_mul_of_nonneg_left hE2 (Real.rpow_nonneg hw.le _))

theorem integral_cpow_mul_exp_neg_pi_mul_sq {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0:ℝ), (t : ℂ) ^ (z - 1) * (rexp (-(π * t ^ 2)) : ℂ) = (1 / 2 : ℂ) * Complex.Gammaℝ z := by
  have hG : ∫ v in Ioi (0:ℝ), (1 / 2 : ℂ) * ((v : ℂ) ^ (z / 2 - 1) * (rexp (-(π * v)) : ℂ)) =
      (1 / 2 : ℂ) * Complex.Gammaℝ z := by
    rw [integral_const_mul]
    congr 1
    have hz2 : 0 < (z / 2).re := by
      rw [Complex.div_re]; simp; positivity
    have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hz2 Real.pi_pos
    rw [Complex.Gammaℝ_def]
    have h1 : (fun v : ℝ => (v : ℂ) ^ (z / 2 - 1) * (rexp (-(π * v)) : ℂ)) =
        fun v : ℝ => (v : ℂ) ^ (z / 2 - 1) * Complex.exp (-(π * v)) := by
      funext v; push_cast; rfl
    rw [h1, h, one_div, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm),
      ← Complex.cpow_neg]
    congr 1; ring
  have key := integral_comp_rpow_Ioi_of_pos
    (g := fun v : ℝ => (1 / 2 : ℂ) * ((v : ℂ) ^ (z / 2 - 1) * (rexp (-(π * v)) : ℂ))) two_pos
  rw [hG] at key
  rw [← key]
  refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_
  symm
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  have hpow : (((x ^ (2 : ℝ)) : ℝ) : ℂ) ^ (z / 2 - 1) = (x : ℂ) ^ (z - 2) := by
    rw [Complex.ofReal_cpow hx.le]
    rw [← Complex.cpow_mul]
    · congr 1; push_cast; ring
    · rw [← Complex.ofReal_log hx.le]; simp [Real.pi_pos]
    · rw [← Complex.ofReal_log hx.le]; simp [Real.pi_pos.le]
  show ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) • ((1 / 2 : ℂ) * ((((x ^ (2 : ℝ)) : ℝ) : ℂ) ^ (z / 2 - 1) *
      (rexp (-(π * x ^ (2 : ℝ))) : ℂ))) = (x : ℂ) ^ (z - 1) * (rexp (-(π * x ^ 2)) : ℂ)
  rw [hpow, Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Complex.real_smul]
  have hsplit : (x : ℂ) ^ (z - 1) = (x : ℂ) * (x : ℂ) ^ (z - 2) := by
    rw [show z - 1 = 1 + (z - 2) by ring, Complex.cpow_add _ _ hx0, Complex.cpow_one]
  rw [hsplit]
  push_cast
  ring

theorem integral_cpow_mul_exp_neg_pi_div_sq {z : ℂ} (hz : 0 < z.re) :
    ∫ y in Ioi (0:ℝ), (y : ℂ) ^ (-z - 1) * (rexp (-(π * (y ^ 2)⁻¹)) : ℂ) = (1 / 2 : ℂ) * Complex.Gammaℝ z := by
  rw [← integral_cpow_mul_exp_neg_pi_mul_sq hz]
  have key := integral_comp_rpow_Ioi (fun t : ℝ => (t : ℂ) ^ (z - 1) * (rexp (-(π * t ^ 2)) : ℂ))
    (p := (-1 : ℝ)) (by norm_num)
  rw [← key]
  refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  have harg : (x : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm
  show (x : ℂ) ^ (-z - 1) * (rexp (-(π * (x ^ 2)⁻¹)) : ℂ) =
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • (((x ^ (-1 : ℝ) : ℝ) : ℂ) ^ (z - 1) * (rexp (-(π * (x ^ (-1 : ℝ)) ^ 2)) : ℂ))
  rw [abs_neg, abs_one, one_mul, Real.rpow_neg_one, inv_pow, Complex.real_smul, show (-1 : ℝ) - 1 = -2 by norm_num,
    Complex.ofReal_cpow hx.le, Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg,
    ← mul_assoc, ← Complex.cpow_add _ _ hx0]
  congr 1
  · congr 1; push_cast; ring

section Core

def F3 (b : ℝ) (p : ℂ) (g K : ℝ → ℂ) (s : ℂ) (q : ℝ × ℝ × ℝ) : ℂ :=
  ((q.1 : ℝ) : ℂ) ^ (s - 2) * (((q.2.1 : ℝ) : ℂ) ^ p * K q.2.2 *
    (rexp (-(π * ((q.2.1 ^ 2)⁻¹ + b * q.1 ^ 2 * q.2.1 ^ 2))) : ℂ) * g (q.1 * q.2.1 / q.2.2))

theorem cpow_ofReal_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (c : ℂ) :
    (((x * y : ℝ)) : ℂ) ^ c = (x : ℂ) ^ c * (y : ℂ) ^ c := by
  push_cast; exact Complex.mul_cpow_ofReal_nonneg hx hy c

theorem cpow_ofReal_inv {x : ℝ} (hx : 0 < x) (c : ℂ) : (((x⁻¹ : ℝ)) : ℂ) ^ c = (x : ℂ) ^ (-c) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ ?_, Complex.cpow_neg]
  rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm

theorem cpow_ofReal_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (c : ℂ) :
    (((x / y : ℝ)) : ℂ) ^ c = (x : ℂ) ^ c * (y : ℂ) ^ (-c) := by
  rw [div_eq_mul_inv, cpow_ofReal_mul hx (inv_pos.2 hy).le, cpow_ofReal_inv hy]

variable {b : ℝ} {p : ℂ} {g K : ℝ → ℂ}

theorem F3_rescale (hb : 0 < b) (s : ℂ) {y₁ y₂ τ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (hτ : 0 < τ) :
    F3 b p g K s (y₂ / y₁ * τ, y₁, y₂) =
      ((y₂ : ℂ) ^ (s - 2) * (y₁ : ℂ) ^ (2 - s) * (y₁ : ℂ) ^ p * K y₂ * (rexp (-(π * (y₁ ^ 2)⁻¹)) : ℂ)) *
        ((τ : ℂ) ^ (s - 2) * (rexp (-(π * b * y₂ ^ 2 * τ ^ 2)) : ℂ) * g τ) := by
  simp only [F3]
  have h1 : (((y₂ / y₁ * τ : ℝ)) : ℂ) ^ (s - 2) = (y₂ : ℂ) ^ (s - 2) * (y₁ : ℂ) ^ (2 - s) * (τ : ℂ) ^ (s - 2) := by
    rw [cpow_ofReal_mul (div_pos hy₂ hy₁).le hτ.le, cpow_ofReal_div hy₂.le hy₁, neg_sub]
  have h2 : rexp (-(π * ((y₁ ^ 2)⁻¹ + b * (y₂ / y₁ * τ) ^ 2 * y₁ ^ 2))) =
      rexp (-(π * (y₁ ^ 2)⁻¹)) * rexp (-(π * b * y₂ ^ 2 * τ ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have h3 : y₂ / y₁ * τ * y₁ / y₂ = τ := by field_simp
  rw [h1, h2, h3]
  push_cast
  ring

theorem inner_y_eq (hb : 0 < b) (s : ℂ) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
    ∫ y in Ioi (0:ℝ), F3 b p g K s (y, y₁, y₂) =
      ((y₁ : ℂ) ^ (p - s + 1) * (rexp (-(π * (y₁ ^ 2)⁻¹)) : ℂ)) *
      ((y₂ : ℂ) ^ (s - 1) * K y₂ *
        ∫ τ in Ioi (0:ℝ), (τ : ℂ) ^ (s - 2) * (rexp (-(π * b * y₂ ^ 2 * τ ^ 2)) : ℂ) * g τ) := by
  have hc : 0 < y₂ / y₁ := div_pos hy₂ hy₁
  have key := integral_comp_mul_left_Ioi (fun y : ℝ => F3 b p g K s (y, y₁, y₂)) 0 hc
  rw [mul_zero] at key
  have key' : ∫ y in Ioi (0:ℝ), F3 b p g K s (y, y₁, y₂) =
      ((y₂ / y₁ : ℝ) : ℂ) * ∫ τ in Ioi (0:ℝ), F3 b p g K s (y₂ / y₁ * τ, y₁, y₂) := by
    rw [key, ← Complex.real_smul, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  rw [key']
  rw [setIntegral_congr_fun measurableSet_Ioi (fun τ (hτ : 0 < τ) => F3_rescale hb s hy₁ hy₂ hτ),
    integral_const_mul]
  have hy₁0 : (y₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₁.ne'
  have hy₂0 : (y₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₂.ne'
  have e1 : (y₂ : ℂ) ^ (s - 1) = (y₂ : ℂ) * (y₂ : ℂ) ^ (s - 2) := by
    rw [show s - 1 = 1 + (s - 2) by ring, Complex.cpow_add _ _ hy₂0, Complex.cpow_one]
  have e2 : (y₁ : ℂ) ^ (p - s + 1) = (y₁ : ℂ) ^ p * (y₁ : ℂ) ^ (2 - s) * (y₁ : ℂ)⁻¹ := by
    rw [show p - s + 1 = p + (2 - s) + (-1 : ℂ) by ring, Complex.cpow_add _ _ hy₁0, Complex.cpow_add _ _ hy₁0,
      Complex.cpow_neg_one]
  rw [e1, e2]
  push_cast
  ring

theorem inner_tau_eq (hb : 0 < b) (s : ℂ) {y₂ : ℝ} (hy₂ : 0 < y₂) :
    (y₂ : ℂ) ^ (s - 1) * K y₂ * ∫ τ in Ioi (0:ℝ), (τ : ℂ) ^ (s - 2) * (rexp (-(π * b * y₂ ^ 2 * τ ^ 2)) : ℂ) * g τ =
      K y₂ * ∫ σ' in Ioi (0:ℝ), (σ' : ℂ) ^ (s - 2) * (rexp (-(π * b * σ' ^ 2)) : ℂ) * g (σ' / y₂) := by
  have hc : 0 < y₂⁻¹ := inv_pos.2 hy₂
  have key := integral_comp_mul_left_Ioi
    (fun τ : ℝ => (τ : ℂ) ^ (s - 2) * (rexp (-(π * b * y₂ ^ 2 * τ ^ 2)) : ℂ) * g τ) 0 hc
  rw [mul_zero, inv_inv] at key

  have key' : ∫ τ in Ioi (0:ℝ), (τ : ℂ) ^ (s - 2) * (rexp (-(π * b * y₂ ^ 2 * τ ^ 2)) : ℂ) * g τ =
      ((y₂⁻¹ : ℝ) : ℂ) * ∫ σ' in Ioi (0:ℝ),
        (((y₂⁻¹ * σ' : ℝ)) : ℂ) ^ (s - 2) * (rexp (-(π * b * y₂ ^ 2 * (y₂⁻¹ * σ') ^ 2)) : ℂ) * g (y₂⁻¹ * σ') := by
    rw [key, ← Complex.real_smul, smul_smul, inv_mul_cancel₀ hy₂.ne', one_smul]
  rw [key']
  have hpt : ∀ σ' : ℝ, σ' ∈ Ioi (0:ℝ) →
      (((y₂⁻¹ * σ' : ℝ)) : ℂ) ^ (s - 2) * (rexp (-(π * b * y₂ ^ 2 * (y₂⁻¹ * σ') ^ 2)) : ℂ) * g (y₂⁻¹ * σ') =
        (y₂ : ℂ) ^ (2 - s) * ((σ' : ℂ) ^ (s - 2) * (rexp (-(π * b * σ' ^ 2)) : ℂ) * g (σ' / y₂)) := by
    intro σ' hσ'
    have hσ : (0:ℝ) < σ' := hσ'
    rw [cpow_ofReal_mul hc.le hσ.le, cpow_ofReal_inv hy₂, neg_sub, inv_mul_eq_div]
    have : π * b * y₂ ^ 2 * (σ' / y₂) ^ 2 = π * b * σ' ^ 2 := by field_simp
    rw [this]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have hy₂0 : (y₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₂.ne'
  have e1 : (y₂ : ℂ) ^ (s - 1) * (((y₂⁻¹ : ℝ)) : ℂ) * (y₂ : ℂ) ^ (2 - s) = 1 := by
    rw [Complex.ofReal_inv, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hy₂0, ← Complex.cpow_add _ _ hy₂0,
      show s - 1 + -1 + (2 - s) = 0 by ring, Complex.cpow_zero]
  calc (y₂ : ℂ) ^ (s - 1) * K y₂ * ((((y₂⁻¹ : ℝ)) : ℂ) * ((y₂ : ℂ) ^ (2 - s) *
        ∫ σ' in Ioi (0:ℝ), (σ' : ℂ) ^ (s - 2) * (rexp (-(π * b * σ' ^ 2)) : ℂ) * g (σ' / y₂)))
      = ((y₂ : ℂ) ^ (s - 1) * (((y₂⁻¹ : ℝ)) : ℂ) * (y₂ : ℂ) ^ (2 - s)) * (K y₂ *
        ∫ σ' in Ioi (0:ℝ), (σ' : ℂ) ^ (s - 2) * (rexp (-(π * b * σ' ^ 2)) : ℂ) * g (σ' / y₂)) := by ring
    _ = _ := by rw [e1, one_mul]

end Core

section Main

variable {b : ℝ} {p : ℂ} {g K : ℝ → ℂ} {C σ CK N : ℝ}

local notation "μ0" => Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))

theorem measurable_F3 (hgm : Measurable g) (hKm : Measurable K) (s : ℂ) : Measurable (F3 b p g K s) := by
  unfold F3
  have h1 : Measurable fun q : ℝ × ℝ × ℝ => ((q.1 : ℝ) : ℂ) ^ (s - 2) :=
    (Complex.measurable_ofReal.comp measurable_fst).pow_const _
  have h2 : Measurable fun q : ℝ × ℝ × ℝ => ((q.2.1 : ℝ) : ℂ) ^ p :=
    (Complex.measurable_ofReal.comp (measurable_fst.comp measurable_snd)).pow_const _
  have h3 : Measurable fun q : ℝ × ℝ × ℝ => K q.2.2 := hKm.comp (measurable_snd.comp measurable_snd)
  have h4 : Measurable fun q : ℝ × ℝ × ℝ =>
      (rexp (-(π * ((q.2.1 ^ 2)⁻¹ + b * q.1 ^ 2 * q.2.1 ^ 2))) : ℂ) := by
    refine Complex.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    exact ((((measurable_fst.comp measurable_snd).pow_const 2).inv.add
      ((measurable_const.mul (measurable_fst.pow_const 2)).mul ((measurable_fst.comp measurable_snd).pow_const 2))).const_mul π).neg
  have h5 : Measurable fun q : ℝ × ℝ × ℝ => g (q.1 * q.2.1 / q.2.2) :=
    hgm.comp ((measurable_fst.mul (measurable_fst.comp measurable_snd)).div (measurable_snd.comp measurable_snd))
  exact h1.mul (((h2.mul h3).mul h4).mul h5)

theorem C_nonneg (hg : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * (1 + t ^ (-σ))) : 0 ≤ C := by
  have h := hg 1 one_pos
  rw [Real.one_rpow] at h
  nlinarith [norm_nonneg (g 1)]

theorem CK_nonneg (hK : ∀ w : ℝ, 0 < w → ‖K w‖ ≤ CK * (w ^ N + w ^ (-N)) * rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2)))) :
    0 ≤ CK := by
  have h := hK 1 one_pos
  simp only [Real.one_rpow, one_pow, inv_one, one_mul, mul_one] at h
  have he : 0 < rexp (-(π * (1 + b))) := Real.exp_pos _
  nlinarith [norm_nonneg (K 1)]

theorem norm_g_mul_le (hg : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * (1 + t ^ (-σ))) {α : ℝ} {t E : ℝ} (ht : 0 < t) (hE : 0 ≤ E) :
    t ^ α * E * ‖g t‖ ≤ C * (t ^ α * E + t ^ (α - σ) * E) := by
  have h := hg t ht
  have h0 : 0 ≤ t ^ α * E := mul_nonneg (Real.rpow_nonneg ht.le _) hE
  calc t ^ α * E * ‖g t‖ ≤ t ^ α * E * (C * (1 + t ^ (-σ))) := mul_le_mul_of_nonneg_left h h0
    _ = C * (t ^ α * E + t ^ (α - σ) * E) := by
        rw [sub_eq_add_neg, Real.rpow_add ht]; ring

theorem integrable_normK_mul_rpow (hb : 0 < b) (hKm : Measurable K)
    (hK : ∀ w : ℝ, 0 < w → ‖K w‖ ≤ CK * (w ^ N + w ^ (-N)) * rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2)))) (r : ℝ) :
    Integrable (fun w : ℝ => ‖K w‖ * w ^ r) μ0 := by
  have hdom : Integrable (fun w : ℝ => CK * (w ^ (N + r) * rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2))) +
      w ^ (-N + r) * rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2))))) μ0 :=
    ((integrableOn_rpow_mul_torusGauss hb (N + r)).add (integrableOn_rpow_mul_torusGauss hb (-N + r))).const_mul CK
  refine Integrable.mono' hdom ((hKm.norm.mul (measurable_id.pow_const r)).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun w (hw : 0 < w) => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hw.le _))]
  have h := hK w hw
  have hr : 0 ≤ w ^ r := Real.rpow_nonneg hw.le _
  calc ‖K w‖ * w ^ r ≤ CK * (w ^ N + w ^ (-N)) * rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2))) * w ^ r :=
        mul_le_mul_of_nonneg_right h hr
    _ = CK * (w ^ (N + r) * rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2))) +
        w ^ (-N + r) * rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2)))) := by
        rw [Real.rpow_add hw, Real.rpow_add hw]; ring

theorem ae_pos_prod : ∀ᵐ q : ℝ × ℝ ∂((μ0).prod (μ0)), 0 < q.1 ∧ 0 < q.2 := by
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with q hq
  exact ⟨hq.1, hq.2⟩

theorem integrableOn_F3_y (hb : 0 < b) (hgm : Measurable g)
    (hg : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * (1 + t ^ (-σ)))
    (s : ℂ) (hs : -1 < s.re - 2 - σ) (hσ : 0 ≤ σ) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
    IntegrableOn (fun y : ℝ => F3 b p g K s (y, y₁, y₂)) (Ioi 0) := by
  have hc : 0 < y₂ / y₁ := div_pos hy₂ hy₁
  have key := integrableOn_Ioi_comp_mul_left_iff (fun y : ℝ => F3 b p g K s (y, y₁, y₂)) 0 hc
  rw [mul_zero] at key
  refine key.1 ?_

  have hB : 0 < π * b * y₂ ^ 2 := by positivity
  have hdom : IntegrableOn (fun τ : ℝ => C * (τ ^ (s.re - 2) * rexp (-(π * b * y₂ ^ 2) * τ ^ 2) +
      τ ^ (s.re - 2 - σ) * rexp (-(π * b * y₂ ^ 2) * τ ^ 2))) (Ioi 0) :=
    ((integrableOn_rpow_mul_exp_neg_mul_sq hB (by linarith)).add
      (integrableOn_rpow_mul_exp_neg_mul_sq hB hs)).const_mul C
  have hcore : IntegrableOn (fun τ : ℝ => (τ : ℂ) ^ (s - 2) * (rexp (-(π * b * y₂ ^ 2 * τ ^ 2)) : ℂ) * g τ) (Ioi 0) := by
    refine Integrable.mono' hdom ?_ ?_
    · exact (((Complex.measurable_ofReal.pow_const _).mul (Complex.measurable_ofReal.comp
        (Real.measurable_exp.comp (by fun_prop)))).mul hgm).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : 0 < τ) => ?_)
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hτ, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_nonneg _), Complex.sub_re, show (2 : ℂ).re = 2 by norm_num]
      have := norm_g_mul_le hg (α := s.re - 2) hτ (Real.exp_nonneg (-(π * b * y₂ ^ 2 * τ ^ 2)))
      convert this using 2 <;> ring_nf
  have heq : ∀ τ ∈ Ioi (0:ℝ), F3 b p g K s (y₂ / y₁ * τ, y₁, y₂) =
      ((y₂ : ℂ) ^ (s - 2) * (y₁ : ℂ) ^ (2 - s) * (y₁ : ℂ) ^ p * K y₂ * (rexp (-(π * (y₁ ^ 2)⁻¹)) : ℂ)) *
        ((τ : ℂ) ^ (s - 2) * (rexp (-(π * b * y₂ ^ 2 * τ ^ 2)) : ℂ) * g τ) :=
    fun τ hτ => F3_rescale hb s hy₁ hy₂ hτ
  exact IntegrableOn.congr_fun (hcore.const_mul ((y₂ : ℂ) ^ (s - 2) * (y₁ : ℂ) ^ (2 - s) * (y₁ : ℂ) ^ p * K y₂ *
    (rexp (-(π * (y₁ ^ 2)⁻¹)) : ℂ))) (fun τ hτ => (heq τ hτ).symm) measurableSet_Ioi

def Tn (b : ℝ) (g : ℝ → ℂ) (α : ℝ) (y₂ : ℝ) : ℝ :=
  ∫ τ in Ioi (0:ℝ), τ ^ α * rexp (-(π * b * y₂ ^ 2 * τ ^ 2)) * ‖g τ‖

theorem Tn_nonneg (α y₂ : ℝ) : 0 ≤ Tn b g α y₂ :=
  setIntegral_nonneg measurableSet_Ioi fun τ (hτ : 0 < τ) =>
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hτ.le _) (Real.exp_nonneg _)) (norm_nonneg _)

theorem integral_moment (hb : 0 < b) {q y₂ : ℝ} (hq : -1 < q) (hy₂ : 0 < y₂) :
    ∫ τ in Ioi (0:ℝ), τ ^ q * rexp (-(π * b * y₂ ^ 2) * τ ^ 2) =
      (π * b) ^ (-(q + 1) / 2) * y₂ ^ (-(q + 1)) * ((1 / 2) * Real.Gamma ((q + 1) / 2)) := by
  rw [integral_rpow_mul_exp_neg_mul_sq (by positivity) hq, Real.mul_rpow (by positivity) (sq_nonneg _),
    show y₂ ^ 2 = y₂ ^ (2 : ℝ) by rw [Real.rpow_two], ← Real.rpow_mul hy₂.le,
    show (2 : ℝ) * (-(q + 1) / 2) = -(q + 1) by ring]
  ring

theorem rpow_mul_Tn_le (hb : 0 < b) (hgm : Measurable g)
    (hg : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * (1 + t ^ (-σ))) {α : ℝ} (hα : -1 < α - σ) (hσ : 0 ≤ σ)
    {y₂ : ℝ} (hy₂ : 0 < y₂) :
    y₂ ^ (α + 1) * Tn b g α y₂ ≤
      C * ((π * b) ^ (-(α + 1) / 2) * ((1 / 2) * Real.Gamma ((α + 1) / 2))) +
        C * ((π * b) ^ (-(α - σ + 1) / 2) * ((1 / 2) * Real.Gamma ((α - σ + 1) / 2))) * y₂ ^ σ := by
  have hB : 0 < π * b * y₂ ^ 2 := by positivity
  have hα' : -1 < α := by linarith
  have i1 := integrableOn_rpow_mul_exp_neg_mul_sq hB hα'
  have i2 := integrableOn_rpow_mul_exp_neg_mul_sq hB hα
  have hTle : Tn b g α y₂ ≤ C * ((∫ τ in Ioi (0:ℝ), τ ^ α * rexp (-(π * b * y₂ ^ 2) * τ ^ 2)) +
      ∫ τ in Ioi (0:ℝ), τ ^ (α - σ) * rexp (-(π * b * y₂ ^ 2) * τ ^ 2)) := by
    rw [← integral_add i1 i2, ← integral_const_mul]
    refine setIntegral_mono_on ?_ ((i1.add i2).const_mul C) measurableSet_Ioi fun τ (hτ : 0 < τ) => ?_
    ·
      refine Integrable.mono' ((i1.add i2).const_mul C) ?_ ?_
      · exact (((measurable_id.pow_const α).mul (Real.measurable_exp.comp (by fun_prop))).mul hgm.norm).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : 0 < τ) => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hτ.le _) (Real.exp_nonneg _)) (norm_nonneg _))]
        have := norm_g_mul_le hg (α := α) hτ (Real.exp_nonneg (-(π * b * y₂ ^ 2) * τ ^ 2))
        convert this using 2 <;> first | rfl | (simp only [Pi.add_apply]; ring_nf) | ring_nf
    · have := norm_g_mul_le hg (α := α) hτ (Real.exp_nonneg (-(π * b * y₂ ^ 2) * τ ^ 2))
      convert this using 2 <;> first | rfl | (simp only [Pi.add_apply]; ring_nf) | ring_nf
  rw [integral_moment hb hα' hy₂, integral_moment hb hα hy₂] at hTle
  have hy : 0 ≤ y₂ ^ (α + 1) := Real.rpow_nonneg hy₂.le _
  have e1 : y₂ ^ (α + 1) * y₂ ^ (-(α + 1)) = 1 := by
    rw [← Real.rpow_add hy₂, add_neg_cancel, Real.rpow_zero]
  have e2 : y₂ ^ (α + 1) * y₂ ^ (-(α - σ + 1)) = y₂ ^ σ := by
    rw [← Real.rpow_add hy₂]; congr 1; ring
  calc y₂ ^ (α + 1) * Tn b g α y₂
      ≤ y₂ ^ (α + 1) * (C * ((π * b) ^ (-(α + 1) / 2) * y₂ ^ (-(α + 1)) * ((1 / 2) * Real.Gamma ((α + 1) / 2)) +
          (π * b) ^ (-(α - σ + 1) / 2) * y₂ ^ (-(α - σ + 1)) * ((1 / 2) * Real.Gamma ((α - σ + 1) / 2)))) :=
        mul_le_mul_of_nonneg_left hTle hy
    _ = C * ((π * b) ^ (-(α + 1) / 2) * ((1 / 2) * Real.Gamma ((α + 1) / 2))) * (y₂ ^ (α + 1) * y₂ ^ (-(α + 1))) +
        C * ((π * b) ^ (-(α - σ + 1) / 2) * ((1 / 2) * Real.Gamma ((α - σ + 1) / 2))) *
          (y₂ ^ (α + 1) * y₂ ^ (-(α - σ + 1))) := by ring
    _ = _ := by rw [e1, e2, mul_one]

theorem measurable_Tn (hgm : Measurable g) (α : ℝ) : Measurable (Tn b g α) := by
  unfold Tn
  have h : StronglyMeasurable (Function.uncurry fun (y₂ τ : ℝ) => τ ^ α * rexp (-(π * b * y₂ ^ 2 * τ ^ 2)) * ‖g τ‖) := by
    refine Measurable.stronglyMeasurable ?_
    exact ((measurable_snd.pow_const α).mul (Real.measurable_exp.comp (by fun_prop))).mul (hgm.comp measurable_snd).norm
  exact (h.integral_prod_right (ν := μ0)).measurable

theorem integral_norm_F3_y (hb : 0 < b) (s : ℂ) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
    ∫ y in Ioi (0:ℝ), ‖F3 b p g K s (y, y₁, y₂)‖ =
      (y₁ ^ (p.re - (s.re - 2) - 1) * rexp (-(π * (y₁ ^ 2)⁻¹))) *
        (y₂ ^ (s.re - 2 + 1) * ‖K y₂‖ * Tn b g (s.re - 2) y₂) := by
  have hc : 0 < y₂ / y₁ := div_pos hy₂ hy₁
  have key := integral_comp_mul_left_Ioi (fun y : ℝ => ‖F3 b p g K s (y, y₁, y₂)‖) 0 hc
  rw [mul_zero] at key
  have key' : ∫ y in Ioi (0:ℝ), ‖F3 b p g K s (y, y₁, y₂)‖ =
      (y₂ / y₁) * ∫ τ in Ioi (0:ℝ), ‖F3 b p g K s (y₂ / y₁ * τ, y₁, y₂)‖ := by
    rw [key, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [key']
  have hpt : ∀ τ ∈ Ioi (0:ℝ), ‖F3 b p g K s (y₂ / y₁ * τ, y₁, y₂)‖ =
      (y₂ ^ (s.re - 2) * y₁ ^ (2 - s.re) * y₁ ^ p.re * ‖K y₂‖ * rexp (-(π * (y₁ ^ 2)⁻¹))) *
        (τ ^ (s.re - 2) * rexp (-(π * b * y₂ ^ 2 * τ ^ 2)) * ‖g τ‖) := by
    intro τ hτ
    have hτ' : (0:ℝ) < τ := hτ
    rw [F3_rescale hb s hy₁ hy₂ hτ', norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hy₂, Complex.norm_cpow_eq_rpow_re_of_pos hy₁,
      Complex.norm_cpow_eq_rpow_re_of_pos hy₁, Complex.norm_cpow_eq_rpow_re_of_pos hτ',
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _), abs_of_nonneg (Real.exp_nonneg _), Complex.sub_re, Complex.sub_re]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  unfold Tn
  have e1 : y₂ / y₁ * (y₂ ^ (s.re - 2) * y₁ ^ (2 - s.re) * y₁ ^ p.re) =
      y₁ ^ (p.re - (s.re - 2) - 1) * y₂ ^ (s.re - 2 + 1) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one y₁, Real.rpow_add hy₂, Real.rpow_one,
      show p.re - (s.re - 2) - 1 = p.re + (2 - s.re) + (-1) by ring, Real.rpow_add hy₁, Real.rpow_add hy₁]
    ring
  calc y₂ / y₁ * (y₂ ^ (s.re - 2) * y₁ ^ (2 - s.re) * y₁ ^ p.re * ‖K y₂‖ * rexp (-(π * (y₁ ^ 2)⁻¹)) *
        ∫ τ in Ioi (0:ℝ), τ ^ (s.re - 2) * rexp (-(π * b * y₂ ^ 2 * τ ^ 2)) * ‖g τ‖)
      = (y₂ / y₁ * (y₂ ^ (s.re - 2) * y₁ ^ (2 - s.re) * y₁ ^ p.re)) * ‖K y₂‖ * rexp (-(π * (y₁ ^ 2)⁻¹)) *
        ∫ τ in Ioi (0:ℝ), τ ^ (s.re - 2) * rexp (-(π * b * y₂ ^ 2 * τ ^ 2)) * ‖g τ‖ := by ring
    _ = _ := by rw [e1]; ring

theorem integrable_F3 (hb : 0 < b) (hgm : Measurable g) (hσ : 0 ≤ σ)
    (hg : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * (1 + t ^ (-σ)))
    (hKm : Measurable K)
    (hK : ∀ w : ℝ, 0 < w → ‖K w‖ ≤ CK * (w ^ N + w ^ (-N)) * rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2))))
    (s : ℂ) (hs1 : 1 + σ < s.re) (hs2 : p.re + 2 < s.re) :
    Integrable (F3 b p g K s) ((μ0).prod ((μ0).prod (μ0))) := by
  have hsσ : -1 < s.re - 2 - σ := by linarith
  rw [integrable_prod_iff' ((measurable_F3 hgm hKm s).aestronglyMeasurable)]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_pos_prod] with q hq
    exact integrableOn_F3_y hb hgm hg s hsσ hσ hq.1 hq.2
  ·
    have hA : Integrable (fun y₁ : ℝ => y₁ ^ (p.re - (s.re - 2) - 1) * rexp (-(π * (y₁ ^ 2)⁻¹))) μ0 :=
      integrableOn_rpow_mul_exp_neg_div_sq Real.pi_pos (by linarith)
    have hB : Integrable (fun y₂ : ℝ => y₂ ^ (s.re - 2 + 1) * ‖K y₂‖ * Tn b g (s.re - 2) y₂) μ0 := by
      set k₁ : ℝ := C * ((π * b) ^ (-(s.re - 2 + 1) / 2) * ((1 / 2) * Real.Gamma ((s.re - 2 + 1) / 2))) with hk₁
      set k₂ : ℝ := C * ((π * b) ^ (-(s.re - 2 - σ + 1) / 2) * ((1 / 2) * Real.Gamma ((s.re - 2 - σ + 1) / 2))) with hk₂
      have hdom : Integrable (fun w : ℝ => k₁ * (‖K w‖ * w ^ (0:ℝ)) + k₂ * (‖K w‖ * w ^ σ)) μ0 :=
        ((integrable_normK_mul_rpow hb hKm hK 0).const_mul k₁).add ((integrable_normK_mul_rpow hb hKm hK σ).const_mul k₂)
      refine Integrable.mono' hdom ?_ ?_
      · exact (((measurable_id.pow_const _).mul hKm.norm).mul (measurable_Tn hgm _)).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun y₂ (hy₂ : 0 < y₂) => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hy₂.le _) (norm_nonneg _)) (Tn_nonneg _ _)),
          Real.rpow_zero, mul_one]
        have h := rpow_mul_Tn_le hb hgm hg (α := s.re - 2) hsσ hσ hy₂
        rw [← hk₁, ← hk₂] at h
        calc y₂ ^ (s.re - 2 + 1) * ‖K y₂‖ * Tn b g (s.re - 2) y₂ = ‖K y₂‖ * (y₂ ^ (s.re - 2 + 1) * Tn b g (s.re - 2) y₂) := by ring
          _ ≤ ‖K y₂‖ * (k₁ + k₂ * y₂ ^ σ) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
          _ = k₁ * ‖K y₂‖ + k₂ * (‖K y₂‖ * y₂ ^ σ) := by ring
    have hAB := hA.mul_prod hB
    refine hAB.congr ?_
    filter_upwards [ae_pos_prod] with q hq
    exact (integral_norm_F3_y hb s hq.1 hq.2).symm

def Lk (b : ℝ) (g K : ℝ → ℂ) (s : ℂ) (q : ℝ × ℝ) : ℂ :=
  K q.1 * (((q.2 : ℝ) : ℂ) ^ (s - 2) * (rexp (-(π * b * q.2 ^ 2)) : ℂ) * g (q.2 / q.1))

theorem integrable_Lk (hb : 0 < b) (hgm : Measurable g) (hσ : 0 ≤ σ)
    (hg : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * (1 + t ^ (-σ)))
    (hKm : Measurable K)
    (hK : ∀ w : ℝ, 0 < w → ‖K w‖ ≤ CK * (w ^ N + w ^ (-N)) * rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2))))
    (s : ℂ) (hs1 : 1 + σ < s.re) :
    Integrable (Lk b g K s) ((μ0).prod (μ0)) := by
  have hB : 0 < π * b := by positivity
  have hdom : Integrable (fun q : ℝ × ℝ => C * (‖K q.1‖ * q.1 ^ (0:ℝ)) * (q.2 ^ (s.re - 2) * rexp (-(π * b) * q.2 ^ 2)) +
      C * (‖K q.1‖ * q.1 ^ σ) * (q.2 ^ (s.re - 2 - σ) * rexp (-(π * b) * q.2 ^ 2))) ((μ0).prod (μ0)) :=
    (((integrable_normK_mul_rpow hb hKm hK 0).const_mul C).mul_prod
        (integrableOn_rpow_mul_exp_neg_mul_sq hB (by linarith))).add
      (((integrable_normK_mul_rpow hb hKm hK σ).const_mul C).mul_prod
        (integrableOn_rpow_mul_exp_neg_mul_sq hB (by linarith)))
  refine Integrable.mono' hdom ?_ ?_
  · unfold Lk
    exact ((hKm.comp measurable_fst).mul ((((Complex.measurable_ofReal.comp measurable_snd).pow_const _).mul
      (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (by fun_prop)))).mul
      (hgm.comp (measurable_snd.div measurable_fst)))).aestronglyMeasurable
  · filter_upwards [ae_pos_prod] with q hq
    obtain ⟨w, σ'⟩ := q
    obtain ⟨hw, hσ'⟩ := hq
    simp only at hw hσ' ⊢
    rw [Lk, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hσ', Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _), Complex.sub_re, show (2 : ℂ).re = 2 by norm_num, Real.rpow_zero, mul_one]
    have hgb := hg (σ' / w) (div_pos hσ' hw)
    rw [Real.div_rpow hσ'.le hw.le, Real.rpow_neg hw.le, div_inv_eq_mul] at hgb
    have hE : 0 ≤ rexp (-(π * b * σ' ^ 2)) := Real.exp_nonneg _
    have h0 : 0 ≤ ‖K w‖ * (σ' ^ (s.re - 2) * rexp (-(π * b * σ' ^ 2))) :=
      mul_nonneg (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hσ'.le _) hE)
    have hC := C_nonneg hg
    calc ‖K w‖ * (σ' ^ (s.re - 2) * rexp (-(π * b * σ' ^ 2)) * ‖g (σ' / w)‖)
        = ‖K w‖ * (σ' ^ (s.re - 2) * rexp (-(π * b * σ' ^ 2))) * ‖g (σ' / w)‖ := by ring
      _ ≤ ‖K w‖ * (σ' ^ (s.re - 2) * rexp (-(π * b * σ' ^ 2))) * (C * (1 + σ' ^ (-σ) * w ^ σ)) :=
        mul_le_mul_of_nonneg_left hgb h0
      _ = C * (‖K w‖ * 1) * (σ' ^ (s.re - 2) * rexp (-(π * b) * σ' ^ 2)) +
          C * (‖K w‖ * w ^ σ) * (σ' ^ (s.re - 2) * σ' ^ (-σ) * rexp (-(π * b) * σ' ^ 2)) := by ring_nf
      _ = _ := by rw [← Real.rpow_add hσ', ← sub_eq_add_neg, mul_one]

theorem integral_Lk_w (s : ℂ) (H : ℝ → ℂ)
    (hH : H = fun σ' => (rexp (-(π * b * σ' ^ 2)) : ℂ) * ∫ w in Ioi (0 : ℝ), g (σ' / w) * K w) (σ' : ℝ) :
    ∫ w in Ioi (0:ℝ), Lk b g K s (w, σ') = ((σ' : ℝ) : ℂ) ^ (s - 1 - 1) • H σ' := by
  rw [hH, smul_eq_mul, show s - 1 - 1 = s - 2 by ring]
  simp only [Lk]
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  ring

theorem main (hb : 0 < b) (hgm : Measurable g) (hσ : 0 ≤ σ)
    (hg : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * (1 + t ^ (-σ)))
    (hKm : Measurable K)
    (hK : ∀ w : ℝ, 0 < w → ‖K w‖ ≤ CK * (w ^ N + w ^ (-N)) * rexp (-(π * ((w ^ 2)⁻¹ + b * w ^ 2))))
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (rexp (-(π * b * σ' ^ 2)) : ℂ) * ∫ w in Ioi (0 : ℝ), g (σ' / w) * K w)
    (s : ℂ) (hs1 : 1 + σ < s.re) (hs2 : p.re + 2 < s.re) :
    MellinConvergent H (s - 1) ∧
      ∫ y in Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (s - 2) *
          ∫ y₁ in Ioi (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((y₁ : ℝ) : ℂ) ^ p * K y₂ * (rexp (-(π * ((y₁ ^ 2)⁻¹ + b * y ^ 2 * y₁ ^ 2))) : ℂ) * g (y * y₁ / y₂) =
        (1 / 2 : ℂ) * Complex.Gammaℝ (s - p - 2) * mellin H (s - 1) := by
  have hInt := integrable_F3 hb hgm hσ hg hKm hK s hs1 hs2
  have hL := integrable_Lk hb hgm hσ hg hKm hK s hs1

  have hMC : MellinConvergent H (s - 1) := by
    have h := hL.integral_prod_right
    refine (h.congr (ae_of_all _ fun σ' => integral_Lk_w s H hH σ')).mono_measure le_rfl
  refine ⟨hMC, ?_⟩

  have hB' : ∫ y₂ in Ioi (0:ℝ), ((y₂ : ℂ) ^ (s - 1) * K y₂ *
      ∫ τ in Ioi (0:ℝ), (τ : ℂ) ^ (s - 2) * (rexp (-(π * b * y₂ ^ 2 * τ ^ 2)) : ℂ) * g τ) = mellin H (s - 1) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y₂ (hy₂ : 0 < y₂) => inner_tau_eq hb s hy₂)]
    have h1 : ∀ w : ℝ, K w * ∫ σ' in Ioi (0:ℝ), (σ' : ℂ) ^ (s - 2) * (rexp (-(π * b * σ' ^ 2)) : ℂ) * g (σ' / w) =
        ∫ σ' in Ioi (0:ℝ), Lk b g K s (w, σ') := by
      intro w; rw [← integral_const_mul]; rfl
    simp_rw [h1]
    rw [integral_integral_swap (by simpa [Function.uncurry_def] using hL)]
    rw [mellin]
    exact integral_congr_ae (ae_of_all _ fun σ' => integral_Lk_w s H hH σ')

  have hA' : ∫ y₁ in Ioi (0:ℝ), (y₁ : ℂ) ^ (p - s + 1) * (rexp (-(π * (y₁ ^ 2)⁻¹)) : ℂ) =
      (1 / 2 : ℂ) * Complex.Gammaℝ (s - p - 2) := by
    rw [← integral_cpow_mul_exp_neg_pi_div_sq (z := s - p - 2) (by simp; linarith)]
    refine setIntegral_congr_fun measurableSet_Ioi fun y₁ _ => ?_
    rw [show -(s - p - 2) - 1 = p - s + 1 by ring]

  have step1 : ∀ y : ℝ, ((y : ℝ) : ℂ) ^ (s - 2) *
      ∫ y₁ in Ioi (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
        ((y₁ : ℝ) : ℂ) ^ p * K y₂ * (rexp (-(π * ((y₁ ^ 2)⁻¹ + b * y ^ 2 * y₁ ^ 2))) : ℂ) * g (y * y₁ / y₂) =
      ∫ y₁ in Ioi (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ), F3 b p g K s (y, y₁, y₂) := by
    intro y
    rw [← integral_const_mul]
    congr 1
    funext y₁
    rw [← integral_const_mul]
    rfl
  simp_rw [step1]
  have step2 : ∀ᵐ y : ℝ ∂(μ0), ∫ y₁ in Ioi (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ), F3 b p g K s (y, y₁, y₂) =
      ∫ q : ℝ × ℝ, F3 b p g K s (y, q) ∂((μ0).prod (μ0)) := by
    filter_upwards [hInt.prod_right_ae] with y hy
    exact (integral_prod (fun q : ℝ × ℝ => F3 b p g K s (y, q)) hy).symm
  rw [integral_congr_ae step2]
  rw [integral_integral_swap (f := fun (y : ℝ) (q : ℝ × ℝ) => F3 b p g K s (y, q))
    (by simpa [Function.uncurry_def] using hInt)]
  have step3 : ∀ᵐ q : ℝ × ℝ ∂((μ0).prod (μ0)), ∫ y in Ioi (0:ℝ), F3 b p g K s (y, q) =
      ((((q.1 : ℝ)) : ℂ) ^ (p - s + 1) * (rexp (-(π * (q.1 ^ 2)⁻¹)) : ℂ)) *
      ((((q.2 : ℝ)) : ℂ) ^ (s - 1) * K q.2 *
        ∫ τ in Ioi (0:ℝ), (τ : ℂ) ^ (s - 2) * (rexp (-(π * b * q.2 ^ 2 * τ ^ 2)) : ℂ) * g τ) := by
    filter_upwards [ae_pos_prod] with q hq
    exact inner_y_eq hb s hq.1 hq.2
  rw [integral_congr_ae step3,
    integral_prod_mul (μ := μ0) (ν := μ0)
      (fun y₁ : ℝ => ((y₁ : ℂ) ^ (p - s + 1) * (rexp (-(π * (y₁ ^ 2)⁻¹)) : ℂ)))
      (fun y₂ : ℝ => ((y₂ : ℂ) ^ (s - 1) * K y₂ *
        ∫ τ in Ioi (0:ℝ), (τ : ℂ) ^ (s - 2) * (rexp (-(π * b * y₂ ^ 2 * τ ^ 2)) : ℂ) * g τ)),
    hA', hB']

end Main

end Z0RC

end

open Z0RC in
theorem solution
    (b : ℝ) (hb : 0 < b) (p : ℂ)
    (g : ℝ → ℂ) (hgm : Measurable g) (C σ : ℝ) (hσ : 0 ≤ σ)
    (hg : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * (1 + t ^ (-σ)))
    (K : ℝ → ℂ) (hKm : Measurable K) (CK N : ℝ)
    (hK : ∀ w : ℝ, 0 < w → ‖K w‖ ≤ CK * (w ^ N + w ^ (-N)) * Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + b * w ^ 2))))
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * b * σ' ^ 2)) : ℂ) * ∫ w in Ioi (0 : ℝ), g (σ' / w) * K w) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun q : ℝ × ℝ × ℝ =>
          ((q.1 : ℝ) : ℂ) ^ (s - 2) * (((q.2.1 : ℝ) : ℂ) ^ p * K q.2.2 *
            (Real.exp (-(Real.pi * ((q.2.1 ^ 2)⁻¹ + b * q.1 ^ 2 * q.2.1 ^ 2))) : ℂ) * g (q.1 * q.2.1 / q.2.2)))
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) ∧
      MellinConvergent H (s - 1) ∧
      ∫ y in Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (s - 2) *
          ∫ y₁ in Ioi (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
            ((y₁ : ℝ) : ℂ) ^ p * K y₂ * (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + b * y ^ 2 * y₁ ^ 2))) : ℂ) * g (y * y₁ / y₂) =
        (1 / 2 : ℂ) * Complex.Gammaℝ (s - p - 2) * mellin H (s - 1) := by
  refine ⟨max (1 + σ) (p.re + 2), fun s hs => ?_⟩
  have hs1 : 1 + σ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs2 : p.re + 2 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  have hI := integrable_F3 (p := p) hb hgm hσ hg hKm hK s hs1 hs2
  obtain ⟨hM, hE⟩ := main hb hgm hσ hg hKm hK H hH s hs1 hs2
  exact ⟨hI, hM, hE⟩

#print axioms solution

end S_LanglandsTunnell_exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin
end P2MW
export P2MW.S_LanglandsTunnell_exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin (solution)
