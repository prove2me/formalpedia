-- Prove2me | solution 1 for LanglandsTunnell.setIntegral_oneSided_torusPair_eq_setIntegral_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/979d4aaa-3c9c-59b0-9bda-e45417d67f55

import Mathlib
import Theorems.Thm_MeasureTheory_setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div
import Theorems.Thm_MeasureTheory_integrable_mul_comp_neg_div_div_of_integrable_prod_Iio_prod_Ioi
import Theorems.Thm_MeasureTheory_integral_integral_integral_comm_of_integrable_prod_prod
import Theorems.Thm_MeasureTheory_setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_setIntegral_oneSided_torusPair_eq_setIntegral_fiber

set_option autoImplicit false

open MeasureTheory Set

namespace OSR9

theorem ofReal_cpow_eq_exp (x : ℝ) (hx : 0 < x) (w : ℂ) :
    ((x : ℝ) : ℂ) ^ w = Complex.exp (w * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), ← Complex.ofReal_log hx.le, mul_comm]

theorem ofReal_eq_exp_log (x : ℝ) (hx : 0 < x) : ((x : ℝ) : ℂ) = Complex.exp ((Real.log x : ℝ) : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log hx]

theorem pointwise (α β γ : ℂ) (g : ℝ → ℂ) (Z : ℝ → ℝ → ℝ → ℂ) (F Ft : ℝ × ℝ × ℝ → ℂ)
    (hF : ∀ t y₁ y₂ : ℝ, F (t, y₁, y₂) =
      ((t : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
          ((|y₁| : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
          g (t * |y₁| / y₂) *
          Z y₁⁻¹ y₂⁻¹ (t * y₁))
    (hFt : ∀ t u v : ℝ, Ft (t, u, v) = ((u / (t * v ^ 2) : ℝ) : ℂ) * F (t, -(u / t), u / v))
    (v σ w : ℝ) (hv : 0 < v) (hσ : 0 < σ) (hw : v / σ < w) :
    ((v ^ 2 / w ^ 3 : ℝ) : ℂ) * Ft (v * (σ * w - v) / w ^ 2, v / w, v) =
      g v * ((v : ℝ) : ℂ) ^ α *
        ((((σ * w - v : ℝ) : ℂ) ^ (α - β - 1)) * ((w : ℝ) : ℂ) ^ (-2 * α + β - γ - 2) *
          (Real.exp (-(Real.pi * (σ ^ 2 + w ^ 2))) : ℂ) *
          Z (-((σ * w - v) / w)) w (-(v / w))) := by
  have hw0 : 0 < w := lt_trans (div_pos hv hσ) hw
  have hD : 0 < σ * w - v := by
    have := (div_lt_iff₀ hσ).1 hw
    linarith [mul_comm σ w]
  rw [hFt, hF]
  have r1 : v / w / v = w⁻¹ := by field_simp
  have r2 : v / w / (v * (σ * w - v) / w ^ 2) = w / (σ * w - v) := by field_simp
  rw [r1, r2, abs_neg, abs_of_pos (div_pos hw0 hD)]
  have r3 : v / w / (v * (σ * w - v) / w ^ 2 * v ^ 2) = w / (v ^ 2 * (σ * w - v)) := by field_simp
  have r4 : v * (σ * w - v) / w ^ 2 * (w / (σ * w - v)) / w⁻¹ = v := by field_simp
  have r5 : (-(w / (σ * w - v)))⁻¹ = -((σ * w - v) / w) := by rw [inv_neg, inv_div]
  have r7 : v * (σ * w - v) / w ^ 2 * -(w / (σ * w - v)) = -(v / w) := by field_simp
  rw [r3, r4, r5, inv_inv, r7]

  have he : (Real.exp (-(2 * Real.pi * (v * (σ * w - v) / w ^ 2))) : ℂ) *
      (Real.exp (-(Real.pi * (((-(w / (σ * w - v))) ^ 2)⁻¹ +
        (v * (σ * w - v) / w ^ 2) ^ 2 * (-(w / (σ * w - v))) ^ 2 + (w⁻¹ ^ 2)⁻¹))) : ℂ) =
      (Real.exp (-(Real.pi * (σ ^ 2 + w ^ 2))) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    field_simp
    ring

  set a : ℝ := Real.log v with ha
  set b : ℝ := Real.log w with hb
  set c : ℝ := Real.log (σ * w - v) with hc
  have hT : 0 < v * (σ * w - v) / w ^ 2 := div_pos (mul_pos hv hD) (pow_pos hw0 2)
  have hJ1 : 0 < v ^ 2 / w ^ 3 := div_pos (pow_pos hv 2) (pow_pos hw0 3)
  have hJ2 : 0 < w / (v ^ 2 * (σ * w - v)) := div_pos hw0 (mul_pos (pow_pos hv 2) hD)
  have lT : Real.log (v * (σ * w - v) / w ^ 2) = a + c - 2 * b := by
    rw [Real.log_div (mul_pos hv hD).ne' (pow_pos hw0 2).ne', Real.log_mul hv.ne' hD.ne', Real.log_pow]
    push_cast; ring
  have lA : Real.log (w / (σ * w - v)) = b - c := Real.log_div hw0.ne' hD.ne'
  have lW : Real.log w⁻¹ = -b := Real.log_inv w
  have lJ1 : Real.log (v ^ 2 / w ^ 3) = 2 * a - 3 * b := by
    rw [Real.log_div (pow_pos hv 2).ne' (pow_pos hw0 3).ne', Real.log_pow, Real.log_pow]
    push_cast; ring
  have lJ2 : Real.log (w / (v ^ 2 * (σ * w - v))) = b - (2 * a + c) := by
    rw [Real.log_div hw0.ne' (mul_pos (pow_pos hv 2) hD).ne', Real.log_mul (pow_pos hv 2).ne' hD.ne', Real.log_pow]
    push_cast; ring
  have hp : ((v ^ 2 / w ^ 3 : ℝ) : ℂ) * ((w / (v ^ 2 * (σ * w - v)) : ℝ) : ℂ) *
      (((v * (σ * w - v) / w ^ 2 : ℝ) : ℂ) ^ α * ((w / (σ * w - v) : ℝ) : ℂ) ^ β * ((w⁻¹ : ℝ) : ℂ) ^ γ) =
      ((v : ℝ) : ℂ) ^ α * (((σ * w - v : ℝ) : ℂ) ^ (α - β - 1) * ((w : ℝ) : ℂ) ^ (-2 * α + β - γ - 2)) := by
    rw [ofReal_eq_exp_log _ hJ1, ofReal_eq_exp_log _ hJ2, ofReal_cpow_eq_exp _ hT, ofReal_cpow_eq_exp _ (div_pos hw0 hD),
      ofReal_cpow_eq_exp _ (inv_pos.2 hw0), ofReal_cpow_eq_exp _ hv, ofReal_cpow_eq_exp _ hD, ofReal_cpow_eq_exp _ hw0,
      lT, lA, lW, lJ1, lJ2, ← hc, ← ha, ← hb]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination
    ((Real.exp (-(2 * Real.pi * (v * (σ * w - v) / w ^ 2))) : ℂ) *
      (Real.exp (-(Real.pi * (((-(w / (σ * w - v))) ^ 2)⁻¹ +
        (v * (σ * w - v) / w ^ 2) ^ 2 * (-(w / (σ * w - v))) ^ 2 + (w⁻¹ ^ 2)⁻¹))) : ℂ) *
      g v * Z (-((σ * w - v) / w)) w (-(v / w))) * hp +
    (((v : ℝ) : ℂ) ^ α * (((σ * w - v : ℝ) : ℂ) ^ (α - β - 1) * ((w : ℝ) : ℂ) ^ (-2 * α + β - γ - 2)) *
      g v * Z (-((σ * w - v) / w)) w (-(v / w))) * he

end OSR9

theorem solution
    (α β γ : ℂ) (g : ℝ → ℂ) (hg : Measurable g) (B : ℝ → ℝ → ℝ → ℝ → ℂ)
    (hB : Measurable fun x : ℝ × ℝ × ℝ × ℝ => B x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hInt : Integrable (fun x : ℝ × ℝ × ℝ × ℝ =>
        ((x.1 : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * x.1)) : ℂ) *
          ((|x.2.1| : ℝ) : ℂ) ^ β * ((x.2.2.1 : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2.1 ^ 2)⁻¹))) : ℂ) *
          g (x.1 * |x.2.1| / x.2.2.1) *
          (B (x.2.1⁻¹) (x.2.2.1⁻¹) (x.1 * x.2.1) x.2.2.2 * (Real.exp (-(Real.pi * x.2.2.2 ^ 2)) : ℂ)))
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod volume)))) :
    ∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
        ((t : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
          ((|y₁| : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
          g (t * |y₁| / y₂) *
          (∫ z : ℝ, B y₁⁻¹ y₂⁻¹ (t * y₁) z * (Real.exp (-(Real.pi * z ^ 2)) : ℂ))
      = ∫ v in Ioi (0 : ℝ), g v * ((v : ℝ) : ℂ) ^ α *
          ∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
            (((σ * w - v : ℝ) : ℂ) ^ (α - β - 1)) * ((w : ℝ) : ℂ) ^ (-2 * α + β - γ - 2) *
              (Real.exp (-(Real.pi * (σ ^ 2 + w ^ 2))) : ℂ) *
              (∫ z : ℝ, B (-((σ * w - v) / w)) w (-(v / w)) z * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) := by

  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set μ' : Measure ℝ := volume.restrict (Iio (0 : ℝ)) with hμ'

  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ → ℝ → ℝ → ℂ,
      Z = fun a b c => ∫ z : ℝ, B a b c z * (Real.exp (-(Real.pi * z ^ 2)) : ℂ) := ⟨_, rfl⟩
  have hZ : ∀ a b c : ℝ, Z a b c = ∫ z : ℝ, B a b c z * (Real.exp (-(Real.pi * z ^ 2)) : ℂ) :=
    fun a b c => by rw [hZdef]
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ × ℝ × ℝ → ℂ, F = fun x =>
      ((x.1 : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * x.1)) : ℂ) *
          ((|x.2.1| : ℝ) : ℂ) ^ β * ((x.2.2 : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2 ^ 2)⁻¹))) : ℂ) *
          g (x.1 * |x.2.1| / x.2.2) *
          Z x.2.1⁻¹ x.2.2⁻¹ (x.1 * x.2.1) := ⟨_, rfl⟩
  have hF : ∀ t y₁ y₂ : ℝ, F (t, y₁, y₂) =
      ((t : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
          ((|y₁| : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
          g (t * |y₁| / y₂) *
          Z y₁⁻¹ y₂⁻¹ (t * y₁) := fun t y₁ y₂ => by rw [hFdef]
  obtain ⟨Ft, hFtdef⟩ : ∃ Ft : ℝ × ℝ × ℝ → ℂ, Ft = fun p : ℝ × ℝ × ℝ =>
      ((p.2.1 / (p.1 * p.2.2 ^ 2) : ℝ) : ℂ) * F (p.1, -(p.2.1 / p.1), p.2.1 / p.2.2) := ⟨_, rfl⟩
  have hFt : ∀ t u v : ℝ, Ft (t, u, v) = ((u / (t * v ^ 2) : ℝ) : ℂ) * F (t, -(u / t), u / v) :=
    fun t u v => by rw [hFtdef]

  simp only [← hZ]
  simp only [← hF]

  have step1 : ∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ), F (t, y₁, y₂) =
      ∫ t in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), Ft (t, u, v) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have e : ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ), F (t, y₁, y₂) =
        ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), ((u / (t * v ^ 2) : ℝ) : ℂ) * F (t, -(u / t), u / v) :=
      MeasureTheory.setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div
        (fun y₁ y₂ => F (t, y₁, y₂)) t ht
    rw [e]
    simp only [hFt]

  have hZm : Measurable fun q : ℝ × ℝ × ℝ => Z q.1 q.2.1 q.2.2 := by
    rw [hZdef]
    have hBm : Measurable fun p : (ℝ × ℝ × ℝ) × ℝ =>
        B p.1.1 p.1.2.1 p.1.2.2 p.2 * (Real.exp (-(Real.pi * p.2 ^ 2)) : ℂ) := by
      refine Measurable.mul ?_ (Complex.measurable_ofReal.comp (by measurability))
      exact hB.comp (by measurability :
        Measurable fun p : (ℝ × ℝ × ℝ) × ℝ => (p.1.1, p.1.2.1, p.1.2.2, p.2))
    exact (hBm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  have hFm : Measurable F := by
    rw [hFdef]
    have m1 : Measurable fun x : ℝ × ℝ × ℝ => ((x.1 : ℝ) : ℂ) ^ α :=
      (Complex.measurable_ofReal.comp measurable_fst).pow_const α
    have m2 : Measurable fun x : ℝ × ℝ × ℝ => (Real.exp (-(2 * Real.pi * x.1)) : ℂ) :=
      Complex.measurable_ofReal.comp (by measurability)
    have m3 : Measurable fun x : ℝ × ℝ × ℝ => ((|x.2.1| : ℝ) : ℂ) ^ β :=
      (Complex.measurable_ofReal.comp (by measurability)).pow_const β
    have m4 : Measurable fun x : ℝ × ℝ × ℝ => ((x.2.2 : ℝ) : ℂ) ^ γ :=
      (Complex.measurable_ofReal.comp (by measurability)).pow_const γ
    have m5 : Measurable fun x : ℝ × ℝ × ℝ =>
        (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2 ^ 2)⁻¹))) : ℂ) :=
      Complex.measurable_ofReal.comp (by measurability)
    have m6 : Measurable fun x : ℝ × ℝ × ℝ => g (x.1 * |x.2.1| / x.2.2) :=
      hg.comp (by measurability)
    have m7 : Measurable fun x : ℝ × ℝ × ℝ => Z x.2.1⁻¹ x.2.2⁻¹ (x.1 * x.2.1) :=
      hZm.comp (by measurability : Measurable fun x : ℝ × ℝ × ℝ => (x.2.1⁻¹, x.2.2⁻¹, x.1 * x.2.1))
    exact (((((m1.mul m2).mul m3).mul m4).mul m5).mul m6).mul m7
  have hFtm : Measurable Ft := by
    rw [hFtdef]
    refine Measurable.mul (Complex.measurable_ofReal.comp (by measurability)) ?_
    exact hFm.comp (by measurability : Measurable fun p : ℝ × ℝ × ℝ => (p.1, -(p.2.1 / p.1), p.2.1 / p.2.2))

  set G : ℝ × ℝ × ℝ × ℝ → ℂ := fun x : ℝ × ℝ × ℝ × ℝ =>
        ((x.1 : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * x.1)) : ℂ) *
          ((|x.2.1| : ℝ) : ℂ) ^ β * ((x.2.2.1 : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2.1 ^ 2)⁻¹))) : ℂ) *
          g (x.1 * |x.2.1| / x.2.2.1) *
          (B (x.2.1⁻¹) (x.2.2.1⁻¹) (x.1 * x.2.1) x.2.2.2 * (Real.exp (-(Real.pi * x.2.2.2 ^ 2)) : ℂ)) with hGdef
  let Φ : (ℝ × ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ × ℝ :=
    (MeasurableEquiv.prodAssoc).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.prodAssoc)
  have hΦ : MeasurePreserving (⇑Φ) ((μ.prod (μ'.prod μ)).prod volume) (μ.prod (μ'.prod (μ.prod volume))) :=
    ((MeasurePreserving.id μ).prod (measurePreserving_prodAssoc μ' μ volume)).comp
      (measurePreserving_prodAssoc μ (μ'.prod μ) volume)
  have hGΦ : Integrable (G ∘ ⇑Φ) ((μ.prod (μ'.prod μ)).prod volume) :=
    (hΦ.integrable_comp hInt.aestronglyMeasurable).2 hInt
  have hFint : Integrable F (μ.prod (μ'.prod μ)) := by
    refine (hGΦ.integral_prod_left).congr (Filter.Eventually.of_forall fun q => ?_)
    have e : ∀ z : ℝ, (G ∘ ⇑Φ) (q, z) =
        (((q.1 : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * q.1)) : ℂ) *
          ((|q.2.1| : ℝ) : ℂ) ^ β * ((q.2.2 : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * ((q.2.1 ^ 2)⁻¹ + q.1 ^ 2 * q.2.1 ^ 2 + (q.2.2 ^ 2)⁻¹))) : ℂ) *
          g (q.1 * |q.2.1| / q.2.2)) *
          (B (q.2.1⁻¹) (q.2.2⁻¹) (q.1 * q.2.1) z * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) := fun z => rfl
    simp only [e]
    rw [integral_const_mul, ← hZ, hFdef]

  have hT : Integrable Ft (μ.prod (μ.prod μ)) := by
    rw [hFtdef]
    exact MeasureTheory.integrable_mul_comp_neg_div_div_of_integrable_prod_Iio_prod_Ioi F hFm hFint
  have step2 : ∫ t in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), Ft (t, u, v) =
      ∫ v in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), Ft (t, u, v) :=
    MeasureTheory.integral_integral_integral_comm_of_integrable_prod_prod μ μ μ Ft hT

  have hT2 : Integrable (Ft ∘ ⇑(MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ)) ((μ.prod μ).prod μ) :=
    ((measurePreserving_prodAssoc μ μ μ).integrable_comp hT.aestronglyMeasurable).2 hT
  have hae : ∀ᵐ v ∂μ, Integrable (fun q : ℝ × ℝ => Ft (q.1, q.2, v)) (μ.prod μ) := by
    filter_upwards [hT2.prod_left_ae] with v hv
    exact hv
  have hmem : ∀ᵐ v ∂μ, v ∈ Ioi (0 : ℝ) := ae_restrict_mem measurableSet_Ioi

  rw [step1, step2]
  refine integral_congr_ae ?_
  filter_upwards [hae, hmem] with v hvint hv
  have hv0 : (0 : ℝ) < v := hv
  have hHm : Measurable (Function.uncurry fun t u => Ft (t, u, v)) :=
    hFtm.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hC : ∫ u in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), Ft (t, u, v) =
      ∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ), ((v ^ 2 / w ^ 3 : ℝ) : ℂ) * Ft (v * (σ * w - v) / w ^ 2, v / w, v) :=
    MeasureTheory.setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst
      (fun t u => Ft (t, u, v)) hHm hvint v hv0
  rw [hC, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun σ hσ => ?_
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  exact OSR9.pointwise α β γ g Z F Ft hF hFt v σ w hv0 hσ hw

end S_LanglandsTunnell_setIntegral_oneSided_torusPair_eq_setIntegral_fiber
end P2MW
export P2MW.S_LanglandsTunnell_setIntegral_oneSided_torusPair_eq_setIntegral_fiber (solution)
