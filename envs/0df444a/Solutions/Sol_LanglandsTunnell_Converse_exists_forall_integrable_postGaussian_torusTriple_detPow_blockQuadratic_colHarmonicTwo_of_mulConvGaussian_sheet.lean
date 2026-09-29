-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_forall_integrable_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/100ea8b5-270e-540f-aa6a-ed847caa95c2

import Mathlib
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory
open Set Real

noncomputable section

namespace PG0a

local notation "μ0" => Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))

def prof (p q : ℂ) (y r : ℝ) : ℂ :=
  ((r : ℂ) ^ p * (rexp (-(π * r ^ 2)) : ℂ)) * ((((y / r : ℝ)) : ℂ) ^ q * (rexp (-(π * (y / r) ^ 2)) : ℂ)) / (r : ℂ)

def G (p q : ℂ) (y : ℝ) : ℂ := (4 : ℂ) * ∫ r in Ioi (0:ℝ), prof p q y r

def Φ (p q A : ℂ) (lam : ℝ) (w : ℝ × ℝ) : ℂ := ((w.1 : ℝ) : ℂ) ^ A * prof p q (lam * w.1) w.2

theorem measurable_prof (p q : ℂ) : Measurable (Function.uncurry (prof p q)) := by
  unfold prof
  have h1 : Measurable fun w : ℝ × ℝ => ((w.2 : ℝ) : ℂ) ^ p := (Complex.measurable_ofReal.comp measurable_snd).pow_const _
  have h2 : Measurable fun w : ℝ × ℝ => (rexp (-(π * w.2 ^ 2)) : ℂ) := Complex.measurable_ofReal.comp (by fun_prop)
  have h3 : Measurable fun w : ℝ × ℝ => ((((w.1 / w.2 : ℝ)) : ℂ)) ^ q :=
    (Complex.measurable_ofReal.comp (measurable_fst.div measurable_snd)).pow_const _
  have h4 : Measurable fun w : ℝ × ℝ => (rexp (-(π * (w.1 / w.2) ^ 2)) : ℂ) :=
    Complex.measurable_ofReal.comp (Real.measurable_exp.comp ((((measurable_fst.div measurable_snd).pow_const 2).const_mul π).neg))
  have h5 : Measurable fun w : ℝ × ℝ => ((w.2 : ℝ) : ℂ) := Complex.measurable_ofReal.comp measurable_snd
  exact ((h1.mul h2).mul (h3.mul h4)).div h5

theorem measurable_Φ (p q A : ℂ) (lam : ℝ) : Measurable (Φ p q A lam) := by
  unfold Φ
  refine ((Complex.measurable_ofReal.comp measurable_fst).pow_const _).mul ?_
  exact (measurable_prof p q).comp ((measurable_fst.const_mul lam).prodMk measurable_snd)

theorem norm_Φ (p q A : ℂ) {lam : ℝ} (hlam : 0 < lam) {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    ‖Φ p q A lam (t, r)‖ =
      t ^ A.re * (r ^ p.re * rexp (-(π * r ^ 2)) * ((lam * t / r) ^ q.re * rexp (-(π * (lam * t / r) ^ 2))) / r) := by
  have hq : 0 < lam * t / r := div_pos (mul_pos hlam ht) hr
  simp only [Φ, prof]
  rw [norm_mul, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_cpow_eq_rpow_re_of_pos hq,
    Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _), abs_of_nonneg (Real.exp_nonneg _), abs_of_pos hr]

theorem ae_pos_prod : ∀ᵐ w : ℝ × ℝ ∂((μ0).prod (μ0)), 0 < w.1 ∧ 0 < w.2 := by
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with q hq
  exact ⟨hq.1, hq.2⟩

theorem integral_rpow_mul_exp_neg_mul_sq {B q : ℝ} (hB : 0 < B) (hq : -1 < q) :
    ∫ x in Ioi (0:ℝ), x ^ q * rexp (-B * x ^ 2) = B ^ (-(q + 1) / 2) * (1 / 2) * Real.Gamma ((q + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := q) (b := B) two_pos hq hB
  simp_rw [Real.rpow_two] at h
  exact h

theorem norm_Φ_eq (p q A : ℂ) {lam : ℝ} (hlam : 0 < lam) {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    ‖Φ p q A lam (t, r)‖ =
      (lam ^ q.re * r ^ (p.re - q.re - 1) * rexp (-(π * r ^ 2))) *
        (t ^ (A.re + q.re) * rexp (-(π * lam ^ 2 / r ^ 2) * t ^ 2)) := by
  rw [norm_Φ p q A hlam ht hr, Real.div_rpow (mul_pos hlam ht).le hr.le, Real.mul_rpow hlam.le ht.le, Real.rpow_add ht,
    show p.re - q.re - 1 = p.re + (-q.re) + (-1 : ℝ) by ring, Real.rpow_add hr, Real.rpow_add hr, Real.rpow_neg hr.le,
    Real.rpow_neg_one]
  have : rexp (-(π * (lam * t / r) ^ 2)) = rexp (-(π * lam ^ 2 / r ^ 2) * t ^ 2) := by congr 1; field_simp
  rw [this]
  field_simp

theorem integrable_Φ (p q A : ℂ) {lam : ℝ} (hlam : 0 < lam) (hp : -1 < A.re + p.re) (hq : -1 < A.re + q.re) :
    Integrable (Φ p q A lam) ((μ0).prod (μ0)) := by
  rw [integrable_prod_iff' ((measurable_Φ p q A lam).aestronglyMeasurable)]
  refine ⟨?_, ?_⟩
  ·
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr' : (0:ℝ) < r := hr
    have hB : 0 < π * lam ^ 2 / r ^ 2 := by positivity
    have hdom : IntegrableOn (fun t : ℝ => (lam ^ q.re * r ^ (p.re - q.re - 1) * rexp (-(π * r ^ 2))) *
        (t ^ (A.re + q.re) * rexp (-(π * lam ^ 2 / r ^ 2) * t ^ 2))) (Ioi 0) :=
      (integrableOn_rpow_mul_exp_neg_mul_sq hB hq).const_mul _
    refine Integrable.mono' hdom ((measurable_Φ p q A lam).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t (ht : 0 < t) => ?_)
    exact (norm_Φ_eq p q A hlam ht hr').le
  ·
    have hval : ∀ r : ℝ, 0 < r → ∫ t in Ioi (0:ℝ), ‖Φ p q A lam (t, r)‖ =
        (lam ^ q.re * ((π * lam ^ 2) ^ (-(A.re + q.re + 1) / 2) * ((1 / 2) * Real.Gamma ((A.re + q.re + 1) / 2)))) *
          (r ^ (A.re + p.re) * rexp (-(π * r ^ 2))) := by
      intro r hr
      have hB : 0 < π * lam ^ 2 / r ^ 2 := by positivity
      rw [setIntegral_congr_fun measurableSet_Ioi (fun t (ht : 0 < t) => norm_Φ_eq p q A hlam ht hr), integral_const_mul,
        integral_rpow_mul_exp_neg_mul_sq hB hq, Real.div_rpow (by positivity) (sq_nonneg r),
        show (r ^ 2 : ℝ) ^ (-(A.re + q.re + 1) / 2) = r ^ (-(A.re + q.re + 1)) by
          rw [show (r ^ 2 : ℝ) = r ^ (2:ℝ) by rw [Real.rpow_two], ← Real.rpow_mul hr.le]; congr 1; ring]
      have e1 : r ^ (p.re - q.re - 1) * (r ^ (-(A.re + q.re + 1)))⁻¹ = r ^ (A.re + p.re) := by
        rw [← Real.rpow_neg hr.le, neg_neg, ← Real.rpow_add hr]; congr 1; ring
      calc lam ^ q.re * r ^ (p.re - q.re - 1) * rexp (-(π * r ^ 2)) *
            ((π * lam ^ 2) ^ (-(A.re + q.re + 1) / 2) / r ^ (-(A.re + q.re + 1)) * (1 / 2) * Real.Gamma ((A.re + q.re + 1) / 2))
          = lam ^ q.re * ((π * lam ^ 2) ^ (-(A.re + q.re + 1) / 2) * ((1 / 2) * Real.Gamma ((A.re + q.re + 1) / 2))) *
            ((r ^ (p.re - q.re - 1) * (r ^ (-(A.re + q.re + 1)))⁻¹) * rexp (-(π * r ^ 2))) := by rw [div_eq_mul_inv]; ring
        _ = _ := by rw [e1]
    have hR : Integrable (fun r : ℝ => (lam ^ q.re * ((π * lam ^ 2) ^ (-(A.re + q.re + 1) / 2) *
        ((1 / 2) * Real.Gamma ((A.re + q.re + 1) / 2)))) * (r ^ (A.re + p.re) * rexp (-(π * r ^ 2)))) μ0 := by
      have := (integrableOn_rpow_mul_exp_neg_mul_sq Real.pi_pos hp).const_mul
        (lam ^ q.re * ((π * lam ^ 2) ^ (-(A.re + q.re + 1) / 2) * ((1 / 2) * Real.Gamma ((A.re + q.re + 1) / 2))))
      refine this.congr (ae_of_all _ fun r => ?_)
      simp only [neg_mul]
    refine hR.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (hval r hr).symm

theorem integrableOn_cpow_mul_G (p q A : ℂ) {lam : ℝ} (hlam : 0 < lam) (hp : -1 < A.re + p.re) (hq : -1 < A.re + q.re) :
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ A * G p q (lam * t)) (Ioi 0) := by
  have h := (integrable_Φ p q A hlam hp hq).integral_prod_left
  have h4 := h.const_mul (4 : ℂ)
  refine h4.congr (ae_of_all _ fun t => ?_)
  simp only [G, Φ]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
  congr 1; funext r; ring

theorem sheets (W G₀ G₁ : ℝ → ℂ)
    (h0 : ∀ t : ℝ, 0 < t → W t + (-1 : ℂ) ^ (0 : ZMod 2).val * W (-t) = (t : ℂ) * G₀ t)
    (h1 : ∀ t : ℝ, 0 < t → W t + (-1 : ℂ) ^ (1 : ZMod 2).val * W (-t) = (t : ℂ) * G₁ t)
    {t : ℝ} (ht : 0 < t) :
    W t = (t : ℂ) * (G₀ t + G₁ t) / 2 ∧ W (-t) = (t : ℂ) * (G₀ t - G₁ t) / 2 := by
  have e0 := h0 t ht
  have e1 := h1 t ht
  rw [show (0 : ZMod 2).val = 0 from rfl, pow_zero, one_mul] at e0
  rw [show (1 : ZMod 2).val = 1 from rfl, pow_one, neg_one_mul] at e1
  constructor
  · linear_combination (e0 + e1) / 2
  · linear_combination (e0 - e1) / 2

theorem measurable_of_continuousOn_ne_zero {W : ℝ → ℂ} (hWc : ContinuousOn W {t : ℝ | t ≠ 0}) : Measurable W :=
  measurable_of_continuousOn_compl_singleton 0 (by rwa [Set.compl_singleton_eq])

theorem integrableOn_cpow_mul_W (p q : ℂ) (b : ZMod 2) (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    (A : ℂ) (hA : -1 < (A + 1).re + p.re ∧ -1 < (A + 1).re + q.re) :
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ A * W t) (Ioi 0) ∧
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ A * W (-t)) (Ioi 0) := by
  have hG : ∀ t : ℝ, 0 < t → W t + (-1 : ℂ) ^ b.val * W (-t) = (t : ℂ) * G p q (1 * t) := by
    intro t ht; rw [hW t ht, one_mul]; rfl
  have hsq : ((-1 : ℂ) ^ b.val) * ((-1 : ℂ) ^ b.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hWt : ∀ t : ℝ, 0 < t → W t = (t : ℂ) * G p q (1 * t) / 2 := by
    intro t ht
    have h := hG t ht
    rw [hWpar t, ← mul_assoc, hsq, one_mul] at h
    linear_combination h / 2
  have i0 := integrableOn_cpow_mul_G p q (A + 1) one_pos hA.1 hA.2
  have hmW : Measurable W := measurable_of_continuousOn_ne_zero hWc
  have hpt : ∀ t : ℝ, 0 < t →
      ((t : ℝ) : ℂ) ^ A * W t = ((t : ℝ) : ℂ) ^ (A + 1) * G p q (1 * t) / 2 := by
    intro t ht
    have hp : ((t : ℝ) : ℂ) ^ (A + 1) = ((t : ℝ) : ℂ) ^ A * (t : ℂ) := by
      rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 ht.ne'), Complex.cpow_one]
    rw [hWt t ht, hp]; ring
  have h1 : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ A * W t) (Ioi 0) := by
    refine Integrable.congr (i0.div_const 2) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t (ht : 0 < t) => ((hpt t ht)).symm)
  refine ⟨h1, ?_⟩
  refine Integrable.congr (h1.const_mul ((-1 : ℂ) ^ b.val)) ?_
  exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t (_ : 0 < t) => by
    show (-1 : ℂ) ^ b.val * (((t : ℝ) : ℂ) ^ A * W t) = ((t : ℝ) : ℂ) ^ A * W (-t)
    rw [hWpar t]; ring)

end PG0a

namespace PG0b

open LanglandsTunnell.Converse.ArchR PG0a

section Profile

variable {P₂ : RealArchParam} (D : ArchDatumR P₂)

def Fp (τ : ℝ) : ℂ := D.W (diagOne τ)

theorem continuous_diagOneCoords : Continuous fun τ : ℝ => Matrix.of.symm (ArchR.diagOne τ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [ArchR.diagOne, continuous_const, continuous_id']

theorem continuousOn_Fp : ContinuousOn (Fp D) {τ : ℝ | τ ≠ 0} := by
  have hW := D.smooth.continuousOn
  have hmap : MapsTo (fun τ : ℝ => Matrix.of.symm (ArchR.diagOne τ)) {τ : ℝ | τ ≠ 0} ArchR.glSet := by
    intro τ hτ
    show (Matrix.of (Matrix.of.symm (ArchR.diagOne τ))).det ≠ 0
    simpa [ArchR.diagOne, Matrix.det_fin_two] using hτ
  have h := hW.comp (continuous_diagOneCoords).continuousOn hmap
  refine h.congr (fun τ _ => ?_)
  simp [Fp, ArchR.asPi]

theorem measurable_Fp : Measurable (Fp D) :=
  measurable_of_continuousOn_compl_singleton 0 (by rw [Set.compl_singleton_eq]; exact continuousOn_Fp D)

theorem exists_bound_Fp : ∃ CF σF : ℝ, 0 ≤ CF ∧ 0 ≤ σF ∧ ∀ τ : ℝ, τ ≠ 0 → ‖Fp D τ‖ ≤ CF * (1 + |τ| ^ (-σF)) := by
  obtain ⟨C₁, hC₁⟩ := D.decay_top 0 0
  obtain ⟨C₂, σ₂, hC₂⟩ := D.decay_zero 0
  have hK1 : ArchR.IsK (1 : Matrix (Fin 2) (Fin 2) ℝ) := Submonoid.one_mem _
  have key : ∀ y : ℝ, ‖iteratedFDerivWithin ℝ 0 (ArchR.asPi D.W) ArchR.glSet (ArchR.diagOneMulCoords y 1)‖ = ‖Fp D y‖ := by
    intro y; rw [norm_iteratedFDerivWithin_zero]; simp [ArchR.asPi, ArchR.diagOneMulCoords, Fp]
  have h1 : ∀ y : ℝ, 1 ≤ |y| → ‖Fp D y‖ ≤ C₁ := by
    intro y hy; have := hC₁ y 1 hK1 hy; rw [key] at this; simpa using this
  have h2 : ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 → ‖Fp D y‖ ≤ C₂ * |y| ^ (-σ₂) := by
    intro y hy hy1; have := hC₂ y 1 hK1 hy hy1; rwa [key] at this
  have hC₁0 : 0 ≤ C₁ := le_trans (norm_nonneg _) (h1 1 (by simp))
  have hC₂0 : 0 ≤ C₂ := by
    have := h2 1 one_ne_zero (by simp)
    simp only [abs_one, Real.one_rpow, mul_one] at this
    exact le_trans (norm_nonneg _) this
  refine ⟨max C₁ C₂, max σ₂ 0, hC₁0.trans (le_max_left _ _), le_max_right _ _, fun τ hτ => ?_⟩
  have hM : 0 ≤ max C₁ C₂ := hC₁0.trans (le_max_left _ _)
  have hτp : 0 < |τ| := abs_pos.2 hτ
  have hr : 0 ≤ |τ| ^ (-max σ₂ 0) := Real.rpow_nonneg hτp.le _
  by_cases h : 1 ≤ |τ|
  · calc ‖Fp D τ‖ ≤ C₁ := h1 τ h
      _ ≤ max C₁ C₂ := le_max_left _ _
      _ ≤ max C₁ C₂ * (1 + |τ| ^ (-max σ₂ 0)) := le_mul_of_one_le_right hM (by linarith)
  · push Not at h
    calc ‖Fp D τ‖ ≤ C₂ * |τ| ^ (-σ₂) := h2 τ hτ h.le
      _ ≤ max C₁ C₂ * |τ| ^ (-max σ₂ 0) := by
          refine mul_le_mul (le_max_right _ _) ?_ (Real.rpow_nonneg hτp.le _) hM
          exact Real.rpow_le_rpow_of_exponent_ge hτp h.le (neg_le_neg (le_max_left _ _))
      _ ≤ max C₁ C₂ * (1 + |τ| ^ (-max σ₂ 0)) := by nlinarith

end Profile

theorem signShift_re_nonneg (e : ZMod 2) : 0 ≤ (signShift e).re := by
  unfold signShift; split_ifs <;> simp

theorem norm_psi (x : ℝ) : ‖ArchR.psi x‖ = 1 := by
  rw [ArchR.psi, Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

theorem continuous_psi : Continuous ArchR.psi := by
  unfold ArchR.psi; fun_prop

theorem integrable_X {y₁ : ℝ} (hy₁ : y₁ ≠ 0) (c₀ c₁ : ℂ) :
    Integrable (fun x : ℝ => ((Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (c₀ + c₁ * Complex.I * (x : ℂ)))) := by
  have hb : 0 < Real.pi / y₁ ^ 2 := by positivity
  have hG : ∀ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℝ) = Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2) := by
    intro x; congr 1; ring
  refine Integrable.mono' (((integrable_exp_neg_mul_sq hb).const_mul ‖c₀‖).add
    ((integrable_mul_exp_neg_mul_sq hb).norm.const_mul ‖c₁‖)) ?_ (ae_of_all _ fun x => ?_)
  · exact ((Complex.continuous_ofReal.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · simp only [Pi.add_apply]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), hG, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.exp_nonneg _)]
    have h1x : ‖c₀ + c₁ * Complex.I * (x : ℂ)‖ ≤ ‖c₀‖ + ‖c₁‖ * |x| := by
      calc ‖c₀ + c₁ * Complex.I * (x : ℂ)‖ ≤ ‖c₀‖ + ‖c₁ * Complex.I * (x : ℂ)‖ := norm_add_le _ _
        _ = ‖c₀‖ + ‖c₁‖ * |x| := by rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hE : 0 ≤ Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2) := Real.exp_nonneg _
    calc Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2) * ‖c₀ + c₁ * Complex.I * (x : ℂ)‖
        ≤ Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2) * (‖c₀‖ + ‖c₁‖ * |x|) := mul_le_mul_of_nonneg_left h1x hE
      _ = ‖c₀‖ * Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2) + ‖c₁‖ * (|x| * Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2)) := by ring

theorem integrableOn_Iic_of_comp_neg (F : ℝ → ℂ) (hF : IntegrableOn (fun t => F (-t)) (Ioi 0)) : IntegrableOn F (Iic 0) := by
  have h' : IntegrableOn F (Iio 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simpa only [Function.comp_def, neg_preimage, neg_Iio, neg_zero] using hF
  exact h'.congr_set_ae Iio_ae_eq_Iic.symm

end PG0b

namespace PG0c

open LanglandsTunnell.Converse.ArchR PG0a PG0b

theorem exp_neg_le_factorial_mul_inv_pow (k : ℕ) {x : ℝ} (hx : 0 < x) :
    rexp (-x) ≤ (k.factorial : ℝ) * (x ^ k)⁻¹ := by
  have h : x ^ k / k.factorial ≤ rexp x := Real.pow_div_factorial_le_exp x hx.le k
  have hk : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hxk : 0 < x ^ k := pow_pos hx k
  have h2 : x ^ k ≤ k.factorial * rexp x := (div_le_iff₀' hk).1 h
  calc rexp (-x) = (x ^ k)⁻¹ * (x ^ k * rexp (-x)) := by field_simp
    _ ≤ (x ^ k)⁻¹ * (k.factorial * rexp x * rexp (-x)) := by gcongr
    _ = (k.factorial : ℝ) * (x ^ k)⁻¹ := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one, mul_comm]

theorem integrableOn_Iic_of_comp_neg' {E : Type*} [NormedAddCommGroup E] (F : ℝ → E)
    (hF : IntegrableOn (fun t => F (-t)) (Ioi 0)) : IntegrableOn F (Iic 0) := by
  have h' : IntegrableOn F (Iio 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simpa only [Function.comp_def, neg_preimage, neg_Iio, neg_zero] using hF
  exact h'.congr_set_ae Iio_ae_eq_Iic.symm

theorem integrable_of_Ioi_of_comp_neg {E : Type*} [NormedAddCommGroup E] (F : ℝ → E)
    (h1 : IntegrableOn F (Ioi 0)) (h2 : IntegrableOn (fun t => F (-t)) (Ioi 0)) : Integrable F := by
  have h := (integrableOn_Iic_of_comp_neg' F h2).union h1
  rwa [Iic_union_Ioi, integrableOn_univ] at h

theorem integrable_T (p q : ℂ) (b : ZMod 2) (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    (A : ℝ) (hA : -1 < A + 1 + p.re ∧ -1 < A + 1 + q.re) :
    Integrable (fun t : ℝ => |t| ^ A * ‖W t‖) := by
  have hA' : -1 < ((A : ℂ) + 1).re + p.re ∧ -1 < ((A : ℂ) + 1).re + q.re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.one_re] using hA
  obtain ⟨i1, i2⟩ := integrableOn_cpow_mul_W p q b W hWc hW hWpar (A : ℂ) hA'
  have e : ∀ t : ℝ, 0 < t → ∀ z : ℂ, ‖((t : ℝ) : ℂ) ^ (A : ℂ) * z‖ = |t| ^ A * ‖z‖ := by
    intro t ht z; rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.ofReal_re, abs_of_pos ht]
  refine integrable_of_Ioi_of_comp_neg _ ?_ ?_
  · exact IntegrableOn.congr_fun i1.norm (fun t ht => e t ht _) measurableSet_Ioi
  · refine IntegrableOn.congr_fun i2.norm (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    show ‖((t : ℝ) : ℂ) ^ (A : ℂ) * W (-t)‖ = |(-t)| ^ A * ‖W (-t)‖
    rw [abs_neg]; exact e t ht _

theorem integrableOn_Z {g : ℝ} (hg : g < -1) :
    IntegrableOn (fun y : ℝ => y ^ g * rexp (-(π / y ^ 2))) (Ioi 0) := by
  have hm : -1 < -g - 2 := by linarith
  have h0 : IntegrableOn (fun x : ℝ => x ^ (-g - 2) * rexp (-π * x ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq Real.pi_pos hm
  have h1 := (integrableOn_Ioi_comp_rpow_iff' (fun x : ℝ => x ^ (-g - 2) * rexp (-π * x ^ 2))
    (show (-1 : ℝ) ≠ 0 by norm_num)).2 h0
  refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy' : (0 : ℝ) < y := hy
  simp only [smul_eq_mul]
  rw [← Real.rpow_mul hy'.le, ← mul_assoc, ← Real.rpow_add hy', Real.rpow_neg_one, inv_pow]
  rw [show (-1 - 1 + -1 * (-g - 2) : ℝ) = g by ring, neg_mul, div_eq_mul_inv]

theorem integrable_Y {b : ℝ} (hb : b < -1) :
    Integrable (fun y : ℝ => |y| ^ b * rexp (-(π / y ^ 2))) := by
  refine integrable_of_Ioi_of_comp_neg _ ?_ ?_
  · exact (integrableOn_Z hb).congr_fun (fun y (hy : (0:ℝ) < y) => by rw [abs_of_pos hy]) measurableSet_Ioi
  · exact (integrableOn_Z hb).congr_fun (fun y (hy : (0:ℝ) < y) => by
      simp only [abs_neg, neg_sq, abs_of_pos hy]) measurableSet_Ioi

local notation "μ3" => Measure.prod (volume : Measure ℝ) (Measure.prod (volume : Measure ℝ) (Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))))

theorem integrable_triple {φ : ℝ → ℝ} (hφ : Integrable φ) {b g : ℝ} (hb : b < -1) (hg : g < -1) :
    Integrable (fun q : ℝ × ℝ × ℝ =>
      φ q.1 * ((|q.2.1| ^ b * rexp (-(π / q.2.1 ^ 2))) * (q.2.2 ^ g * rexp (-(π / q.2.2 ^ 2))))) μ3 :=
  hφ.mul_prod ((integrable_Y hb).mul_prod (integrableOn_Z hg))

theorem ae_good : ∀ᵐ q : ℝ × ℝ × ℝ ∂μ3, q.1 ≠ 0 ∧ q.2.1 ≠ 0 ∧ 0 < q.2.2 := by
  have h0 : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ 0 := by
    have : ({0}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.2 (measure_singleton 0)
    filter_upwards [this] with x hx
    simpa using hx
  have h2 : ∀ᵐ y : ℝ ∂((volume : Measure ℝ).restrict (Ioi 0)), 0 < y := ae_restrict_mem measurableSet_Ioi
  have hB : ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))), p.1 ≠ 0 ∧ 0 < p.2 :=
    ((Measure.quasiMeasurePreserving_fst).ae h0).and ((Measure.quasiMeasurePreserving_snd).ae h2)
  exact ((Measure.quasiMeasurePreserving_fst).ae h0).and ((Measure.quasiMeasurePreserving_snd).ae hB)

def M (W F : ℝ → ℂ) (a α β γ : ℝ) (q : ℝ × ℝ × ℝ) : ℝ :=
  (|q.1| ^ α * ‖W q.1‖ * ‖F (a * q.1 * q.2.1 / q.2.2)‖ * rexp (-(π * ((a * q.1) ^ 2 * q.2.1 ^ 2)))) *
    ((|q.2.1| ^ β * rexp (-(π / q.2.1 ^ 2))) * (q.2.2 ^ γ * rexp (-(π / q.2.2 ^ 2))))

theorem measurable_M {W F : ℝ → ℂ} (hmW : Measurable W) (hmF : Measurable F) (a α β γ : ℝ) :
    Measurable (M W F a α β γ) := by
  unfold M
  have h1 : Measurable fun q : ℝ × ℝ × ℝ => ‖W q.1‖ := (hmW.comp measurable_fst).norm
  have h2 : Measurable fun q : ℝ × ℝ × ℝ => ‖F (a * q.1 * q.2.1 / q.2.2)‖ :=
    (hmF.comp (((measurable_fst.const_mul a).mul (measurable_fst.comp measurable_snd)).div
      (measurable_snd.comp measurable_snd))).norm
  have h3 : Measurable fun q : ℝ × ℝ × ℝ => |q.1| ^ α := (measurable_fst.abs).pow_const _
  have h4 : Measurable fun q : ℝ × ℝ × ℝ => rexp (-(π * ((a * q.1) ^ 2 * q.2.1 ^ 2))) := by fun_prop
  have h5 : Measurable fun q : ℝ × ℝ × ℝ => |q.2.1| ^ β := ((measurable_fst.comp measurable_snd).abs).pow_const _
  have h6 : Measurable fun q : ℝ × ℝ × ℝ => rexp (-(π / q.2.1 ^ 2)) := by fun_prop
  have h7 : Measurable fun q : ℝ × ℝ × ℝ => q.2.2 ^ γ := (measurable_snd.comp measurable_snd).pow_const _
  have h8 : Measurable fun q : ℝ × ℝ × ℝ => rexp (-(π / q.2.2 ^ 2)) := by fun_prop
  exact (((h3.mul h1).mul h2).mul h4).mul ((h5.mul h6).mul (h7.mul h8))

theorem integrable_M (p q : ℂ) (b : ZMod 2) (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ p * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ q * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    (F : ℝ → ℂ) (hmF : Measurable F) (CF σF : ℝ) (hCF : 0 ≤ CF) (hσF : 0 ≤ σF)
    (hF : ∀ τ : ℝ, τ ≠ 0 → ‖F τ‖ ≤ CF * (1 + |τ| ^ (-σF)))
    {a : ℝ} (ha : a ≠ 0) (α β γ : ℝ) (k : ℕ)
    (hβ : β - 2 * k < -1) (hγ : γ + σF < -1)
    (hα : -1 < (α - 2 * k - σF) + 1 + p.re ∧ -1 < (α - 2 * k - σF) + 1 + q.re) :
    Integrable (M W F a α β γ) μ3 := by
  have hmW : Measurable W := measurable_of_continuousOn_ne_zero hWc
  set K : ℝ := (k.factorial : ℝ) * ((π * a ^ 2) ^ k)⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  have hα0 : -1 < (α - 2 * k) + 1 + p.re ∧ -1 < (α - 2 * k) + 1 + q.re := by
    constructor <;> linarith [hα.1, hα.2]
  have I1 := integrable_triple (integrable_T p q b W hWc hW hWpar (α - 2 * k) hα0) hβ (by linarith : γ < -1)
  have I2 := integrable_triple (integrable_T p q b W hWc hW hWpar (α - 2 * k - σF) hα)
    (by linarith : β - 2 * k - σF < -1) hγ
  refine Integrable.mono' ((I1.const_mul (CF * K)).add (I2.const_mul (CF * K * |a| ^ (-σF))))
    (measurable_M hmW hmF a α β γ).aestronglyMeasurable ?_
  filter_upwards [ae_good] with q hq
  obtain ⟨t, y₁, y₂⟩ := q
  obtain ⟨ht, hy₁, hy₂⟩ := hq
  simp only at ht hy₁ hy₂
  simp only [Pi.add_apply]

  have hX : 0 < |t| := abs_pos.2 ht
  have hY : 0 < |y₁| := abs_pos.2 hy₁
  set X : ℝ := |t| with hXd
  set Y : ℝ := |y₁| with hYd
  have hw : 0 ≤ ‖W t‖ := norm_nonneg _
  have he₁ : 0 ≤ rexp (-(π / y₁ ^ 2)) := (Real.exp_pos _).le
  have he₂ : 0 ≤ rexp (-(π / y₂ ^ 2)) := (Real.exp_pos _).le

  have hE3 : rexp (-(π * ((a * t) ^ 2 * y₁ ^ 2))) ≤ K * (X ^ (-(2 * (k:ℝ))) * Y ^ (-(2 * (k:ℝ)))) := by
    have hx : 0 < π * ((a * t) ^ 2 * y₁ ^ 2) := by positivity
    refine (exp_neg_le_factorial_mul_inv_pow k hx).trans (le_of_eq ?_)
    have e1 : π * ((a * t) ^ 2 * y₁ ^ 2) = (π * a ^ 2) * (X * Y) ^ 2 := by
      rw [hXd, hYd, mul_pow, mul_pow, sq_abs, sq_abs]; ring
    rw [e1, mul_pow, ← pow_mul, mul_inv, hK, mul_assoc]
    congr 1
    rw [← Real.rpow_natCast (X * Y) (2 * k), ← Real.rpow_neg (mul_pos hX hY).le, Real.mul_rpow hX.le hY.le]
    push_cast; ring_nf

  have hnF : ‖F (a * t * y₁ / y₂)‖ ≤ CF + CF * |a| ^ (-σF) * (X ^ (-σF) * Y ^ (-σF) * y₂ ^ σF) := by
    have hτ : a * t * y₁ / y₂ ≠ 0 := div_ne_zero (mul_ne_zero (mul_ne_zero ha ht) hy₁) hy₂.ne'
    refine (hF _ hτ).trans (le_of_eq ?_)
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hy₂, Real.div_rpow (by positivity) hy₂.le,
      Real.mul_rpow (by positivity) hY.le, Real.mul_rpow (abs_nonneg a) hX.le, Real.rpow_neg hy₂.le,
      div_inv_eq_mul]
    ring

  have hL : M W F a α β γ (t, y₁, y₂) =
      (X ^ α * ‖W t‖ * (Y ^ β * rexp (-(π / y₁ ^ 2))) * (y₂ ^ γ * rexp (-(π / y₂ ^ 2)))) *
        rexp (-(π * ((a * t) ^ 2 * y₁ ^ 2))) * ‖F (a * t * y₁ / y₂)‖ := by
    simp only [M, hXd, hYd]; ring
  have hbase : 0 ≤ X ^ α * ‖W t‖ * (Y ^ β * rexp (-(π / y₁ ^ 2))) * (y₂ ^ γ * rexp (-(π / y₂ ^ 2))) := by
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by rw [hL]; positivity), hL]
  have step := mul_le_mul (mul_le_mul_of_nonneg_left hE3 hbase) hnF (norm_nonneg _) (by positivity)
  refine step.trans (le_of_eq ?_)
  have eX1 : X ^ (α - 2 * k) = X ^ α * X ^ (-(2 * (k:ℝ))) := by rw [sub_eq_add_neg, Real.rpow_add hX]
  have eX2 : X ^ (α - 2 * k - σF) = X ^ α * X ^ (-(2 * (k:ℝ))) * X ^ (-σF) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, Real.rpow_add hX, Real.rpow_add hX]
  have eY1 : Y ^ (β - 2 * k) = Y ^ β * Y ^ (-(2 * (k:ℝ))) := by rw [sub_eq_add_neg, Real.rpow_add hY]
  have eY2 : Y ^ (β - 2 * k - σF) = Y ^ β * Y ^ (-(2 * (k:ℝ))) * Y ^ (-σF) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, Real.rpow_add hY, Real.rpow_add hY]
  have eZ2 : y₂ ^ (γ + σF) = y₂ ^ γ * y₂ ^ σF := Real.rpow_add hy₂ _ _
  simp only [hXd, hYd] at eX1 eX2 eY1 eY2 ⊢
  rw [eX1, eX2, eY1, eY2, eZ2]
  ring

theorem norm_quasiChar (u : ℂ) (e : ZMod 2) {y : ℝ} (hy : y ≠ 0) : ‖ArchR.quasiChar u e y‖ = |y| ^ u.re := by
  unfold ArchR.quasiChar
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.2 hy)]
  by_cases h : e = 0
  · simp [h]
  · rcases lt_or_gt_of_ne hy with h' | h'
    · simp [h, sign_neg h']
    · simp [h, sign_pos h']

theorem measurable_sign_coe : Measurable (fun y : ℝ => (((SignType.sign y : SignType) : ℝ) : ℂ)) := by
  have : (fun y : ℝ => (((SignType.sign y : SignType) : ℝ) : ℂ)) =
      fun y => if 0 < y then (1 : ℂ) else if y < 0 then -1 else 0 := by
    funext y; rw [sign_apply]; split_ifs <;> simp
  rw [this]
  refine Measurable.ite measurableSet_Ioi measurable_const (Measurable.ite measurableSet_Iio measurable_const measurable_const)

theorem measurable_quasiChar (u : ℂ) (e : ZMod 2) : Measurable (ArchR.quasiChar u e) := by
  unfold ArchR.quasiChar
  refine ((Complex.measurable_ofReal.comp measurable_abs).pow_const _).mul ?_
  by_cases h : e = 0
  · simp only [h, if_true]; exact measurable_const
  · simp only [h, if_false]; exact measurable_sign_coe

end PG0c

open PG0a PG0b PG0c LanglandsTunnell.Converse.ArchR in
theorem solution
    (ν₁ ν₂ : ℂ) (b : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (u₀ cP : ℂ) (a₀ : ZMod 2) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun q : ℝ × ℝ × ℝ =>
        (ArchR.quasiChar u₀ a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) *
          ((((q.2.1 * q.2.2)⁻¹ : ℝ) : ℂ) ^ δ * ((|q.2.1 * q.2.2| : ℝ) : ℂ) *
            (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (q.2.2 : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) * ((|q.2.1| : ℝ) : ℂ)) *
          (W q.1 * D.W (ArchR.diagOne (a * q.1 * q.2.1 / q.2.2)) * (((|q.1| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.1 ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * q.1) ^ 2 * q.2.1 ^ 2))) : ℂ) * (((1 / q.2.1 ^ 2 - 1 / q.2.2 ^ 2 - a ^ 2 * q.1 ^ 2 * q.2.1 ^ 2 + 1 / (2 * Real.pi) + 2 * a * q.1 * q.2.1 / q.2.2 : ℝ)) : ℂ)))))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by
  obtain ⟨CF, σF, hCF, hσF, hbF⟩ := exists_bound_Fp D
  set k : ℕ := ⌈|u₀.re|⌉₊ + 2 with hk
  have hk2 : |u₀.re| + 2 ≤ (k : ℝ) := by
    rw [hk]; push_cast; exact add_le_add_left (Nat.le_ceil _) _
  refine ⟨2 * k + σF + |ν₁.re| + |ν₂.re| + |u₀.re| + |cP.re| + 10, fun s hs => ?_⟩
  have hν₁ := abs_nonneg ν₁.re
  have hν₂ := abs_nonneg ν₂.re
  have hn1 := neg_abs_le ν₁.re
  have hn2 := neg_abs_le ν₂.re
  have hnu := neg_abs_le u₀.re
  have hnu' := le_abs_self u₀.re
  have hncP := neg_abs_le cP.re
  have hncP' := le_abs_self cP.re
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hn0 : (0:ℝ) ≤ 2 := Nat.cast_nonneg 2
  have hδ0 : (0:ℝ) ≤ δ := Nat.cast_nonneg δ
  have hδ1 : (δ:ℝ) ≤ 1 := by rcases hδ with h | h <;> simp [h]
  have hcond : ∀ A : ℝ, |ν₁.re| + |ν₂.re| - 2 < A → -1 < A + 1 + ν₁.re ∧ -1 < A + 1 + ν₂.re := by
    intro A hA; constructor <;> linarith

  set w : ℂ := cP + P₂.centralExponent + 2 * s + 2 + 1 with hw
  have hwre : w.re = cP.re + P₂.centralExponent.re + 2 * s.re + 2 + 1 := by
    rw [hw]; simp <;> ring
  set α : ℝ := s.re - 5 / 2 with hα
  set β : ℝ := -u₀.re - δ with hβ
  set γ : ℝ := -u₀.re + P₂.centralExponent.re + 2 + 2 + -w.re - δ with hγ
  have hβb : β - 2 * k < -1 := by rw [hβ]; linarith
  have hγa : γ + σF < -1 := by rw [hγ, hwre]; linarith
  have hA0 : |ν₁.re| + |ν₂.re| - 2 < α - 2 * k - σF := by rw [hα]; linarith
  have hβb2 : β - 2 - 2 * k < -1 := by rw [hβ]; linarith
  have hβbp2 : β + 2 - 2 * k < -1 := by rw [hβ]; linarith
  have hβbp1 : β + 1 - 2 * k < -1 := by rw [hβ]; linarith
  have hγa2 : γ - 2 + σF < -1 := by rw [hγ, hwre]; linarith
  have hγa1 : γ - 1 + σF < -1 := by rw [hγ, hwre]; linarith
  have hA1 : |ν₁.re| + |ν₂.re| - 2 < α + 1 - 2 * k - σF := by rw [hα]; linarith
  have hA2 : |ν₁.re| + |ν₂.re| - 2 < α + 2 - 2 * k - σF := by rw [hα]; linarith
  have IM := integrable_M ν₁ ν₂ b W hWc hW hWpar (Fp D) (measurable_Fp D) CF σF hCF hσF hbF ha α β γ k hβb hγa (hcond _ hA0)
  have IM1 := integrable_M ν₁ ν₂ b W hWc hW hWpar (Fp D) (measurable_Fp D) CF σF hCF hσF hbF ha α (β - 2) γ k hβb2 hγa (hcond _ hA0)
  have IM2 := integrable_M ν₁ ν₂ b W hWc hW hWpar (Fp D) (measurable_Fp D) CF σF hCF hσF hbF ha α β (γ - 2) k hβb hγa2 (hcond _ hA0)
  have IM3 := integrable_M ν₁ ν₂ b W hWc hW hWpar (Fp D) (measurable_Fp D) CF σF hCF hσF hbF ha (α + 2) (β + 2) γ k hβbp2 hγa (hcond _ hA2)
  have IM5 := integrable_M ν₁ ν₂ b W hWc hW hWpar (Fp D) (measurable_Fp D) CF σF hCF hσF hbF ha (α + 1) (β + 1) (γ - 1) k hβbp1 hγa1 (hcond _ hA1)
  set Cs : ℝ := |a| ^ 2 * (1 / 2) * ((π * a ^ 2) ^ (-w.re / 2) * ‖Complex.Gamma (w / 2)‖) with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  have hmW : Measurable W := measurable_of_continuousOn_ne_zero hWc
  refine Integrable.mono' ((((((IM1.const_mul Cs).add (IM2.const_mul Cs)).add (IM3.const_mul (Cs * a ^ 2))).add
    (IM.const_mul (Cs * (1 / (2 * Real.pi))))).add (IM5.const_mul (Cs * (2 * |a|))))) ?_ ?_
  ·
    have my1 : Measurable fun q : ℝ × ℝ × ℝ => q.2.1 := measurable_fst.comp measurable_snd
    have my2 : Measurable fun q : ℝ × ℝ × ℝ => q.2.2 := measurable_snd.comp measurable_snd
    have mt : Measurable fun q : ℝ × ℝ × ℝ => q.1 := measurable_fst
    have cR : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal
    have mQ1 : Measurable fun q : ℝ × ℝ × ℝ => ArchR.quasiChar u₀ a₀ (q.2.1 * q.2.2)⁻¹ :=
      (measurable_quasiChar u₀ a₀).comp (my1.mul my2).inv
    have mQ2 : Measurable fun q : ℝ × ℝ × ℝ => (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) :=
      cR.comp ((my1.mul my2).inv.abs.pow_const 2).inv
    have mQ3 : Measurable fun q : ℝ × ℝ × ℝ => ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ) :=
      ((measurable_quasiChar _ _).comp my2).mul (cR.comp my2.abs)
    have mQ4 : Measurable fun q : ℝ × ℝ × ℝ =>
        (((q.2.1 * q.2.2)⁻¹ : ℝ) : ℂ) ^ δ * ((|q.2.1 * q.2.2| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (q.2.2 : ℂ)) ^ 2 *
          ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-(w / 2)) * Complex.Gamma (w / 2)) :=
      (((((cR.comp (my1.mul my2).inv).pow_const δ).mul (cR.comp (my1.mul my2).abs)).mul measurable_const).mul
        ((measurable_const.mul (cR.comp my2)).pow_const 2)).mul
        ((measurable_const.mul ((cR.comp ((my2.pow_const 2).const_mul (Real.pi * a ^ 2))).pow_const _)).mul
          measurable_const)
    have mQ5 : Measurable fun q : ℝ × ℝ × ℝ => ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ) :=
      cR.comp ((my2.pow_const 2).mul ((my1.mul my2).abs.pow_const 4).inv)
    have mF : Measurable fun q : ℝ × ℝ × ℝ =>
        (Real.exp (-(Real.pi * (1 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) * ((|q.2.1| : ℝ) : ℂ) :=
      (cR.comp (by fun_prop)).mul (cR.comp my1.abs)
    have mP : Measurable fun q : ℝ × ℝ × ℝ => (1 / q.2.1 ^ 2 - 1 / q.2.2 ^ 2 - a ^ 2 * q.1 ^ 2 * q.2.1 ^ 2 + 1 / (2 * Real.pi) + 2 * a * q.1 * q.2.1 / q.2.2 : ℝ) := by fun_prop
    have mG : Measurable fun q : ℝ × ℝ × ℝ =>
        W q.1 * D.W (ArchR.diagOne (a * q.1 * q.2.1 / q.2.2)) * (((|q.1| : ℝ) : ℂ) ^ (s - 1 / 2)) *
          (((q.1 ^ 2)⁻¹ : ℝ) : ℂ) *
          ((Real.exp (-(Real.pi * ((a * q.1) ^ 2 * q.2.1 ^ 2))) : ℂ) * (((1 / q.2.1 ^ 2 - 1 / q.2.2 ^ 2 - a ^ 2 * q.1 ^ 2 * q.2.1 ^ 2 + 1 / (2 * Real.pi) + 2 * a * q.1 * q.2.1 / q.2.2 : ℝ)) : ℂ)) :=
      ((((hmW.comp mt).mul ((measurable_Fp D).comp (((mt.const_mul a).mul my1).div my2))).mul
        ((cR.comp mt.abs).pow_const _)).mul (cR.comp (mt.pow_const 2).inv)).mul ((cR.comp (by fun_prop)).mul (cR.comp mP))
    exact (((((mQ1.mul mQ2).mul mQ3).mul mQ4).mul mQ5).mul (mF.mul mG)).aestronglyMeasurable
  ·
    filter_upwards [ae_good] with q hq
    obtain ⟨t, y₁, y₂⟩ := q
    obtain ⟨ht, hy₁, hy₂⟩ := hq
    simp only at ht hy₁ hy₂
    have hX : 0 < |t| := abs_pos.2 ht
    have hY : 0 < |y₁| := abs_pos.2 hy₁
    have hy12 : y₁ * y₂ ≠ 0 := mul_ne_zero hy₁ hy₂.ne'
    have nQ1 : ‖ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹‖ = (|y₁| ^ u₀.re)⁻¹ * (y₂ ^ u₀.re)⁻¹ := by
      rw [norm_quasiChar _ _ (inv_ne_zero hy12), abs_inv, abs_mul, abs_of_pos hy₂, Real.inv_rpow (by positivity),
        Real.mul_rpow hY.le hy₂.le, mul_inv]
    have nC : ‖ArchR.centralChar P₂ y₂‖ = y₂ ^ P₂.centralExponent.re := by
      rw [ArchR.centralChar, norm_quasiChar _ _ hy₂.ne', abs_of_pos hy₂]
    have ncp1 : ‖(((|t| : ℝ) : ℂ)) ^ (s - 1 / 2)‖ = |t| ^ (s.re - 1 / 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, Complex.sub_re, show ((1 : ℂ) / 2).re = 1 / 2 by norm_num]
    have ncp2 : ‖((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-(w / 2))‖ = (π * a ^ 2) ^ (-w.re / 2) * (y₂ ^ w.re)⁻¹ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re, Complex.div_ofNat_re,
        Real.mul_rpow (by positivity) (sq_nonneg _), ← Real.rpow_natCast y₂ 2, ← Real.rpow_mul hy₂.le,
        ← Real.rpow_neg hy₂.le]
      congr 2 <;> push_cast <;> ring
    have nhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    have nIa : ‖(-Complex.I * (a : ℂ)) ^ 2‖ = |a| ^ 2 := by
      rw [norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have nIy : ‖(-Complex.I * (y₂ : ℂ)) ^ 2‖ = y₂ ^ 2 := by
      rw [norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy₂]
    have nD : ‖(((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ‖ = (|y₁| ^ δ)⁻¹ * (y₂ ^ δ)⁻¹ := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_mul, abs_of_pos hy₂, inv_pow, mul_pow, mul_inv]
    have eα : |t| ^ α = |t| ^ (s.re - 1 / 2) * (|t| ^ 2)⁻¹ := by
      rw [hα, show s.re - 5 / 2 = (s.re - 1 / 2) - 2 by ring, Real.rpow_sub hX, Real.rpow_two, div_eq_mul_inv]
    have eβ : |y₁| ^ β = (|y₁| ^ u₀.re)⁻¹ * (|y₁| ^ δ)⁻¹ := by
      rw [hβ, sub_eq_add_neg, Real.rpow_add hY, Real.rpow_neg hY.le, Real.rpow_neg hY.le, Real.rpow_natCast]
    have eγ : y₂ ^ γ = (y₂ ^ u₀.re)⁻¹ * y₂ ^ P₂.centralExponent.re * y₂ ^ 2 * y₂ ^ 2 * (y₂ ^ w.re)⁻¹ * (y₂ ^ δ)⁻¹ := by
      rw [hγ, show -u₀.re + P₂.centralExponent.re + 2 + 2 + -w.re - δ =
          -u₀.re + P₂.centralExponent.re + ((2 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + -w.re + -((δ : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_add hy₂, Real.rpow_add hy₂, Real.rpow_add_natCast hy₂.ne', Real.rpow_add_natCast hy₂.ne', Real.rpow_add hy₂,
        Real.rpow_neg hy₂.le, Real.rpow_neg hy₂.le, Real.rpow_neg hy₂.le, Real.rpow_natCast]
    have eE : rexp (-(π * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) = rexp (-(π / y₁ ^ 2)) * rexp (-(π / y₂ ^ 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h0 : (Norm.norm (
        (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) *
            (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((w) / 2)) *
              Complex.Gamma ((w) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ)))))) = Cs * M W (Fp D) a α β γ (t, y₁, y₂) := by
      simp only [M, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, nQ1, nC, ncp1, ncp2, nhalf, nIa, nIy, nD,
        abs_abs, abs_inv, abs_mul, abs_pow, abs_div, abs_of_pos hy₂, Real.abs_exp, eα, eβ, eγ, eE, Fp]
      have hYu : |y₁| ^ u₀.re ≠ 0 := (Real.rpow_pos_of_pos hY _).ne'
      have hZu : y₂ ^ u₀.re ≠ 0 := (Real.rpow_pos_of_pos hy₂ _).ne'
      have hZw : y₂ ^ w.re ≠ 0 := (Real.rpow_pos_of_pos hy₂ _).ne'
      have hTs : |t| ^ (s.re - 1 / 2) ≠ 0 := (Real.rpow_pos_of_pos hX _).ne'
      have hYd : |y₁| ^ δ ≠ 0 := pow_ne_zero _ hY.ne'
      have hZd : y₂ ^ δ ≠ 0 := pow_ne_zero _ hy₂.ne'
      rw [hCs]
      field_simp
    have hsplit : (Norm.norm (
        (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) *
            (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((w) / 2)) *
              Complex.Gamma ((w) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)) : ℂ)))))) = (Norm.norm (
        (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) *
            (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((w) / 2)) *
              Complex.Gamma ((w) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ)))))) * |(1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)| := by
      rw [← Real.norm_eq_abs ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)), ← Complex.norm_real ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)), ← norm_mul]
      congr 1
      ring
    have nP : |(1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)| ≤
        (|y₁| ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + a ^ 2 * |t| ^ 2 * |y₁| ^ 2 + 1 / (2 * Real.pi) + 2 * |a| * |t| * |y₁| * y₂⁻¹ := by
      have e1 : |(1 / y₁ ^ 2 : ℝ)| = (|y₁| ^ 2)⁻¹ := by rw [abs_div, abs_one, abs_pow, one_div]
      have e2 : |(1 / y₂ ^ 2 : ℝ)| = (y₂ ^ 2)⁻¹ := by rw [abs_of_pos (by positivity), one_div]
      have e3 : |(a ^ 2 * t ^ 2 * y₁ ^ 2 : ℝ)| = a ^ 2 * |t| ^ 2 * |y₁| ^ 2 := by
        rw [abs_of_nonneg (by positivity), ← sq_abs t, ← sq_abs y₁]
      have e4 : |(1 / (2 * Real.pi) : ℝ)| = 1 / (2 * Real.pi) := abs_of_pos (by positivity)
      have e5 : |(2 * a * t * y₁ / y₂ : ℝ)| = 2 * |a| * |t| * |y₁| * y₂⁻¹ := by
        rw [abs_div, abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos hy₂, div_eq_mul_inv]
      calc |(1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)|
          ≤ |(1 / y₁ ^ 2 : ℝ) - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi)| + |(2 * a * t * y₁ / y₂ : ℝ)| := abs_add_le _ _
        _ ≤ |(1 / y₁ ^ 2 : ℝ) - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2| + |(1 / (2 * Real.pi) : ℝ)| + |(2 * a * t * y₁ / y₂ : ℝ)| := by
          gcongr; exact abs_add_le _ _
        _ ≤ |(1 / y₁ ^ 2 : ℝ) - 1 / y₂ ^ 2| + |(a ^ 2 * t ^ 2 * y₁ ^ 2 : ℝ)| + |(1 / (2 * Real.pi) : ℝ)| + |(2 * a * t * y₁ / y₂ : ℝ)| := by
          gcongr; exact abs_sub _ _
        _ ≤ |(1 / y₁ ^ 2 : ℝ)| + |(1 / y₂ ^ 2 : ℝ)| + |(a ^ 2 * t ^ 2 * y₁ ^ 2 : ℝ)| + |(1 / (2 * Real.pi) : ℝ)| + |(2 * a * t * y₁ / y₂ : ℝ)| := by
          gcongr; exact abs_sub _ _
        _ = _ := by rw [e1, e2, e3, e4, e5]
    have hM0 : 0 ≤ Cs * M W (Fp D) a α β γ (t, y₁, y₂) := by simp only [M]; positivity
    have rβ2 : |y₁| ^ (β - 2) = |y₁| ^ β * (|y₁| ^ 2)⁻¹ := by rw [Real.rpow_sub hY, Real.rpow_two, div_eq_mul_inv]
    have rγ2 : y₂ ^ (γ - 2) = y₂ ^ γ * (y₂ ^ 2)⁻¹ := by rw [Real.rpow_sub hy₂, Real.rpow_two, div_eq_mul_inv]
    have rα2 : |t| ^ (α + 2) = |t| ^ α * |t| ^ 2 := by rw [Real.rpow_add hX, Real.rpow_two]
    have rβp2 : |y₁| ^ (β + 2) = |y₁| ^ β * |y₁| ^ 2 := by rw [Real.rpow_add hY, Real.rpow_two]
    have rα1 : |t| ^ (α + 1) = |t| ^ α * |t| := Real.rpow_add_one hX.ne' _
    have rβ1 : |y₁| ^ (β + 1) = |y₁| ^ β * |y₁| := Real.rpow_add_one hY.ne' _
    have rγ1 : y₂ ^ (γ - 1) = y₂ ^ γ * y₂⁻¹ := by rw [Real.rpow_sub_one hy₂.ne', div_eq_mul_inv]
    calc (Norm.norm (
        (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) *
            (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((w) / 2)) *
              Complex.Gamma ((w) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)) : ℂ))))))
        = Cs * M W (Fp D) a α β γ (t, y₁, y₂) * |(1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)| := by rw [hsplit, h0]
      _ ≤ Cs * M W (Fp D) a α β γ (t, y₁, y₂) *
          ((|y₁| ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + a ^ 2 * |t| ^ 2 * |y₁| ^ 2 + 1 / (2 * Real.pi) + 2 * |a| * |t| * |y₁| * y₂⁻¹) :=
          mul_le_mul_of_nonneg_left nP hM0
      _ = _ := by
          simp only [Pi.add_apply, M, Fp, rβ2, rγ2, rα2, rβp2, rα1, rβ1, rγ1]
          ring

end
end S_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet (solution)
