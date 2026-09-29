-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_archDatumR
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/536fe6cf-c3c4-5cc6-b8c0-146ed6ba7c5c

import Mathlib
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_archDatumR

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory
open Set Real

noncomputable section

namespace K7RA5

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

theorem integrableOn_cpow_mul_W (P : ZMod 2 → ℂ × ℂ) (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (P b).1 * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (P b).2 * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (A : ℂ) (hA : ∀ b : ZMod 2, -1 < (A + 1).re + (P b).1.re ∧ -1 < (A + 1).re + (P b).2.re) :
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ A * W t) (Ioi 0) ∧
    IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ A * W (-t)) (Ioi 0) := by

  have hG : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t → W t + (-1 : ℂ) ^ b.val * W (-t) =
      (t : ℂ) * G (P b).1 (P b).2 (1 * t) := by
    intro b t ht; rw [hW b t ht, one_mul]; rfl
  have i0 := integrableOn_cpow_mul_G (P 0).1 (P 0).2 (A + 1) one_pos (hA 0).1 (hA 0).2
  have i1 := integrableOn_cpow_mul_G (P 1).1 (P 1).2 (A + 1) one_pos (hA 1).1 (hA 1).2
  have hmW : Measurable W := measurable_of_continuousOn_ne_zero hWc
  have hm1 : AEStronglyMeasurable (fun t : ℝ => ((t : ℝ) : ℂ) ^ A * W t) (μ0) :=
    ((Complex.measurable_ofReal.pow_const A).mul hmW).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun t : ℝ => ((t : ℝ) : ℂ) ^ A * W (-t)) (μ0) :=
    ((Complex.measurable_ofReal.pow_const A).mul (hmW.comp measurable_neg)).aestronglyMeasurable

  have hpt : ∀ t : ℝ, 0 < t →
      ((t : ℝ) : ℂ) ^ A * W t =
        (((t : ℝ) : ℂ) ^ (A + 1) * G (P 0).1 (P 0).2 (1 * t) +
          ((t : ℝ) : ℂ) ^ (A + 1) * G (P 1).1 (P 1).2 (1 * t)) / 2 ∧
      ((t : ℝ) : ℂ) ^ A * W (-t) =
        (((t : ℝ) : ℂ) ^ (A + 1) * G (P 0).1 (P 0).2 (1 * t) -
          ((t : ℝ) : ℂ) ^ (A + 1) * G (P 1).1 (P 1).2 (1 * t)) / 2 := by
    intro t ht
    obtain ⟨e0, e1⟩ := sheets W _ _ (hG 0) (hG 1) ht
    have hp : ((t : ℝ) : ℂ) ^ (A + 1) = ((t : ℝ) : ℂ) ^ A * (t : ℂ) := by
      rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 ht.ne'), Complex.cpow_one]
    rw [e0, e1, hp]; constructor <;> ring
  refine ⟨?_, ?_⟩
  · refine Integrable.congr ((i0.add i1).div_const 2) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t (ht : 0 < t) => by
      simp only [Pi.add_apply]; exact ((hpt t ht).1).symm)
  · refine Integrable.congr ((i0.sub i1).div_const 2) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t (ht : 0 < t) => by
      simp only [Pi.sub_apply]; exact ((hpt t ht).2).symm)

end K7RA5

namespace K7RA5b

open LanglandsTunnell.Converse.ArchR K7RA5

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

end K7RA5b

open K7RA5 K7RA5b LanglandsTunnell.Converse.ArchR in
theorem solution
    (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (c₀ c₁ : ℂ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y₂ : ℝ, 0 < y₂ →
      Integrable (fun q : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (q.1 ^ 2 / y₁ ^ 2))) : ℂ) * (c₀ + c₁ * Complex.I * (q.1 : ℂ)) * ArchR.psi (a * q.2 * q.1)) *
          (W q.2 * D.W (ArchR.diagOne (a * q.2 * y₁ / y₂)) * (((|q.2| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.2 ^ 2)⁻¹ : ℝ) : ℂ)))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  obtain ⟨CF, σF, hCF, hσF, hbF⟩ := exists_bound_Fp D
  refine ⟨σF + |ν₁.re| + |ν₂.re| + 1, fun s hs y₁ hy₁ y₂ hy₂ => ?_⟩
  have hν₁ := abs_nonneg ν₁.re
  have hν₂ := abs_nonneg ν₂.re

  set lam : ℝ := a * y₁ / y₂ with hlam
  have hlam0 : lam ≠ 0 := div_ne_zero (mul_ne_zero ha hy₁) hy₂.ne'
  have hlampos : 0 < |lam| := abs_pos.2 hlam0
  set α : ℝ := s.re - 5 / 2 with hα
  set P : ZMod 2 → ℂ × ℂ := fun b => (ν₁ + signShift (a₁ + b), ν₂ + signShift (a₂ + b)) with hP
  have hWP : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (P b).1 * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (P b).2 * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) := by
    intro b t ht; simpa only [hP] using hW b t ht
  have hcond : ∀ A : ℂ, |ν₁.re| + |ν₂.re| - 3 / 2 < A.re →
      ∀ b : ZMod 2, -1 < (A + 1).re + ((P b).1).re ∧ -1 < (A + 1).re + ((P b).2).re := by
    intro A hA b
    have h1 := signShift_re_nonneg (a₁ + b); have h2 := signShift_re_nonneg (a₂ + b)
    have hn1 := neg_abs_le ν₁.re; have hn2 := neg_abs_le ν₂.re
    simp only [hP, Complex.add_re, Complex.one_re]
    constructor <;> linarith [abs_nonneg ν₁.re, abs_nonneg ν₂.re]
  obtain ⟨iW0, iW0n⟩ := integrableOn_cpow_mul_W P W hWc hWP (α : ℂ) (hcond _ (by simp only [Complex.ofReal_re, hα]; linarith))
  obtain ⟨iW1, iW1n⟩ := integrableOn_cpow_mul_W P W hWc hWP ((α - σF : ℝ) : ℂ) (hcond _ (by simp only [Complex.ofReal_re, hα]; linarith))

  set T : ℝ → ℂ := fun t => W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) with hT
  have hmW : Measurable W := measurable_of_continuousOn_ne_zero hWc
  have hmT : Measurable T := by
    rw [hT]
    refine ((hmW.mul ((measurable_Fp D).comp (by fun_prop))).mul
      ((Complex.measurable_ofReal.comp measurable_abs).pow_const _)).mul (Complex.measurable_ofReal.comp (by fun_prop))

  have key : ∀ (t : ℝ), 0 < t → ∀ (u : ℝ) (Wv : ℂ), |u| = |lam| * t →
      ‖Wv * D.W (ArchR.diagOne u) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤
        CF * ‖((t : ℝ) : ℂ) ^ (α : ℂ) * Wv‖ + CF * |lam| ^ (-σF) * ‖((t : ℝ) : ℂ) ^ ((α - σF : ℝ) : ℂ) * Wv‖ := by
    intro t ht u Wv hu
    have hu0 : u ≠ 0 := by intro h; rw [h, abs_zero] at hu; exact (mul_pos hlampos ht).ne' hu.symm
    have hb := hbF u hu0
    rw [hu, Real.mul_rpow hlampos.le ht.le] at hb
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.2 ht.ne'), abs_of_pos ht,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (sq_nonneg t)), norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.ofReal_re, Complex.ofReal_re,
      Complex.sub_re, show ((1 : ℂ) / 2).re = 1 / 2 by norm_num]
    have e1 : t ^ (s.re - 1 / 2) * (t ^ 2)⁻¹ = t ^ α := by
      rw [hα, show (t ^ 2 : ℝ) = t ^ (2:ℝ) by rw [Real.rpow_two], ← Real.rpow_neg ht.le, ← Real.rpow_add ht]; congr 1; ring
    have e2 : t ^ α * t ^ (-σF) = t ^ (α - σF) := by rw [sub_eq_add_neg, Real.rpow_add ht]
    have hWn : 0 ≤ ‖Wv‖ := norm_nonneg _
    have hta : 0 ≤ t ^ α := Real.rpow_nonneg ht.le _
    calc ‖Wv‖ * ‖D.W (ArchR.diagOne u)‖ * t ^ (s.re - 1 / 2) * (t ^ 2)⁻¹
        = ‖Wv‖ * ‖D.W (ArchR.diagOne u)‖ * (t ^ (s.re - 1 / 2) * (t ^ 2)⁻¹) := by ring
      _ = ‖Wv‖ * ‖D.W (ArchR.diagOne u)‖ * t ^ α := by rw [e1]
      _ ≤ ‖Wv‖ * (CF * (1 + |lam| ^ (-σF) * t ^ (-σF))) * t ^ α := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hWn) hta
      _ = CF * (t ^ α * ‖Wv‖) + CF * |lam| ^ (-σF) * (t ^ α * t ^ (-σF) * ‖Wv‖) := by ring
      _ = CF * (t ^ α * ‖Wv‖) + CF * |lam| ^ (-σF) * (t ^ (α - σF) * ‖Wv‖) := by rw [e2]

  have hTpos : IntegrableOn T (Ioi 0) := by
    refine Integrable.mono' ((iW0.norm.const_mul CF).add (iW1.norm.const_mul (CF * |lam| ^ (-σF)))) hmT.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t (ht : 0 < t) => ?_)
    have := key t ht (a * t * y₁ / y₂) (W t) (by rw [show a * t * y₁ / y₂ = lam * t by rw [hlam]; ring, abs_mul, abs_of_pos ht])
    simpa only [hT, Pi.add_apply] using this

  have hTneg : IntegrableOn (fun t => T (-t)) (Ioi 0) := by
    refine Integrable.mono' ((iW0n.norm.const_mul CF).add (iW1n.norm.const_mul (CF * |lam| ^ (-σF))))
      (hmT.comp measurable_neg).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t (ht : 0 < t) => ?_)
    have := key t ht (a * (-t) * y₁ / y₂) (W (-t)) (by rw [show a * (-t) * y₁ / y₂ = -(lam * t) by rw [hlam]; ring, abs_neg, abs_mul, abs_of_pos ht])
    simpa only [hT, Pi.add_apply, abs_neg, neg_sq] using this
  have hTint : Integrable T := by
    have h := (integrableOn_Iic_of_comp_neg T hTneg).union hTpos
    rwa [Iic_union_Ioi, integrableOn_univ] at h

  have hX := integrable_X hy₁ c₀ c₁
  refine Integrable.mono' (hX.norm.mul_prod hTint.norm) ?_ (ae_of_all _ fun q => ?_)
  · refine ((((Complex.continuous_ofReal.comp (by fun_prop)).mul (by fun_prop)).mul
      (continuous_psi.comp (by fun_prop))).measurable.mul (hmT.comp measurable_snd)).aestronglyMeasurable
  · rw [norm_mul, norm_mul, norm_psi, mul_one]

#print axioms solution

end
end S_LanglandsTunnell_Converse_exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_archDatumR
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_archDatumR (solution)
