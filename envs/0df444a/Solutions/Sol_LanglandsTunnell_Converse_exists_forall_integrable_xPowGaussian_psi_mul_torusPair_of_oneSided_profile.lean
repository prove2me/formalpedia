-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_forall_integrable_xPowGaussian_psi_mul_torusPair_of_oneSided_profile
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ec51c1ab-cec3-5133-b950-8b4631ecda8e

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_xPowGaussian_psi_mul_torusPair_of_oneSided_profile

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

noncomputable section

namespace K9R
open Set Real LanglandsTunnell.Converse.ArchR

section Profile
variable {P₂ : RealArchParam} (D : ArchDatumR P₂)

def Fp (τ : ℝ) : ℂ := D.W (ArchR.diagOne τ)

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

theorem norm_psi (x : ℝ) : ‖ArchR.psi x‖ = 1 := by
  rw [ArchR.psi, Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

theorem continuous_psi : Continuous ArchR.psi := by
  unfold ArchR.psi; fun_prop

theorem measurable_W_of_oneSided (W : ℝ → ℂ) (Q : ℂ)
    (hWpos : ∀ t : ℝ, 0 < t → W t = (2 : ℂ) * (t : ℂ) ^ Q * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → W t = 0) : Measurable W := by
  have hW : W = fun t : ℝ => if 0 < t then (2 : ℂ) * (t : ℂ) ^ Q * (Real.exp (-(2 * Real.pi * t)) : ℂ)
      else if t < 0 then 0 else W 0 := by
    funext t
    rcases lt_trichotomy t 0 with h | h | h
    · rw [if_neg (not_lt.2 h.le), if_pos h, hWneg t h]
    · subst h; simp
    · rw [if_pos h, hWpos t h]
  rw [hW]
  refine Measurable.ite measurableSet_Ioi ?_ (Measurable.ite measurableSet_Iio measurable_const measurable_const)
  exact (measurable_const.mul (Complex.measurable_ofReal.pow_const Q)).mul
    (Complex.measurable_ofReal.comp (by fun_prop))

theorem one_add_pow_le (m : ℕ) {u : ℝ} (hu : 0 ≤ u) : (1 + u) ^ m ≤ 2 ^ m * (1 + u ^ m) := by
  have h1 : 1 + u ≤ 2 * max 1 u := by
    rcases le_total u 1 with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h]; linarith
  have h2 : (max 1 u) ^ m ≤ 1 + u ^ m := by
    rcases le_total u 1 with h | h
    · rw [max_eq_left h, one_pow]; linarith [pow_nonneg hu m]
    · rw [max_eq_right h]; linarith
  calc (1 + u) ^ m ≤ (2 * max 1 u) ^ m := pow_le_pow_left₀ (by linarith) h1 m
    _ = 2 ^ m * (max 1 u) ^ m := mul_pow _ _ _
    _ ≤ 2 ^ m * (1 + u ^ m) := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem integrable_Xm {y₁ : ℝ} (hy₁ : y₁ ≠ 0) (c₀ c₁ : ℂ) (m : ℕ) :
    Integrable (fun x : ℝ => (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (c₀ + c₁ * Complex.I * (x : ℂ)) ^ m) := by
  have hb : 0 < Real.pi / y₁ ^ 2 := by positivity
  have hG : ∀ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℝ) = Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2) := by
    intro x; congr 1; ring
  set K : ℝ := (‖c₀‖ + ‖c₁‖) ^ m * 2 ^ m with hK
  have hm : (-1 : ℝ) < (m : ℝ) := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have iG := integrable_exp_neg_mul_sq hb
  have iM := (integrable_rpow_mul_exp_neg_mul_sq hb hm).norm
  refine Integrable.mono' ((iG.add iM).const_mul K) ?_ (ae_of_all _ fun x => ?_)
  · exact ((Complex.continuous_ofReal.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · simp only [Pi.add_apply]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), hG, norm_pow,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _), Real.rpow_natCast, abs_pow]
    have hE : 0 ≤ Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2) := Real.exp_nonneg _
    have h1x : ‖c₀ + c₁ * Complex.I * (x : ℂ)‖ ≤ (‖c₀‖ + ‖c₁‖) * (1 + |x|) := by
      calc ‖c₀ + c₁ * Complex.I * (x : ℂ)‖ ≤ ‖c₀‖ + ‖c₁ * Complex.I * (x : ℂ)‖ := norm_add_le _ _
        _ = ‖c₀‖ + ‖c₁‖ * |x| := by rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (‖c₀‖ + ‖c₁‖) * (1 + |x|) := by nlinarith [norm_nonneg c₀, norm_nonneg c₁, abs_nonneg x]
    have h2x : ‖c₀ + c₁ * Complex.I * (x : ℂ)‖ ^ m ≤ K * (1 + |x| ^ m) := by
      calc ‖c₀ + c₁ * Complex.I * (x : ℂ)‖ ^ m ≤ ((‖c₀‖ + ‖c₁‖) * (1 + |x|)) ^ m :=
            pow_le_pow_left₀ (norm_nonneg _) h1x m
        _ = (‖c₀‖ + ‖c₁‖) ^ m * (1 + |x|) ^ m := mul_pow _ _ _
        _ ≤ (‖c₀‖ + ‖c₁‖) ^ m * (2 ^ m * (1 + |x| ^ m)) :=
            mul_le_mul_of_nonneg_left (one_add_pow_le m (abs_nonneg x)) (by positivity)
        _ = K * (1 + |x| ^ m) := by rw [hK]; ring
    calc Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2) * ‖c₀ + c₁ * Complex.I * (x : ℂ)‖ ^ m
        ≤ Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2) * (K * (1 + |x| ^ m)) := mul_le_mul_of_nonneg_left h2x hE
      _ = K * (Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2) + |x| ^ m * Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2)) := by ring

theorem integrableOn_rpow_mul_exp_neg_two_pi {A : ℝ} (hA : -1 < A) :
    IntegrableOn (fun t : ℝ => t ^ A * Real.exp (-(2 * Real.pi * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := A) (b := 2 * Real.pi) hA one_pos (by positivity)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  beta_reduce
  rw [Real.rpow_one, neg_mul]

end K9R

end

open K9R LanglandsTunnell.Converse.ArchR Set in
theorem solution
    (W : ℝ → ℂ) (Q : ℂ)
    (hWpos : ∀ t : ℝ, 0 < t → W t = (2 : ℂ) * (t : ℂ) ^ Q * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → W t = 0)
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (m : ℕ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y₂ : ℝ, 0 < y₂ → ∀ c₀ c₁ : ℂ,
      Integrable (fun q : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (q.1 ^ 2 / y₁ ^ 2))) : ℂ) * (c₀ + c₁ * Complex.I * (q.1 : ℂ)) ^ m * ArchR.psi (a * q.2 * q.1)) *
          (W q.2 * D.W (ArchR.diagOne (a * q.2 * y₁ / y₂)) * (((|q.2| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.2 ^ 2)⁻¹ : ℝ) : ℂ)))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  obtain ⟨CF, σF, hCF, hσF, hbF⟩ := exists_bound_Fp D
  refine ⟨σF + 3 / 2 - Q.re, fun s hs y₁ hy₁ y₂ hy₂ c₀ c₁ => ?_⟩

  set lam : ℝ := a * y₁ / y₂ with hlam
  have hlam0 : lam ≠ 0 := div_ne_zero (mul_ne_zero ha hy₁) hy₂.ne'
  have hlampos : 0 < |lam| := abs_pos.2 hlam0
  set A : ℝ := Q.re + s.re - 5 / 2 with hA
  have hA1 : -1 < A := by rw [hA]; linarith
  have hA2 : -1 < A - σF := by rw [hA]; linarith

  set T : ℝ → ℂ := fun t => W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) with hT
  have hmW : Measurable W := measurable_W_of_oneSided W Q hWpos hWneg
  have hmT : Measurable T := by
    rw [hT]
    refine ((hmW.mul ((measurable_Fp D).comp (by fun_prop))).mul
      ((Complex.measurable_ofReal.comp measurable_abs).pow_const _)).mul (Complex.measurable_ofReal.comp (by fun_prop))

  have hT0 : ∀ t : ℝ, t ≤ 0 → T t = 0 := by
    intro t ht
    rcases lt_or_eq_of_le ht with h | h
    · simp only [hT, hWneg t h, zero_mul]
    · simp only [hT, h]; simp

  have key : ∀ t : ℝ, 0 < t →
      ‖T t‖ ≤ 2 * CF * (t ^ A * Real.exp (-(2 * Real.pi * t))) +
        2 * CF * |lam| ^ (-σF) * (t ^ (A - σF) * Real.exp (-(2 * Real.pi * t))) := by
    intro t ht
    have hu0 : a * t * y₁ / y₂ ≠ 0 := div_ne_zero (mul_ne_zero (mul_ne_zero ha ht.ne') hy₁) hy₂.ne'
    have hb := hbF (a * t * y₁ / y₂) hu0
    have hu : |a * t * y₁ / y₂| = |lam| * t := by
      rw [show a * t * y₁ / y₂ = lam * t by rw [hlam]; ring, abs_mul, abs_of_pos ht]
    rw [hu, Real.mul_rpow hlampos.le ht.le] at hb
    have n2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have nQ : ‖(t : ℂ) ^ Q‖ = t ^ Q.re := Complex.norm_cpow_eq_rpow_re_of_pos ht _
    have nE : ‖((Real.exp (-(2 * Real.pi * t)) : ℝ) : ℂ)‖ = Real.exp (-(2 * Real.pi * t)) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    have nS : ‖((|t| : ℝ) : ℂ) ^ (s - 1 / 2)‖ = t ^ (s.re - 1 / 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.2 ht.ne'), abs_of_pos ht, Complex.sub_re,
        show ((1 : ℂ) / 2).re = 1 / 2 by norm_num]
    have nI : ‖(((t ^ 2)⁻¹ : ℝ) : ℂ)‖ = (t ^ 2)⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (sq_nonneg t))]
    simp only [hT, hWpos t ht, norm_mul, n2, nQ, nE, nS, nI]
    have e1 : t ^ Q.re * (t ^ (s.re - 1 / 2) * (t ^ 2)⁻¹) = t ^ A := by
      rw [hA, show (t ^ 2 : ℝ) = t ^ (2:ℝ) by rw [Real.rpow_two], ← Real.rpow_neg ht.le, ← Real.rpow_add ht,
        ← Real.rpow_add ht]; congr 1; ring
    have e2 : t ^ A * t ^ (-σF) = t ^ (A - σF) := by rw [sub_eq_add_neg, Real.rpow_add ht]
    have hF0 : 0 ≤ ‖D.W (ArchR.diagOne (a * t * y₁ / y₂))‖ := norm_nonneg _
    have hE : 0 ≤ Real.exp (-(2 * Real.pi * t)) := Real.exp_nonneg _
    have htA : 0 ≤ t ^ A := Real.rpow_nonneg ht.le _
    have hb' : ‖D.W (ArchR.diagOne (a * t * y₁ / y₂))‖ ≤ CF * (1 + |lam| ^ (-σF) * t ^ (-σF)) := hb
    calc 2 * t ^ Q.re * Real.exp (-(2 * Real.pi * t)) * ‖D.W (ArchR.diagOne (a * t * y₁ / y₂))‖ *
          t ^ (s.re - 1 / 2) * (t ^ 2)⁻¹
        = 2 * (t ^ Q.re * (t ^ (s.re - 1 / 2) * (t ^ 2)⁻¹)) * Real.exp (-(2 * Real.pi * t)) *
            ‖D.W (ArchR.diagOne (a * t * y₁ / y₂))‖ := by ring
      _ = 2 * t ^ A * Real.exp (-(2 * Real.pi * t)) * ‖D.W (ArchR.diagOne (a * t * y₁ / y₂))‖ := by rw [e1]
      _ ≤ 2 * t ^ A * Real.exp (-(2 * Real.pi * t)) * (CF * (1 + |lam| ^ (-σF) * t ^ (-σF))) :=
          mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = 2 * CF * (t ^ A * Real.exp (-(2 * Real.pi * t))) +
            2 * CF * |lam| ^ (-σF) * ((t ^ A * t ^ (-σF)) * Real.exp (-(2 * Real.pi * t))) := by ring
      _ = _ := by rw [e2]

  have hTpos : IntegrableOn T (Ioi 0) := by
    refine Integrable.mono' (((integrableOn_rpow_mul_exp_neg_two_pi hA1).const_mul (2 * CF)).add
      ((integrableOn_rpow_mul_exp_neg_two_pi hA2).const_mul (2 * CF * |lam| ^ (-σF)))) hmT.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t (ht : 0 < t) => ?_)
    simpa only [Pi.add_apply] using key t ht

  have hTneg : IntegrableOn T (Iic 0) := by
    refine (integrableOn_zero).congr_fun (fun t ht => ?_) measurableSet_Iic
    exact (hT0 t ht).symm
  have hTint : Integrable T := by
    have h := hTneg.union hTpos
    rwa [Iic_union_Ioi, integrableOn_univ] at h

  have hX := integrable_Xm hy₁ c₀ c₁ m
  refine Integrable.mono' (hX.norm.mul_prod hTint.norm) ?_ (ae_of_all _ fun q => ?_)
  · refine ((((Complex.continuous_ofReal.comp (by fun_prop)).mul (by fun_prop)).mul
      (continuous_psi.comp (by fun_prop))).measurable.mul (hmT.comp measurable_snd)).aestronglyMeasurable
  · rw [norm_mul, norm_mul, norm_psi, mul_one]

#print axioms solution

end S_LanglandsTunnell_Converse_exists_forall_integrable_xPowGaussian_psi_mul_torusPair_of_oneSided_profile
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_xPowGaussian_psi_mul_torusPair_of_oneSided_profile (solution)
