-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_forall_integrable_thetaFree_iwasawaIntegrand_conjBlockPow_colHarmonic_of_oneSided_profile
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1e26db3d-4521-5485-a8c7-d9e5e064e501

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_conjBlockPow_colHarmonic_of_oneSided_profile

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

noncomputable section
namespace K9E
open Set Real LanglandsTunnell.Converse.ArchR K9R

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

theorem exists_bound_Fp₂ {P₂ : RealArchParam} (D : ArchDatumR P₂) (N : ℕ) :
    ∃ CF σ₁ : ℝ, 0 ≤ CF ∧ (N : ℝ) ≤ σ₁ ∧ ∀ τ : ℝ, τ ≠ 0 → ‖Fp D τ‖ ≤ CF * (|τ| ^ (-σ₁) + |τ| ^ (-(N : ℝ))) := by
  obtain ⟨C₁, hC₁⟩ := D.decay_top 0 N
  obtain ⟨C₂, σ₂, hC₂⟩ := D.decay_zero 0
  have hK1 : ArchR.IsK (1 : Matrix (Fin 2) (Fin 2) ℝ) := Submonoid.one_mem _
  have key : ∀ y : ℝ, ‖iteratedFDerivWithin ℝ 0 (ArchR.asPi D.W) ArchR.glSet (ArchR.diagOneMulCoords y 1)‖ = ‖Fp D y‖ := by
    intro y; rw [norm_iteratedFDerivWithin_zero]; simp [ArchR.asPi, ArchR.diagOneMulCoords, Fp]
  have h1 : ∀ y : ℝ, 1 ≤ |y| → ‖Fp D y‖ ≤ C₁ * |y| ^ (-(N : ℝ)) := by
    intro y hy; have := hC₁ y 1 hK1 hy; rwa [key] at this
  have h2 : ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 → ‖Fp D y‖ ≤ C₂ * |y| ^ (-σ₂) := by
    intro y hy hy1; have := hC₂ y 1 hK1 hy hy1; rwa [key] at this
  have hC₁0 : 0 ≤ C₁ := by
    have := h1 1 (by simp)
    simp only [abs_one, Real.one_rpow, mul_one] at this
    exact le_trans (norm_nonneg _) this
  have hC₂0 : 0 ≤ C₂ := by
    have := h2 1 one_ne_zero (by simp)
    simp only [abs_one, Real.one_rpow, mul_one] at this
    exact le_trans (norm_nonneg _) this
  refine ⟨max C₁ C₂, max σ₂ N, hC₁0.trans (le_max_left _ _), le_max_right _ _, fun τ hτ => ?_⟩
  have hM : 0 ≤ max C₁ C₂ := hC₁0.trans (le_max_left _ _)
  have hτp : 0 < |τ| := abs_pos.2 hτ
  have hr1 : 0 ≤ |τ| ^ (-max σ₂ (N : ℝ)) := Real.rpow_nonneg hτp.le _
  have hr2 : 0 ≤ |τ| ^ (-(N : ℝ)) := Real.rpow_nonneg hτp.le _
  by_cases h : 1 ≤ |τ|
  · calc ‖Fp D τ‖ ≤ C₁ * |τ| ^ (-(N : ℝ)) := h1 τ h
      _ ≤ max C₁ C₂ * |τ| ^ (-(N : ℝ)) := mul_le_mul_of_nonneg_right (le_max_left _ _) hr2
      _ ≤ max C₁ C₂ * (|τ| ^ (-max σ₂ (N : ℝ)) + |τ| ^ (-(N : ℝ))) := by nlinarith
  · have h' : |τ| ≤ 1 := le_of_not_ge h
    calc ‖Fp D τ‖ ≤ C₂ * |τ| ^ (-σ₂) := h2 τ hτ h'
      _ ≤ max C₁ C₂ * |τ| ^ (-max σ₂ (N : ℝ)) := by
          refine mul_le_mul (le_max_right _ _) ?_ (Real.rpow_nonneg hτp.le _) hM
          exact Real.rpow_le_rpow_of_exponent_ge hτp h' (neg_le_neg (le_max_left _ _))
      _ ≤ max C₁ C₂ * (|τ| ^ (-max σ₂ (N : ℝ)) + |τ| ^ (-(N : ℝ))) := by nlinarith

local notation "νY" => Measure.prod (volume : Measure ℝ) (Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ)))

def M2 (W F : ℝ → ℂ) (a α β γ : ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  ((|p.1.1| ^ β * rexp (-(π / p.1.1 ^ 2))) * (p.1.2 ^ γ * rexp (-(π / p.1.2 ^ 2)))) *
    (|p.2| ^ α * ‖W p.2‖ * ‖F (a * p.2 * p.1.1 / p.1.2)‖)

theorem measurable_M2 {W F : ℝ → ℂ} (hmW : Measurable W) (hmF : Measurable F) (a α β γ : ℝ) :
    Measurable (M2 W F a α β γ) := by
  unfold M2
  have my1 : Measurable fun p : (ℝ × ℝ) × ℝ => p.1.1 := measurable_fst.comp measurable_fst
  have my2 : Measurable fun p : (ℝ × ℝ) × ℝ => p.1.2 := measurable_snd.comp measurable_fst
  have mt : Measurable fun p : (ℝ × ℝ) × ℝ => p.2 := measurable_snd
  have h1 : Measurable fun p : (ℝ × ℝ) × ℝ => ‖W p.2‖ := (hmW.comp mt).norm
  have h2 : Measurable fun p : (ℝ × ℝ) × ℝ => ‖F (a * p.2 * p.1.1 / p.1.2)‖ :=
    (hmF.comp (((mt.const_mul a).mul my1).div my2)).norm
  have h3 : Measurable fun p : (ℝ × ℝ) × ℝ => |p.2| ^ α := (mt.abs).pow_const _
  have h5 : Measurable fun p : (ℝ × ℝ) × ℝ => |p.1.1| ^ β := (my1.abs).pow_const _
  have h6 : Measurable fun p : (ℝ × ℝ) × ℝ => rexp (-(π / p.1.1 ^ 2)) := by fun_prop
  have h7 : Measurable fun p : (ℝ × ℝ) × ℝ => p.1.2 ^ γ := my2.pow_const _
  have h8 : Measurable fun p : (ℝ × ℝ) × ℝ => rexp (-(π / p.1.2 ^ 2)) := by fun_prop
  exact ((h5.mul h6).mul (h7.mul h8)).mul ((h3.mul h1).mul h2)

theorem integrable_pairT {b g : ℝ} (hb : b < -1) (hg : g < -1) {φ : ℝ → ℝ} (hφ : Integrable φ) :
    Integrable (fun p : (ℝ × ℝ) × ℝ =>
      ((|p.1.1| ^ b * rexp (-(π / p.1.1 ^ 2))) * (p.1.2 ^ g * rexp (-(π / p.1.2 ^ 2)))) * φ p.2)
      (Measure.prod νY (volume : Measure ℝ)) :=
  ((integrable_Y hb).mul_prod (integrableOn_Z hg)).mul_prod hφ

theorem ae_ne_zero' : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ 0 := by
  have : ({0}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [this] with x hx
  simpa using hx

theorem ae_goodY : ∀ᵐ y : ℝ × ℝ ∂νY, y.1 ≠ 0 ∧ 0 < y.2 :=
  ((Measure.quasiMeasurePreserving_fst).ae ae_ne_zero').and
    ((Measure.quasiMeasurePreserving_snd).ae (ae_restrict_mem measurableSet_Ioi : ∀ᵐ y : ℝ ∂(Measure.restrict volume (Ioi 0)), 0 < y))

theorem ae_good2 : ∀ᵐ p : (ℝ × ℝ) × ℝ ∂(Measure.prod νY (volume : Measure ℝ)), p.1.1 ≠ 0 ∧ 0 < p.1.2 ∧ p.2 ≠ 0 := by
  have h : ∀ᵐ p : (ℝ × ℝ) × ℝ ∂(Measure.prod νY (volume : Measure ℝ)), (p.1.1 ≠ 0 ∧ 0 < p.1.2) ∧ p.2 ≠ 0 :=
    ((Measure.quasiMeasurePreserving_fst).ae ae_goodY).and ((Measure.quasiMeasurePreserving_snd).ae ae_ne_zero')
  filter_upwards [h] with p hp
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

theorem integrable_M2 (W : ℝ → ℂ) (hmW : Measurable W) (A₀ : ℝ)
    (hT : ∀ A : ℝ, A₀ < A → Integrable (fun t : ℝ => |t| ^ A * ‖W t‖))
    (F : ℝ → ℂ) (hmF : Measurable F) (CF σ₁ σ₂ : ℝ) (hCF : 0 ≤ CF)
    (hF : ∀ τ : ℝ, τ ≠ 0 → ‖F τ‖ ≤ CF * (|τ| ^ (-σ₁) + |τ| ^ (-σ₂)))
    {a : ℝ} (ha : a ≠ 0) (α β γ : ℝ)
    (hβ₁ : β - σ₁ < -1) (hβ₂ : β - σ₂ < -1) (hγ₁ : γ + σ₁ < -1) (hγ₂ : γ + σ₂ < -1)
    (hα₁ : A₀ < α - σ₁) (hα₂ : A₀ < α - σ₂) :
    Integrable (M2 W F a α β γ) (Measure.prod νY (volume : Measure ℝ)) := by
  have I1 := integrable_pairT hβ₁ hγ₁ (hT (α - σ₁) hα₁)
  have I2 := integrable_pairT hβ₂ hγ₂ (hT (α - σ₂) hα₂)
  refine Integrable.mono' ((I1.const_mul (CF * |a| ^ (-σ₁))).add (I2.const_mul (CF * |a| ^ (-σ₂))))
    (measurable_M2 hmW hmF a α β γ).aestronglyMeasurable ?_
  filter_upwards [ae_good2] with p hp
  obtain ⟨⟨y₁, y₂⟩, t⟩ := p
  obtain ⟨hy₁, hy₂, ht⟩ := hp
  simp only at ht hy₁ hy₂
  simp only [Pi.add_apply]
  have hX : 0 < |t| := abs_pos.2 ht
  have hY : 0 < |y₁| := abs_pos.2 hy₁

  have hnF : ‖F (a * t * y₁ / y₂)‖ ≤
      CF * |a| ^ (-σ₁) * (|t| ^ (-σ₁) * |y₁| ^ (-σ₁) * y₂ ^ σ₁) +
        CF * |a| ^ (-σ₂) * (|t| ^ (-σ₂) * |y₁| ^ (-σ₂) * y₂ ^ σ₂) := by
    have hτ : a * t * y₁ / y₂ ≠ 0 := div_ne_zero (mul_ne_zero (mul_ne_zero ha ht) hy₁) hy₂.ne'
    refine (hF _ hτ).trans (le_of_eq ?_)
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hy₂, Real.div_rpow (by positivity) hy₂.le,
      Real.div_rpow (by positivity) hy₂.le,
      Real.mul_rpow (by positivity) hY.le, Real.mul_rpow (abs_nonneg a) hX.le,
      Real.mul_rpow (by positivity) hY.le, Real.mul_rpow (abs_nonneg a) hX.le,
      Real.rpow_neg hy₂.le, Real.rpow_neg hy₂.le, div_inv_eq_mul, div_inv_eq_mul]
    ring
  have hL : M2 W F a α β γ ((y₁, y₂), t) =
      ((|y₁| ^ β * rexp (-(π / y₁ ^ 2))) * (y₂ ^ γ * rexp (-(π / y₂ ^ 2))) * (|t| ^ α * ‖W t‖)) *
        ‖F (a * t * y₁ / y₂)‖ := by
    simp only [M2]; ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by rw [hL]; positivity), hL]
  refine (mul_le_mul_of_nonneg_left hnF (by positivity)).trans (le_of_eq ?_)
  have eX1 : |t| ^ (α - σ₁) = |t| ^ α * |t| ^ (-σ₁) := by rw [sub_eq_add_neg, Real.rpow_add hX]
  have eX2 : |t| ^ (α - σ₂) = |t| ^ α * |t| ^ (-σ₂) := by rw [sub_eq_add_neg, Real.rpow_add hX]
  have eY1 : |y₁| ^ (β - σ₁) = |y₁| ^ β * |y₁| ^ (-σ₁) := by rw [sub_eq_add_neg, Real.rpow_add hY]
  have eY2 : |y₁| ^ (β - σ₂) = |y₁| ^ β * |y₁| ^ (-σ₂) := by rw [sub_eq_add_neg, Real.rpow_add hY]
  have eZ1 : y₂ ^ (γ + σ₁) = y₂ ^ γ * y₂ ^ σ₁ := Real.rpow_add hy₂ _ _
  have eZ2 : y₂ ^ (γ + σ₂) = y₂ ^ γ * y₂ ^ σ₂ := Real.rpow_add hy₂ _ _
  rw [eX1, eX2, eY1, eY2, eZ1, eZ2]
  ring

theorem integrable_of_dilate {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) [SFinite ν]
    (f : ℝ × Z → ℂ) (hf : AEStronglyMeasurable f ((volume : Measure ℝ).prod ν))
    (c : Z → ℝ) (hc : ∀ᵐ z ∂ν, c z ≠ 0)
    (hg : Integrable (fun p : ℝ × Z => ((|c p.2| : ℝ) : ℂ) * f (c p.2 * p.1, p.2)) ((volume : Measure ℝ).prod ν)) :
    Integrable f ((volume : Measure ℝ).prod ν) := by
  rw [integrable_prod_iff' hf]
  obtain ⟨hg1, hg2⟩ := (integrable_prod_iff' hg.aestronglyMeasurable).1 hg
  constructor
  · filter_upwards [hg1, hc] with z hz hcz
    have hne : (((|c z| : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (abs_ne_zero.2 hcz)
    have h1 : Integrable (fun x : ℝ => f (c z * x, z)) := by
      refine (hz.const_mul ((((|c z| : ℝ)) : ℂ)⁻¹)).congr (ae_of_all _ fun x => ?_)
      simp only []
      rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    exact (integrable_comp_mul_left_iff (fun x => f (x, z)) hcz).1 h1
  · refine hg2.congr ?_
    filter_upwards [hc] with z hcz
    have e1 : (fun u : ℝ => ‖((|c z| : ℝ) : ℂ) * f (c z * u, z)‖) = fun u => |c z| * ‖f (c z * u, z)‖ := by
      funext u; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs]
    have hsub := Measure.integral_comp_mul_left (fun x : ℝ => ‖f (x, z)‖) (c z)
    beta_reduce at hsub ⊢
    rw [e1, integral_const_mul, hsub, smul_eq_mul, abs_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.2 hcz), one_mul]

theorem integrable_U0 : Integrable (fun u : ℝ => rexp (-π * u ^ 2)) := integrable_exp_neg_mul_sq Real.pi_pos

theorem integrable_U1 : Integrable (fun u : ℝ => |u| * rexp (-π * u ^ 2)) := by
  refine (integrable_mul_exp_neg_mul_sq Real.pi_pos).norm.congr (ae_of_all _ fun u => ?_)
  simp only [Real.norm_eq_abs, abs_mul, Real.abs_exp]

theorem ae_good4 : ∀ᵐ p : ℝ × ((ℝ × ℝ) × ℝ) ∂((volume : Measure ℝ).prod (Measure.prod νY (volume : Measure ℝ))),
    p.2.1.1 ≠ 0 ∧ 0 < p.2.1.2 ∧ p.2.2 ≠ 0 :=
  (Measure.quasiMeasurePreserving_snd).ae ae_good2

theorem integrable_Um (m : ℕ) : Integrable (fun u : ℝ => |u| ^ m * rexp (-π * u ^ 2)) := by
  have hm : (-1 : ℝ) < (m : ℝ) := by have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
  refine (integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos hm).norm.congr (ae_of_all _ fun u => ?_)
  simp only [Real.norm_eq_abs, abs_mul, Real.abs_exp, Real.rpow_natCast, abs_pow]

theorem integrable_T_oneSided (W : ℝ → ℂ) (Q : ℂ)
    (hWpos : ∀ t : ℝ, 0 < t → W t = (2 : ℂ) * (t : ℂ) ^ Q * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → W t = 0) (A : ℝ) (hA : -1 < A + Q.re) :
    Integrable (fun t : ℝ => |t| ^ A * ‖W t‖) := by
  refine integrable_of_Ioi_of_comp_neg _ ?_ ?_
  · refine IntegrableOn.congr_fun ((integrableOn_rpow_mul_exp_neg_two_pi hA).const_mul 2) (fun t (ht : (0:ℝ) < t) => ?_)
      measurableSet_Ioi
    have n2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hWpos t ht, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), abs_of_pos ht, Real.rpow_add ht, n2]
    ring
  · refine (integrableOn_zero).congr_fun (fun t (ht : (0:ℝ) < t) => ?_) measurableSet_Ioi
    rw [hWneg (-t) (by linarith), norm_zero, mul_zero]

theorem add_three_pow_le (m : ℕ) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a + b + c) ^ m ≤ 3 ^ m * (a ^ m + b ^ m + c ^ m) := by
  set M := max a (max b c) with hM
  have haM : a ≤ M := le_max_left _ _
  have hbM : b ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hcM : c ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have h1 : a + b + c ≤ 3 * M := by linarith
  have h2 : M ^ m ≤ a ^ m + b ^ m + c ^ m := by
    have ham := pow_nonneg ha m; have hbm := pow_nonneg hb m; have hcm := pow_nonneg hc m
    rcases le_total b c with hbc | hbc
    · rw [max_eq_right hbc] at hM
      rcases le_total a c with hac | hac
      · rw [hM, max_eq_right hac]; linarith
      · rw [hM, max_eq_left hac]; linarith
    · rw [max_eq_left hbc] at hM
      rcases le_total a b with hab | hab
      · rw [hM, max_eq_right hab]; linarith
      · rw [hM, max_eq_left hab]; linarith
  calc (a + b + c) ^ m ≤ (3 * M) ^ m := pow_le_pow_left₀ (by positivity) h1 m
    _ = 3 ^ m * M ^ m := mul_pow _ _ _
    _ ≤ 3 ^ m * (a ^ m + b ^ m + c ^ m) := mul_le_mul_of_nonneg_left h2 (by positivity)

end K9E
end

theorem K9E.alg_identity (Y Z T A B C Zw Ts E1 E2 EU Cm Pm Qm Um An En Yn Gn Pn Wn Fn : ℝ)
    (hY : Y ≠ 0) (hZ : Z ≠ 0) :
    Y * (A⁻¹ * B⁻¹ * ((Y * Z)⁻¹ ^ 2)⁻¹ * (C * Z) *
            (Cm * (Pm + Qm + Um) * (E1 * E2 * EU) * (Y * Z) * An * (En * Yn) * (1 / 2 * (Pn * Zw⁻¹) * Gn)) *
          (Z ^ 2 * ((Y * Z) ^ 4)⁻¹) *
        (Wn * 1 * Fn * Ts * (T ^ 2)⁻¹)) =
    An * En * (1 / 2) * (Pn * Gn) * Cm *
          (EU * (A⁻¹ * Pm * E1 * (B⁻¹ * C * Yn * Z ^ 2 * Zw⁻¹ * E2) * (Ts * (T ^ 2)⁻¹ * Wn * Fn))) +
        An * En * (1 / 2) * (Pn * Gn) * Cm *
          (EU * (A⁻¹ * E1 * (B⁻¹ * C * Yn * Z ^ 2 * Zw⁻¹ * Qm * E2) * (Ts * (T ^ 2)⁻¹ * Wn * Fn))) +
      An * En * (1 / 2) * (Pn * Gn) * Cm *
        (Um * EU * (A⁻¹ * E1 * (B⁻¹ * C * Yn * Z ^ 2 * Zw⁻¹ * E2) * (Ts * (T ^ 2)⁻¹ * Wn * Fn))) := by
  have hV : (Y * Z) ^ 4 ≠ 0 := pow_ne_zero 4 (mul_ne_zero hY hZ)
  rw [inv_pow, inv_inv]
  linear_combination (Z ^ 2 * (A⁻¹ * B⁻¹ * C * Cm * (Pm + Qm + Um) * (E1 * E2 * EU) * An * (En * Yn) *
    (1 / 2 * Pn * Zw⁻¹ * Gn) * (Wn * Fn * Ts * (T ^ 2)⁻¹))) * (mul_inv_cancel₀ hV)

open K9R K9E LanglandsTunnell.Converse.ArchR Set Real in
theorem solution
    (W : ℝ → ℂ) (Q : ℂ)
    (hWpos : ∀ t : ℝ, 0 < t → W t = (2 : ℂ) * (t : ℂ) ^ Q * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → W t = 0)
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (u₀ cP : ℂ) (a₀ : ZMod 2) (m n : ℕ) (ε' : ℝ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun q : ℝ × ℝ × ℝ =>
        ArchR.quasiChar u₀ a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * q.1) * D.W (ArchR.diagOne (a * t * q.2.1 / q.2.2)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((1 / q.2.1 - 1 / q.2.2 : ℝ) : ℂ)) + Complex.I * (((q.1 / q.2.1 : ℝ) : ℂ))) ^ m *
              (Real.exp (-(Real.pi * ((1 + q.1 ^ 2) / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) *
              ((|q.2.1 * q.2.2| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) ^ n * ((ε' : ℂ) * Complex.I * (q.2.2 : ℂ)) ^ n *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by

  set N : ℕ := ⌈|u₀.re|⌉₊ + 3 with hN
  have hN2 : |u₀.re| + 3 ≤ (N : ℝ) := by
    rw [hN]; push_cast; exact add_le_add_left (Nat.le_ceil _) _
  obtain ⟨CF, σ₁, hCF, hσ₁, hbF⟩ := exists_bound_Fp₂ D N
  refine ⟨σ₁ + |u₀.re| + |cP.re| + |Q.re| + 10, fun s hs => ?_⟩
  have hnu := neg_abs_le u₀.re
  have hnu' := le_abs_self u₀.re
  have hncP := neg_abs_le cP.re
  have hncP' := le_abs_self cP.re
  have hnQ := neg_abs_le Q.re
  have hnQ' := le_abs_self Q.re
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hmW : Measurable W := measurable_W_of_oneSided W Q hWpos hWneg
  have hT : ∀ A : ℝ, -1 - Q.re < A → Integrable (fun t : ℝ => |t| ^ A * ‖W t‖) :=
    fun A hA => integrable_T_oneSided W Q hWpos hWneg A (by linarith)

  set w : ℂ := cP + P₂.centralExponent + 2 * s + n + 1 with hw
  have hwre : w.re = cP.re + P₂.centralExponent.re + 2 * s.re + n + 1 := by
    rw [hw]; simp
  set α : ℝ := s.re - 5 / 2 with hα
  set β : ℝ := -u₀.re with hβ
  set γ : ℝ := -u₀.re + P₂.centralExponent.re + n + 2 + -w.re with hγ
  have hβa₁ : β - m - σ₁ < -1 := by rw [hβ]; linarith
  have hβa₂ : β - m - N < -1 := by rw [hβ]; linarith
  have hβb₁ : β - σ₁ < -1 := by rw [hβ]; linarith
  have hβb₂ : β - N < -1 := by rw [hβ]; linarith
  have hγa₁ : γ + σ₁ < -1 := by rw [hγ, hwre]; linarith
  have hγa₂ : γ + N < -1 := by rw [hγ, hwre]; linarith
  have hγb₁ : γ - m + σ₁ < -1 := by rw [hγ, hwre]; linarith
  have hγb₂ : γ - m + N < -1 := by rw [hγ, hwre]; linarith
  have hA₁ : -1 - Q.re < α - σ₁ := by rw [hα]; linarith
  have hA₂ : -1 - Q.re < α - N := by rw [hα]; linarith
  have IMa := integrable_M2 W hmW (-1 - Q.re) hT (Fp D) (measurable_Fp D) CF σ₁ N hCF hbF ha α (β - m) γ
    hβa₁ hβa₂ hγa₁ hγa₂ hA₁ hA₂
  have IMb := integrable_M2 W hmW (-1 - Q.re) hT (Fp D) (measurable_Fp D) CF σ₁ N hCF hbF ha α β (γ - m)
    hβb₁ hβb₂ hγb₁ hγb₂ hA₁ hA₂
  have IMc := integrable_M2 W hmW (-1 - Q.re) hT (Fp D) (measurable_Fp D) CF σ₁ N hCF hbF ha α β γ
    hβb₁ hβb₂ hγa₁ hγa₂ hA₁ hA₂
  set Cs : ℝ := |a| ^ n * |ε'| ^ n * (1 / 2) * ((π * a ^ 2) ^ (-w.re / 2) * ‖Complex.Gamma (w / 2)‖) * 3 ^ m with hCs
  have hCs0 : 0 ≤ Cs := by positivity

  set Φ : ℝ × ((ℝ × ℝ) × ℝ) → ℂ := fun p =>
    (ArchR.quasiChar u₀ a₀ (p.2.1.1 * p.2.1.2)⁻¹ * (((|(p.2.1.1 * p.2.1.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
      (ArchR.centralChar P₂ p.2.1.2 * ((|p.2.1.2| : ℝ) : ℂ)) *
      (((((1 / p.2.1.1 - 1 / p.2.1.2 : ℝ) : ℂ)) + Complex.I * (((p.1 / p.2.1.1 : ℝ) : ℂ))) ^ m *
        (Real.exp (-(Real.pi * ((1 + p.1 ^ 2) / p.2.1.1 ^ 2 + 1 / p.2.1.2 ^ 2))) : ℂ) *
        ((|p.2.1.1 * p.2.1.2| : ℝ) : ℂ) *
        (-Complex.I * (a : ℂ)) ^ n * ((ε' : ℂ) * Complex.I * (p.2.1.2 : ℂ)) ^ n *
        ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * p.2.1.2 ^ 2 : ℝ) : ℂ) ^ (-(w / 2)) * Complex.Gamma (w / 2))) *
      ((p.2.1.2 ^ 2 * (|p.2.1.1 * p.2.1.2| ^ 4)⁻¹ : ℝ) : ℂ)) *
    (W p.2.2 * ArchR.psi (a * p.2.2 * p.1) * D.W (ArchR.diagOne (a * p.2.2 * p.2.1.1 / p.2.1.2)) *
      (((|p.2.2| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((p.2.2 ^ 2)⁻¹ : ℝ) : ℂ)) with hΦ
  have hmΦ : Measurable Φ := by
    rw [hΦ]
    have mx : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => p.1 := measurable_fst
    have my1 : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => p.2.1.1 := measurable_fst.comp (measurable_fst.comp measurable_snd)
    have my2 : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => p.2.1.2 := measurable_snd.comp (measurable_fst.comp measurable_snd)
    have mt : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => p.2.2 := measurable_snd.comp measurable_snd
    have cR : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal
    have mQ1 : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => ArchR.quasiChar u₀ a₀ (p.2.1.1 * p.2.1.2)⁻¹ :=
      (measurable_quasiChar u₀ a₀).comp (my1.mul my2).inv
    have mQ2 : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => (((|(p.2.1.1 * p.2.1.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) :=
      cR.comp ((my1.mul my2).inv.abs.pow_const 2).inv
    have mQ3 : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => ArchR.centralChar P₂ p.2.1.2 * ((|p.2.1.2| : ℝ) : ℂ) :=
      ((measurable_quasiChar _ _).comp my2).mul (cR.comp my2.abs)
    have mQ4 : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) =>
        ((((1 / p.2.1.1 - 1 / p.2.1.2 : ℝ) : ℂ)) + Complex.I * (((p.1 / p.2.1.1 : ℝ) : ℂ))) ^ m *
          (Real.exp (-(Real.pi * ((1 + p.1 ^ 2) / p.2.1.1 ^ 2 + 1 / p.2.1.2 ^ 2))) : ℂ) *
          ((|p.2.1.1 * p.2.1.2| : ℝ) : ℂ) *
          (-Complex.I * (a : ℂ)) ^ n * ((ε' : ℂ) * Complex.I * (p.2.1.2 : ℂ)) ^ n *
          ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * p.2.1.2 ^ 2 : ℝ) : ℂ) ^ (-(w / 2)) * Complex.Gamma (w / 2)) :=
      (((((((cR.comp ((measurable_const.div my1).sub (measurable_const.div my2))).add
          (measurable_const.mul (cR.comp (mx.div my1)))).pow_const m).mul (cR.comp (by fun_prop))).mul
          (cR.comp (my1.mul my2).abs)).mul measurable_const).mul
          (((measurable_const.mul measurable_const).mul (cR.comp my2)).pow_const n)).mul
        ((measurable_const.mul ((cR.comp ((my2.pow_const 2).const_mul (Real.pi * a ^ 2))).pow_const _)).mul
          measurable_const)
    have mQ5 : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => ((p.2.1.2 ^ 2 * (|p.2.1.1 * p.2.1.2| ^ 4)⁻¹ : ℝ) : ℂ) :=
      cR.comp ((my2.pow_const 2).mul ((my1.mul my2).abs.pow_const 4).inv)
    have mH : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) =>
        W p.2.2 * ArchR.psi (a * p.2.2 * p.1) * D.W (ArchR.diagOne (a * p.2.2 * p.2.1.1 / p.2.1.2)) *
          (((|p.2.2| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((p.2.2 ^ 2)⁻¹ : ℝ) : ℂ) :=
      ((((hmW.comp mt).mul (continuous_psi.measurable.comp ((mt.const_mul a).mul mx))).mul
        ((measurable_Fp D).comp (((mt.const_mul a).mul my1).div my2))).mul
        ((cR.comp mt.abs).pow_const _)).mul (cR.comp (mt.pow_const 2).inv)
    exact ((((mQ1.mul mQ2).mul mQ3).mul mQ4).mul mQ5).mul mH

  have hG : Integrable (fun p : ℝ × ((ℝ × ℝ) × ℝ) => ((|p.2.1.1| : ℝ) : ℂ) * Φ (p.2.1.1 * p.1, p.2))
      ((volume : Measure ℝ).prod (Measure.prod (Measure.prod (volume : Measure ℝ) (Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ)))) (volume : Measure ℝ))) := by
    have my1 : Measurable fun p : ℝ × ((ℝ × ℝ) × ℝ) => p.2.1.1 := measurable_fst.comp (measurable_fst.comp measurable_snd)
    have hmG : Measurable (fun p : ℝ × ((ℝ × ℝ) × ℝ) => ((|p.2.1.1| : ℝ) : ℂ) * Φ (p.2.1.1 * p.1, p.2)) :=
      (Complex.measurable_ofReal.comp my1.abs).mul (hmΦ.comp ((my1.mul measurable_fst).prodMk measurable_snd))
    refine Integrable.mono'
      ((((integrable_U0.mul_prod IMa).const_mul Cs).add ((integrable_U0.mul_prod IMb).const_mul Cs)).add
        (((integrable_Um m).mul_prod IMc).const_mul Cs)) hmG.aestronglyMeasurable ?_
    filter_upwards [ae_good4] with p hp
    obtain ⟨u, ⟨y₁, y₂⟩, t⟩ := p
    obtain ⟨hy₁, hy₂, ht⟩ := hp
    simp only at ht hy₁ hy₂
    simp only [Pi.add_apply]
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
    have nIa : ‖(-Complex.I * (a : ℂ)) ^ n‖ = |a| ^ n := by
      rw [norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have nIy : ‖((ε' : ℂ) * Complex.I * (y₂ : ℂ)) ^ n‖ = |ε'| ^ n * y₂ ^ n := by
      rw [norm_pow, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hy₂, mul_pow]
    have nBp : ‖(((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((y₁ * u / y₁ : ℝ) : ℂ))) ^ m)‖ =
        ‖((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((y₁ * u / y₁ : ℝ) : ℂ)))‖ ^ m := norm_pow _ m
    have nB : ‖((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((y₁ * u / y₁ : ℝ) : ℂ)))‖ ≤ |y₁|⁻¹ + y₂⁻¹ + |u| := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        mul_div_cancel_left₀ u hy₁]
      have h1 : |1 / y₁ - 1 / y₂| ≤ |y₁|⁻¹ + y₂⁻¹ := by
        calc |1 / y₁ - 1 / y₂| ≤ |1 / y₁| + |1 / y₂| := abs_sub _ _
          _ = |y₁|⁻¹ + y₂⁻¹ := by rw [abs_div, abs_div, abs_one, abs_of_pos hy₂, one_div, one_div]
      linarith
    have nBm : ‖((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((y₁ * u / y₁ : ℝ) : ℂ)))‖ ^ m ≤
        3 ^ m * (|y₁|⁻¹ ^ m + y₂⁻¹ ^ m + |u| ^ m) :=
      (pow_le_pow_left₀ (norm_nonneg _) nB m).trans
        (add_three_pow_le m (inv_nonneg.2 (abs_nonneg _)) (inv_nonneg.2 hy₂.le) (abs_nonneg u))
    have eα : |t| ^ α = |t| ^ (s.re - 1 / 2) * (|t| ^ 2)⁻¹ := by
      rw [hα, show s.re - 5 / 2 = (s.re - 1 / 2) - 2 by ring, Real.rpow_sub hX, Real.rpow_two, div_eq_mul_inv]
    have eβ : |y₁| ^ β = (|y₁| ^ u₀.re)⁻¹ := by rw [hβ, Real.rpow_neg hY.le]
    have eβm : |y₁| ^ (β - m) = (|y₁| ^ u₀.re)⁻¹ * |y₁|⁻¹ ^ m := by
      rw [Real.rpow_sub_natCast hY.ne', eβ, div_eq_mul_inv, inv_pow]
    have eγ : y₂ ^ γ = (y₂ ^ u₀.re)⁻¹ * y₂ ^ P₂.centralExponent.re * y₂ ^ n * y₂ ^ 2 * (y₂ ^ w.re)⁻¹ := by
      rw [hγ, show -u₀.re + P₂.centralExponent.re + n + 2 + -w.re = -u₀.re + P₂.centralExponent.re + ((n : ℕ) : ℝ) + ((2 : ℕ) : ℝ) + -w.re by push_cast; ring,
        Real.rpow_add hy₂, Real.rpow_add_natCast hy₂.ne', Real.rpow_add_natCast hy₂.ne', Real.rpow_add hy₂,
        Real.rpow_neg hy₂.le, Real.rpow_neg hy₂.le]
    have eγm : y₂ ^ (γ - m) = (y₂ ^ u₀.re)⁻¹ * y₂ ^ P₂.centralExponent.re * y₂ ^ n * y₂ ^ 2 * (y₂ ^ w.re)⁻¹ * y₂⁻¹ ^ m := by
      rw [Real.rpow_sub_natCast hy₂.ne', eγ, div_eq_mul_inv, inv_pow]
    have eE : rexp (-(π * ((1 + (y₁ * u) ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) =
        rexp (-(π / y₁ ^ 2)) * rexp (-(π / y₂ ^ 2)) * rexp (-π * u ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; field_simp; ring
    simp only [hΦ, M2, norm_mul, Complex.norm_real, Real.norm_eq_abs, nQ1, nC, ncp1, ncp2, nhalf,
      nIa, nIy, nBp, norm_psi, abs_abs, abs_inv, abs_mul, abs_pow, abs_of_pos hy₂, Real.abs_exp, eα, eβ, eβm, eγ, eγm, eE, Fp]
    have hFp : 0 ≤ ‖D.W (ArchR.diagOne (a * t * y₁ / y₂))‖ := norm_nonneg _
    have hW0 : 0 ≤ ‖W t‖ := norm_nonneg _
    have hG0 : 0 ≤ ‖Complex.Gamma (w / 2)‖ := norm_nonneg _
    have hYu : |y₁| ^ u₀.re ≠ 0 := (Real.rpow_pos_of_pos hY _).ne'
    have hZu : y₂ ^ u₀.re ≠ 0 := (Real.rpow_pos_of_pos hy₂ _).ne'
    have hZw : y₂ ^ w.re ≠ 0 := (Real.rpow_pos_of_pos hy₂ _).ne'
    have hTs : |t| ^ (s.re - 1 / 2) ≠ 0 := (Real.rpow_pos_of_pos hX _).ne'
    refine LE.le.trans_eq (b := |y₁| *
      ((|y₁| ^ u₀.re)⁻¹ * (y₂ ^ u₀.re)⁻¹ * ((|y₁| * y₂)⁻¹ ^ 2)⁻¹ * (y₂ ^ P₂.centralExponent.re * y₂) *
            ((3 ^ m * (|y₁|⁻¹ ^ m + y₂⁻¹ ^ m + |u| ^ m)) *
                      (rexp (-(π / y₁ ^ 2)) * rexp (-(π / y₂ ^ 2)) * rexp (-π * u ^ 2)) *
                    (|y₁| * y₂) *
                  |a| ^ n *
                (|ε'| ^ n * y₂ ^ n) *
              (1 / 2 * ((π * a ^ 2) ^ (-w.re / 2) * (y₂ ^ w.re)⁻¹) * ‖Complex.Gamma (w / 2)‖)) *
          (y₂ ^ 2 * ((|y₁| * y₂) ^ 4)⁻¹) *
        (‖W t‖ * 1 * ‖D.W (ArchR.diagOne (a * t * y₁ / y₂))‖ * |t| ^ (s.re - 1 / 2) * (|t| ^ 2)⁻¹))) ?_ ?_
    · gcongr
    · rw [hCs]
      exact K9E.alg_identity |y₁| y₂ |t| (|y₁| ^ u₀.re) (y₂ ^ u₀.re) (y₂ ^ P₂.centralExponent.re) (y₂ ^ w.re)
        (|t| ^ (s.re - 1 / 2)) (rexp (-(π / y₁ ^ 2))) (rexp (-(π / y₂ ^ 2))) (rexp (-π * u ^ 2)) (3 ^ m)
        (|y₁|⁻¹ ^ m) (y₂⁻¹ ^ m) (|u| ^ m) (|a| ^ n) (|ε'| ^ n) (y₂ ^ n) ‖Complex.Gamma (w / 2)‖
        ((π * a ^ 2) ^ (-w.re / 2)) ‖W t‖ ‖D.W (ArchR.diagOne (a * t * y₁ / y₂))‖ hY.ne' hy₂.ne'

  have hΦi : Integrable Φ ((volume : Measure ℝ).prod (Measure.prod (Measure.prod (volume : Measure ℝ) (Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ)))) (volume : Measure ℝ))) :=
    integrable_of_dilate _ Φ hmΦ.aestronglyMeasurable (fun z => z.1.1)
      ((Measure.quasiMeasurePreserving_fst).ae ae_goodY |>.mono fun z hz => hz.1) hG
  have hΦa := (MeasureTheory.measurePreserving_prodAssoc (volume : Measure ℝ)
      (Measure.prod (volume : Measure ℝ) (Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ)))) (volume : Measure ℝ)).integrable_comp_of_integrable hΦi
  have hI := hΦa.integral_prod_left
  refine hI.congr (ae_of_all _ fun q => ?_)
  obtain ⟨x, y₁, y₂⟩ := q
  show (∫ t : ℝ, Φ (x, ((y₁, y₂), t))) = _
  simp only [hΦ]
  rw [integral_const_mul]
  ring

#print axioms solution

end S_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_conjBlockPow_colHarmonic_of_oneSided_profile
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_conjBlockPow_colHarmonic_of_oneSided_profile (solution)
