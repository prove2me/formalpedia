-- Prove2me | solution 1 for LanglandsTunnell.Converse.integrable_dualConfig_iwasawaIntegrand_detPow_colHarmonic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1d1ca690-5cbf-5f97-977a-74df92d1d2ee

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_integrable_dualConfig_iwasawaIntegrand_detPow_colHarmonic

set_option autoImplicit false
set_option maxHeartbeats 4000000

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

noncomputable section

namespace DualRB3a

open Set Real

theorem measurable_of_continuousOn_ne_zero {W : ℝ → ℂ} (hWc : ContinuousOn W {t : ℝ | t ≠ 0}) : Measurable W :=
  measurable_of_continuousOn_compl_singleton 0 (by rwa [Set.compl_singleton_eq])

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

end Profile

theorem norm_psi (x : ℝ) : ‖ArchR.psi x‖ = 1 := by
  rw [ArchR.psi, Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

theorem continuous_psi : Continuous ArchR.psi := by
  unfold ArchR.psi; fun_prop

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

local notation "νY" => Measure.prod (volume : Measure ℝ) (Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ)))

theorem ae_ne_zero' : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ 0 := by
  have : ({0}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [this] with x hx
  simpa using hx

theorem ae_goodY : ∀ᵐ y : ℝ × ℝ ∂νY, y.1 ≠ 0 ∧ 0 < y.2 :=
  ((Measure.quasiMeasurePreserving_fst).ae ae_ne_zero').and
    ((Measure.quasiMeasurePreserving_snd).ae (ae_restrict_mem measurableSet_Ioi : ∀ᵐ y : ℝ ∂(Measure.restrict volume (Ioi 0)), 0 < y))

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
    rw [e1, integral_const_mul, hsub, smul_eq_mul, abs_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.2 hcz), one_mul]

theorem integrable_U0 : Integrable (fun u : ℝ => rexp (-π * u ^ 2)) := integrable_exp_neg_mul_sq Real.pi_pos

theorem ae_good3 : ∀ᵐ p : ℝ × (ℝ × ℝ) ∂((volume : Measure ℝ).prod νY), p.2.1 ≠ 0 ∧ 0 < p.2.2 :=
  (Measure.quasiMeasurePreserving_snd).ae ae_goodY

theorem integrableOn_Zg (γ : ℝ) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    IntegrableOn (fun y : ℝ => y ^ γ * (rexp (-(c₁ / y ^ 2)) * rexp (-(c₂ * y ^ 2)))) (Ioi 0) := by
  set k : ℕ := ⌈|γ|⌉₊ + 1 with hk
  have hk1 : |γ| + 1 ≤ (k : ℝ) := by rw [hk]; push_cast; exact add_le_add_left (Nat.le_ceil _) _
  have hγk : -1 < γ + 2 * k := by
    have := neg_abs_le γ; linarith
  set K : ℝ := (k.factorial : ℝ) * (c₁ ^ k)⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  have h0 : IntegrableOn (fun y : ℝ => y ^ (γ + 2 * k) * rexp (-c₂ * y ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hc₂ hγk
  refine Integrable.mono' (h0.const_mul K) ?_ ?_
  · refine ((measurable_id.pow_const _).mul ((by fun_prop : Measurable fun y : ℝ => rexp (-(c₁ / y ^ 2))).mul
      (by fun_prop : Measurable fun y : ℝ => rexp (-(c₂ * y ^ 2))))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : (0 : ℝ) < y := hy
    have hx : 0 < c₁ / y ^ 2 := by positivity
    have h1 : rexp (-(c₁ / y ^ 2)) ≤ K * y ^ ((2 * k : ℕ) : ℝ) := by
      refine (exp_neg_le_factorial_mul_inv_pow k hx).trans (le_of_eq ?_)
      rw [hK, Real.rpow_natCast, div_pow, inv_div, pow_mul]
      field_simp
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc y ^ γ * (rexp (-(c₁ / y ^ 2)) * rexp (-(c₂ * y ^ 2)))
        ≤ y ^ γ * (K * y ^ ((2 * k : ℕ) : ℝ) * rexp (-(c₂ * y ^ 2))) := by gcongr
      _ = K * (y ^ (γ + 2 * k) * rexp (-c₂ * y ^ 2)) := by
          rw [Real.rpow_add hy', neg_mul]; push_cast; ring

end DualRB3a

theorem solution
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℝ) (ha : a ≠ 0) (u : ℂ) (a₀ : ZMod 2) (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : 0 < a₂) (n : ℕ) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) :
    Integrable (fun q : ℝ × ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (q.1 ^ 2 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2) + 1 / q.2.1 ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |q.2.1 * q.2.2| : ℝ)) : ℂ) *
            (((q.2.1⁻¹ : ℝ) : ℂ) ^ n * (-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((q.1 * q.2.2 / q.2.1 : ℝ)) : ℂ))) ^ δ) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * q.2.2 ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * q.1) * (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * q.2.1 / q.2.2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by
  classical

  set N : ℕ := ⌈|u.re|⌉₊ + 3 with hN
  have hN2 : |u.re| + 3 ≤ (N : ℝ) := by
    rw [hN]; push_cast; exact add_le_add_left (Nat.le_ceil _) _
  obtain ⟨CF, σ₁, hCF, hσ₁, hbF⟩ := DualRB3a.exists_bound_Fp₂ D N
  have hnu := neg_abs_le u.re

  have ha2 : 0 < a ^ 2 := by positivity
  have ha12 : 0 < a₁ ^ 2 := by positivity
  have hc₁ : 0 < Real.pi * a₂⁻¹ ^ 2 := by positivity
  have hc₂ : 0 < Real.pi * a ^ 2 * a₁ ^ 2 := by positivity

  set Φ : ℝ × ℝ × ℝ → ℂ := fun q =>
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (q.1 ^ 2 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2) + 1 / q.2.1 ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |q.2.1 * q.2.2| : ℝ)) : ℂ) *
            (((q.2.1⁻¹ : ℝ) : ℂ) ^ n * (-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((q.1 * q.2.2 / q.2.1 : ℝ)) : ℂ))) ^ δ) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * q.2.2 ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * q.1) * (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * q.2.1 / q.2.2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ) with hΦ
  have hmΦ : Measurable Φ := by
    rw [hΦ]
    have mx : Measurable fun q : ℝ × ℝ × ℝ => q.1 := measurable_fst
    have my1 : Measurable fun q : ℝ × ℝ × ℝ => q.2.1 := measurable_fst.comp measurable_snd
    have my2 : Measurable fun q : ℝ × ℝ × ℝ => q.2.2 := measurable_snd.comp measurable_snd
    have cR : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal
    have m1 : Measurable fun q : ℝ × ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (q.1 ^ 2 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2) + 1 / q.2.1 ^ 2))) : ℂ)) :=
      cR.comp (by fun_prop)
    have m2 : Measurable fun q : ℝ × ℝ × ℝ => (((a₁ ^ 2 * |q.2.1 * q.2.2| : ℝ)) : ℂ) :=
      cR.comp ((my1.mul my2).abs.const_mul _)
    have m3 : Measurable fun q : ℝ × ℝ × ℝ =>
        (((q.2.1⁻¹ : ℝ) : ℂ) ^ n * (-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((q.1 * q.2.2 / q.2.1 : ℝ)) : ℂ))) ^ δ) :=
      ((cR.comp my1.inv).pow_const n).mul
        ((measurable_const.mul (measurable_const.mul (cR.comp ((mx.mul my2).div my1)))).pow_const δ)
    have m4 : Measurable fun q : ℝ × ℝ × ℝ => (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * q.2.2 ^ 2)) : ℂ) :=
      cR.comp (by fun_prop)
    have m5 : Measurable fun q : ℝ × ℝ × ℝ => ArchR.quasiChar u a₀ (q.2.1 * q.2.2)⁻¹ :=
      (DualRB3a.measurable_quasiChar u a₀).comp (my1.mul my2).inv
    have m6 : Measurable fun q : ℝ × ℝ × ℝ => (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) :=
      cR.comp ((my1.mul my2).inv.abs.pow_const 2).inv
    have m7 : Measurable fun q : ℝ × ℝ × ℝ => ArchR.psi (a * q.1) :=
      DualRB3a.continuous_psi.measurable.comp (mx.const_mul a)
    have m8 : Measurable fun q : ℝ × ℝ × ℝ => ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ) :=
      ((DualRB3a.measurable_quasiChar _ _).comp my2).mul (cR.comp my2.abs)
    have m9 : Measurable fun q : ℝ × ℝ × ℝ => D.W (ArchR.diagOne (a * q.2.1 / q.2.2)) :=
      (DualRB3a.measurable_Fp D).comp ((my1.const_mul a).div my2)
    have m10 : Measurable fun q : ℝ × ℝ × ℝ => ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ) :=
      cR.comp ((my2.pow_const 2).mul ((my1.mul my2).abs.pow_const 4).inv)
    exact (((((m1.mul m2).mul m3).mul m4).mul (m5.mul m6)).mul ((m7.mul m8).mul m9)).mul m10

  set r : ℝ := u.re with hr
  set cre : ℝ := P₂.centralExponent.re with hcre
  have hn0' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hb₁ : -(n : ℝ) - r - σ₁ < -1 := by rw [hr]; linarith
  have hb₂ : -(n : ℝ) - r - (N : ℝ) < -1 := by rw [hr]; linarith
  set K₀ : ℝ := CF * a₁ ^ 2 * (|a| * |a₁| * a₂⁻¹) ^ δ with hK₀
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; have := ha₂.le; positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hvg : Integrable (fun v : ℝ => |v| ^ δ * Real.exp (-(Real.pi * a₂⁻¹ ^ 2) * v ^ 2)) := by
    have h1 : Integrable (fun v : ℝ => v ^ δ * Real.exp (-(Real.pi * a₂⁻¹ ^ 2) * v ^ 2)) := by
      refine (integrable_rpow_mul_exp_neg_mul_sq hc₁ (show (-1 : ℝ) < (δ : ℝ) by
        have := Nat.cast_nonneg (α := ℝ) δ; linarith)).congr (Filter.Eventually.of_forall fun v => ?_)
      simp only [Real.rpow_natCast]
    refine h1.norm.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, Real.abs_exp]

  set ZU : ℝ → ℝ → ℝ := fun σ y =>
    K₀ * |a| ^ (-σ) * (y ^ (2 + (δ : ℝ) - r + cre + σ) * (Real.exp (-(Real.pi * a₂⁻¹ ^ 2 / y ^ 2)) * Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y ^ 2)))) with hZU
  have hZUi : ∀ σ : ℝ, Integrable (ZU σ) ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    intro σ
    simp only [hZU]
    exact ((DualRB3a.integrableOn_Zg (2 + (δ : ℝ) - r + cre + σ) hc₁ hc₂).const_mul _)

  set M : ℝ × (ℝ × ℝ) → ℝ := fun p =>
    |p.1| ^ δ * Real.exp (-(Real.pi * a₂⁻¹ ^ 2) * p.1 ^ 2) * ((|p.2.1| ^ (-(n : ℝ) - r - σ₁) * Real.exp (-(Real.pi / p.2.1 ^ 2))) * ZU σ₁ p.2.2) +
    |p.1| ^ δ * Real.exp (-(Real.pi * a₂⁻¹ ^ 2) * p.1 ^ 2) * ((|p.2.1| ^ (-(n : ℝ) - r - (N : ℝ)) * Real.exp (-(Real.pi / p.2.1 ^ 2))) * ZU N p.2.2)
    with hM
  have hMi : Integrable M ((volume : Measure ℝ).prod
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by
    simp only [hM]
    exact (hvg.mul_prod ((DualRB3a.integrable_Y hb₁).mul_prod (hZUi σ₁))).add
      (hvg.mul_prod ((DualRB3a.integrable_Y hb₂).mul_prod (hZUi N)))

  have hG : Integrable (fun p : ℝ × (ℝ × ℝ) => ((|p.2.1| : ℝ) : ℂ) * Φ (p.2.1 * p.1, p.2))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by
    refine Integrable.mono' hMi ?_ ?_
    · exact ((Complex.measurable_ofReal.comp (measurable_fst.comp measurable_snd).abs).mul
        (hmΦ.comp (((measurable_fst.comp measurable_snd).mul measurable_fst).prodMk measurable_snd))).aestronglyMeasurable
    filter_upwards [DualRB3a.ae_good3] with p hp
    obtain ⟨v, y₁, y₂⟩ := p
    obtain ⟨hy₁, hy₂⟩ := hp
    simp only at hy₁ hy₂
    have hY : 0 < |y₁| := abs_pos.2 hy₁
    have hYZ : 0 < |y₁| * y₂ := mul_pos hY hy₂
    have hy12 : y₁ * y₂ ≠ 0 := mul_ne_zero hy₁ hy₂.ne'

    have eE : Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * ((y₁ * v) ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) =
        Real.exp (-(Real.pi * a₂⁻¹ ^ 2) * v ^ 2) * Real.exp (-(Real.pi * a₂⁻¹ ^ 2 / y₂ ^ 2)) *
          Real.exp (-(Real.pi / y₁ ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; field_simp; ring
    have nAff : (Norm.norm ((((y₁⁻¹ : ℝ) : ℂ) ^ n * (-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * ((((y₁ * v) * y₂ / y₁ : ℝ)) : ℂ))) ^ δ))) ≤
        (|y₁| ^ n)⁻¹ * (|a| * |a₁| * a₂⁻¹ * (|v| * y₂)) ^ δ := by
      have hv : (y₁ * v) * y₂ / y₁ = v * y₂ := by field_simp
      rw [hv]
      refine le_of_eq ?_
      simp only [norm_mul, norm_pow, norm_neg, norm_inv, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_inv,
        abs_mul, abs_of_pos hy₂, abs_of_pos ha₂, one_mul, inv_pow]
    have hA : (Norm.norm (((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * ((y₁ * v) ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            (((y₁⁻¹ : ℝ) : ℂ) ^ n * (-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * ((((y₁ * v) * y₂ / y₁ : ℝ)) : ℂ))) ^ δ) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)))) ≤
        (Real.exp (-(Real.pi * a₂⁻¹ ^ 2) * v ^ 2) * Real.exp (-(Real.pi * a₂⁻¹ ^ 2 / y₂ ^ 2)) *
          Real.exp (-(Real.pi / y₁ ^ 2))) * (a₁ ^ 2 * (|y₁| * y₂)) *
          ((|y₁| ^ n)⁻¹ * (|a| * |a₁| * a₂⁻¹ * (|v| * y₂)) ^ δ) * Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp, Real.abs_exp, eE]
      simp only [abs_mul, abs_abs, abs_of_pos hy₂, abs_of_pos ha12]
      gcongr

    have hB : (Norm.norm (ArchR.quasiChar u a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ))) =
        ((|y₁| * y₂) ^ r)⁻¹ * (|y₁| * y₂) ^ 2 := by
      rw [norm_mul, DualRB3a.norm_quasiChar _ _ (inv_ne_zero hy12), Complex.norm_real, Real.norm_eq_abs]
      simp only [abs_inv, abs_pow, abs_abs, abs_mul, abs_of_pos hy₂, inv_pow, inv_inv]
      rw [Real.inv_rpow hYZ.le, ← hr]

    have nC : (Norm.norm (ArchR.centralChar P₂ y₂)) = y₂ ^ cre := by
      rw [ArchR.centralChar, DualRB3a.norm_quasiChar _ _ hy₂.ne', abs_of_pos hy₂, hcre]
    have nF : (Norm.norm (D.W (ArchR.diagOne (a * y₁ / y₂)))) ≤
        CF * (|a| ^ (-σ₁) * (((|y₁| ^ σ₁)⁻¹) * y₂ ^ σ₁) + |a| ^ (-(N : ℝ)) * (((|y₁| ^ (N : ℝ))⁻¹) * y₂ ^ (N : ℝ))) := by
      have hτ : a * y₁ / y₂ ≠ 0 := div_ne_zero (mul_ne_zero ha hy₁) hy₂.ne'
      have h := hbF _ hτ
      rw [show DualRB3a.Fp D (a * y₁ / y₂) = D.W (ArchR.diagOne (a * y₁ / y₂)) from rfl] at h
      refine h.trans (le_of_eq ?_)
      rw [abs_div, abs_mul, abs_of_pos hy₂, Real.div_rpow (by positivity) hy₂.le,
        Real.div_rpow (by positivity) hy₂.le, Real.mul_rpow (abs_nonneg a) hY.le, Real.mul_rpow (abs_nonneg a) hY.le,
        Real.rpow_neg hy₂.le, Real.rpow_neg hy₂.le, Real.rpow_neg (abs_nonneg a), Real.rpow_neg (abs_nonneg a),
        Real.rpow_neg hY.le, Real.rpow_neg hY.le]
      field_simp
    have hC : (Norm.norm (ArchR.psi (a * (y₁ * v)) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            D.W (ArchR.diagOne (a * y₁ / y₂)))) ≤
        (y₂ ^ cre * y₂) *
          (CF * (|a| ^ (-σ₁) * (((|y₁| ^ σ₁)⁻¹) * y₂ ^ σ₁) + |a| ^ (-(N : ℝ)) * (((|y₁| ^ (N : ℝ))⁻¹) * y₂ ^ (N : ℝ)))) := by
      rw [norm_mul, norm_mul, DualRB3a.norm_psi, one_mul, norm_mul, nC, Complex.norm_real, Real.norm_eq_abs, abs_abs,
        abs_of_pos hy₂]
      gcongr

    have hD : (Norm.norm (((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ))) = y₂ ^ 2 * ((|y₁| * y₂) ^ 4)⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      simp only [abs_mul, abs_inv, abs_pow, abs_abs, abs_of_pos hy₂]

    have hsplit : (Norm.norm ((((|y₁| : ℝ)) : ℂ) * Φ (y₁ * v, (y₁, y₂)))) =
        |y₁| * ((Norm.norm (((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * ((y₁ * v) ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            (((y₁⁻¹ : ℝ) : ℂ) ^ n * (-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * ((((y₁ * v) * y₂ / y₁ : ℝ)) : ℂ))) ^ δ) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)))) *
          (Norm.norm (ArchR.quasiChar u a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ))) *
          (Norm.norm (ArchR.psi (a * (y₁ * v)) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            D.W (ArchR.diagOne (a * y₁ / y₂)))) *
          (Norm.norm (((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)))) := by
      simp only [hΦ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs]
    rw [hsplit, hB, hD]
    have step : |y₁| * ((Norm.norm (((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * ((y₁ * v) ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            (((y₁⁻¹ : ℝ) : ℂ) ^ n * (-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * ((((y₁ * v) * y₂ / y₁ : ℝ)) : ℂ))) ^ δ) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)))) *
          (((|y₁| * y₂) ^ r)⁻¹ * (|y₁| * y₂) ^ 2) *
          (Norm.norm (ArchR.psi (a * (y₁ * v)) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            D.W (ArchR.diagOne (a * y₁ / y₂)))) *
          (y₂ ^ 2 * ((|y₁| * y₂) ^ 4)⁻¹)) ≤
        |y₁| * (((Real.exp (-(Real.pi * a₂⁻¹ ^ 2) * v ^ 2) * Real.exp (-(Real.pi * a₂⁻¹ ^ 2 / y₂ ^ 2)) *
          Real.exp (-(Real.pi / y₁ ^ 2))) * (a₁ ^ 2 * (|y₁| * y₂)) *
          ((|y₁| ^ n)⁻¹ * (|a| * |a₁| * a₂⁻¹ * (|v| * y₂)) ^ δ) * Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2))) *
          (((|y₁| * y₂) ^ r)⁻¹ * (|y₁| * y₂) ^ 2) *
          ((y₂ ^ cre * y₂) *
            (CF * (|a| ^ (-σ₁) * (((|y₁| ^ σ₁)⁻¹) * y₂ ^ σ₁) + |a| ^ (-(N : ℝ)) * (((|y₁| ^ (N : ℝ))⁻¹) * y₂ ^ (N : ℝ))))) *
          (y₂ ^ 2 * ((|y₁| * y₂) ^ 4)⁻¹)) := by
      gcongr
    refine step.trans (le_of_eq ?_)

    have eY : ∀ σ : ℝ, |y₁| ^ (-(n : ℝ) - r - σ) = ((|y₁| ^ r)⁻¹ * (|y₁| ^ σ)⁻¹) * (|y₁| ^ n)⁻¹ := by
      intro σ
      rw [show -(n : ℝ) - r - σ = -r + -σ + -(n : ℝ) by ring, Real.rpow_add hY, Real.rpow_add hY, Real.rpow_neg hY.le,
        Real.rpow_neg hY.le, Real.rpow_neg hY.le, Real.rpow_natCast]
    have eZ : ∀ σ : ℝ, y₂ ^ (2 + (δ : ℝ) - r + cre + σ) = y₂ ^ 2 * y₂ ^ δ * (y₂ ^ r)⁻¹ * y₂ ^ cre * y₂ ^ σ := by
      intro σ
      rw [show 2 + (δ : ℝ) - r + cre + σ = ((2 : ℕ) : ℝ) + ((δ : ℕ) : ℝ) + -r + cre + σ by push_cast; ring,
        Real.rpow_add hy₂, Real.rpow_add hy₂, Real.rpow_add hy₂, Real.rpow_add hy₂, Real.rpow_natCast, Real.rpow_natCast,
        Real.rpow_neg hy₂.le]
    have eYZr : ((|y₁| * y₂) ^ r)⁻¹ = (|y₁| ^ r)⁻¹ * (y₂ ^ r)⁻¹ := by
      rw [Real.mul_rpow hY.le hy₂.le, mul_inv]
    simp only [hM, hZU, hK₀, eY, eZ, eYZr, mul_pow]
    field_simp

  have hΦi : Integrable Φ ((volume : Measure ℝ).prod
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) :=
    DualRB3a.integrable_of_dilate _ Φ hmΦ.aestronglyMeasurable (fun z => z.1)
      (DualRB3a.ae_goodY.mono fun z hz => hz.1) hG
  simpa only [hΦ] using hΦi

end
end S_LanglandsTunnell_Converse_integrable_dualConfig_iwasawaIntegrand_detPow_colHarmonic
end P2MW
export P2MW.S_LanglandsTunnell_Converse_integrable_dualConfig_iwasawaIntegrand_detPow_colHarmonic (solution)
