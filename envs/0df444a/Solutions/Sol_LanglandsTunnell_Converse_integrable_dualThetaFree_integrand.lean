-- Prove2me | solution 1 for LanglandsTunnell.Converse.integrable_dualThetaFree_integrand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/070e9702-6f06-5008-afd5-0d73afe50aa0

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_integrable_dualThetaFree_integrand

set_option autoImplicit false

open MeasureTheory Set LanglandsTunnell.Converse
open LanglandsTunnell

noncomputable section

namespace K9D
open Real LanglandsTunnell.Converse.ArchR

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

theorem exists_bound_Fp₂ (N : ℕ) :
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

theorem norm_psi (x : ℝ) : ‖ArchR.psi x‖ = 1 := by
  rw [ArchR.psi, Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

theorem continuous_psi : Continuous ArchR.psi := by
  unfold ArchR.psi; fun_prop

theorem integrable_U0 : Integrable (fun u : ℝ => rexp (-(π * u ^ 2))) := by
  simpa only [neg_mul] using integrable_exp_neg_mul_sq Real.pi_pos

theorem integrable_Um (m : ℕ) : Integrable (fun u : ℝ => |u| ^ m * rexp (-(π * u ^ 2))) := by
  have hm : (-1 : ℝ) < (m : ℝ) := by have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
  refine (integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos hm).norm.congr (ae_of_all _ fun u => ?_)
  simp only [Real.norm_eq_abs, abs_mul, Real.abs_exp, Real.rpow_natCast, abs_pow, neg_mul]

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

theorem integrable_Yprod (n : ℕ) (r σ : ℝ) (h : 1 - n + r - σ < -1) :
    Integrable (fun y : ℝ => |y| * |y|⁻¹ ^ n * |y| ^ r * |y| ^ (-σ) * rexp (-(π * (y ^ 2)⁻¹))) := by
  have hae : ∀ᵐ y : ℝ ∂(volume : Measure ℝ), y ≠ 0 := by
    have : ({0}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.2 (measure_singleton 0)
    filter_upwards [this] with x hx
    simpa using hx
  refine (integrable_Y h).congr ?_
  filter_upwards [hae] with y hy
  have hY : 0 < |y| := abs_pos.2 hy
  rw [show (1 - n + r - σ : ℝ) = 1 + (-(n : ℝ)) + r + (-σ) by ring, Real.rpow_add hY, Real.rpow_add hY, Real.rpow_add hY,
    Real.rpow_one, Real.rpow_neg hY.le, Real.rpow_natCast, inv_pow, div_eq_mul_inv]

theorem integrableOn_Zall (g : ℝ) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    IntegrableOn (fun y : ℝ => y ^ g * rexp (-(c₁ / y ^ 2)) * rexp (-(c₂ * y ^ 2))) (Ioi 0) := by
  set k : ℕ := ⌈|g|⌉₊ with hk
  have hk' : |g| ≤ (k : ℝ) := by rw [hk]; exact Nat.le_ceil _
  have hg : -1 < g + 2 * k := by have := neg_abs_le g; linarith [abs_nonneg g]
  set K : ℝ := (k.factorial : ℝ) * (c₁ ^ k)⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  have h0 : IntegrableOn (fun y : ℝ => K * (y ^ (g + 2 * k) * rexp (-c₂ * y ^ 2))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_sq hc₂ hg).const_mul K
  refine Integrable.mono' h0 ?_ ?_
  · exact ((measurable_id.pow_const _).mul (by fun_prop)).mul (by fun_prop) |>.aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun y (hy : 0 < y) => ?_)
    have hyg : 0 ≤ y ^ g := Real.rpow_nonneg hy.le _
    have hx : 0 < c₁ / y ^ 2 := by positivity
    have hE := exp_neg_le_factorial_mul_inv_pow k hx
    have e1 : ((c₁ / y ^ 2) ^ k)⁻¹ = (c₁ ^ k)⁻¹ * y ^ (2 * (k : ℝ)) := by
      rw [div_pow, inv_div, ← pow_mul, ← Real.rpow_natCast]; push_cast; ring
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_add hy, neg_mul]
    calc y ^ g * rexp (-(c₁ / y ^ 2)) * rexp (-(c₂ * y ^ 2))
        ≤ y ^ g * ((k.factorial : ℝ) * ((c₁ / y ^ 2) ^ k)⁻¹) * rexp (-(c₂ * y ^ 2)) := by gcongr
      _ = K * (y ^ g * y ^ (2 * (k : ℝ)) * rexp (-(c₂ * y ^ 2))) := by rw [e1, hK]; ring

theorem ae_good3 : ∀ᵐ p : ℝ × (ℝ × ℝ) ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0)))),
    p.2.1 ≠ 0 ∧ 0 < p.2.2 := by
  have h0 : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ 0 := by
    have : ({0}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.2 (measure_singleton 0)
    filter_upwards [this] with x hx
    simpa using hx
  have h2 : ∀ᵐ y : ℝ ∂((volume : Measure ℝ).restrict (Ioi 0)), 0 < y := ae_restrict_mem measurableSet_Ioi
  have hB : ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))), p.1 ≠ 0 ∧ 0 < p.2 :=
    ((Measure.quasiMeasurePreserving_fst).ae h0).and ((Measure.quasiMeasurePreserving_snd).ae h2)
  exact (Measure.quasiMeasurePreserving_snd).ae hB

theorem ae_goodZ : ∀ᵐ z : ℝ × ℝ ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))), z.1 ≠ 0 := by
  have h0 : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ 0 := by
    have : ({0}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.2 (measure_singleton 0)
    filter_upwards [this] with x hx
    simpa using hx
  exact (Measure.quasiMeasurePreserving_fst).ae h0

end K9D

end

open K9D Real LanglandsTunnell.Converse.ArchR in
theorem solution
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℝ) (ha : a ≠ 0)
    (β γ : ℂ) (m n : ℕ) (S : ℝ → ℂ) (hSm : Measurable S) (CS : ℝ) (hSb : ∀ y : ℝ, ‖S y‖ ≤ CS)
    (a₁ : ℝ) (ha₁ : a₁ ≠ 0) (a₂ : ℝ) (ha₂ : 0 < a₂) :
    Integrable (fun q : ℝ × ℝ × ℝ =>
        ((q.2.1⁻¹ : ℝ) : ℂ) ^ n * S q.2.1 * ((|q.2.1| : ℝ) : ℂ) ^ β * ((q.2.2 : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * (q.1 ^ 2 / (a₂ * q.2.1) ^ 2))) : ℂ) * ArchR.psi (a * q.1) *
          ((((a₁ * q.2.2 - (a₂ * q.2.2)⁻¹ : ℝ) : ℂ)) + Complex.I * (((q.1 / (a₂ * q.2.1) : ℝ) : ℂ))) ^ m *
          (Real.exp (-(Real.pi * (((a₂ * q.2.2) ^ 2)⁻¹ + (q.2.1 ^ 2)⁻¹ + a₁ ^ 2 * q.2.2 ^ 2))) : ℂ) *
          D.W (ArchR.diagOne (a * (q.2.1 / q.2.2))))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))))) := by

  set N : ℕ := ⌈|β.re|⌉₊ + 3 with hN
  have hN2 : |β.re| + 3 ≤ (N : ℝ) := by
    rw [hN]; push_cast; exact add_le_add_left (Nat.le_ceil _) _
  obtain ⟨CF, σ₁, hCF, hσ₁, hbF⟩ := exists_bound_Fp₂ D N
  have hCS : 0 ≤ CS := le_trans (norm_nonneg _) (hSb 0)
  have hβabs := le_abs_self β.re
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hb₁ : 1 - n + β.re - σ₁ < -1 := by linarith
  have hb₂ : 1 - n + β.re - N < -1 := by linarith
  have ha₂0 : a₂ ≠ 0 := ha₂.ne'
  have hc₁ : 0 < Real.pi / a₂ ^ 2 := by positivity
  have ha₁sq : 0 < a₁ ^ 2 := by positivity
  have hc₂ : 0 < Real.pi * a₁ ^ 2 := by positivity

  have IU0 := integrable_U0
  have IUm := integrable_Um m
  have IY₁ := integrable_Yprod n β.re σ₁ hb₁
  have IY₂ := integrable_Yprod n β.re N hb₂
  set EZ : ℝ → ℝ := fun y => rexp (-(Real.pi * ((a₂ * y) ^ 2)⁻¹)) * rexp (-(Real.pi * (a₁ ^ 2 * y ^ 2))) with hEZ
  have hZ : ∀ g : ℝ, IntegrableOn (fun y : ℝ => y ^ g * EZ y) (Ioi 0) := by
    intro g
    refine (integrableOn_Zall g hc₁ hc₂).congr_fun (fun y (hy : (0:ℝ) < y) => ?_) measurableSet_Ioi
    have e1 : rexp (-(Real.pi / a₂ ^ 2 / y ^ 2)) = rexp (-(Real.pi * ((a₂ * y) ^ 2)⁻¹)) := by
      have : (a₂ * y) ^ 2 = a₂ ^ 2 * y ^ 2 := mul_pow _ _ _
      rw [this, div_div, div_eq_mul_inv]
    have e2 : rexp (-(Real.pi * a₁ ^ 2 * y ^ 2)) = rexp (-(Real.pi * (a₁ ^ 2 * y ^ 2))) := by rw [mul_assoc]
    simp only [hEZ]
    rw [e1, e2, mul_assoc]
  have hZa : ∀ σ : ℝ, IntegrableOn (fun y : ℝ => y ^ γ.re * y ^ σ * y ^ m * EZ y) (Ioi 0) := by
    intro σ
    refine (hZ (γ.re + σ + m)).congr_fun (fun y (hy : (0:ℝ) < y) => ?_) measurableSet_Ioi
    dsimp only
    rw [Real.rpow_add hy, Real.rpow_add hy, Real.rpow_natCast]
  have hZb : ∀ σ : ℝ, IntegrableOn (fun y : ℝ => y ^ γ.re * y ^ σ * (a₂ * y)⁻¹ ^ m * EZ y) (Ioi 0) := by
    intro σ
    refine IntegrableOn.congr_fun ((hZ (γ.re + σ - m)).const_mul (a₂⁻¹ ^ m)) (fun y (hy : (0:ℝ) < y) => ?_) measurableSet_Ioi
    rw [Real.rpow_sub_natCast hy.ne', Real.rpow_add hy, mul_inv, mul_pow, div_eq_mul_inv, ← inv_pow]
    ring
  have hZc : ∀ σ : ℝ, IntegrableOn (fun y : ℝ => y ^ γ.re * y ^ σ * EZ y) (Ioi 0) := by
    intro σ
    refine (hZ (γ.re + σ)).congr_fun (fun y (hy : (0:ℝ) < y) => ?_) measurableSet_Ioi
    dsimp only
    rw [Real.rpow_add hy]

  set f : ℝ × ℝ × ℝ → ℂ := fun q =>
        ((q.2.1⁻¹ : ℝ) : ℂ) ^ n * S q.2.1 * ((|q.2.1| : ℝ) : ℂ) ^ β * ((q.2.2 : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * (q.1 ^ 2 / (a₂ * q.2.1) ^ 2))) : ℂ) * ArchR.psi (a * q.1) *
          ((((a₁ * q.2.2 - (a₂ * q.2.2)⁻¹ : ℝ) : ℂ)) + Complex.I * (((q.1 / (a₂ * q.2.1) : ℝ) : ℂ))) ^ m *
          (Real.exp (-(Real.pi * (((a₂ * q.2.2) ^ 2)⁻¹ + (q.2.1 ^ 2)⁻¹ + a₁ ^ 2 * q.2.2 ^ 2))) : ℂ) *
          D.W (ArchR.diagOne (a * (q.2.1 / q.2.2))) with hf
  have hmf : Measurable f := by
    rw [hf]
    have mx : Measurable fun q : ℝ × ℝ × ℝ => q.1 := measurable_fst
    have my1 : Measurable fun q : ℝ × ℝ × ℝ => q.2.1 := measurable_fst.comp measurable_snd
    have my2 : Measurable fun q : ℝ × ℝ × ℝ => q.2.2 := measurable_snd.comp measurable_snd
    have cR : Measurable (fun x : ℝ => (x : ℂ)) := Complex.measurable_ofReal
    have m1 : Measurable fun q : ℝ × ℝ × ℝ => (((q.2.1⁻¹ : ℝ) : ℂ)) ^ n := (cR.comp my1.inv).pow_const n
    have m2 : Measurable fun q : ℝ × ℝ × ℝ => S q.2.1 := hSm.comp my1
    have m3 : Measurable fun q : ℝ × ℝ × ℝ => (((|q.2.1| : ℝ) : ℂ)) ^ β := (cR.comp my1.abs).pow_const _
    have m4 : Measurable fun q : ℝ × ℝ × ℝ => (((q.2.2 : ℝ) : ℂ)) ^ γ := (cR.comp my2).pow_const _
    have m5 : Measurable fun q : ℝ × ℝ × ℝ => ((Real.exp (-(Real.pi * (q.1 ^ 2 / (a₂ * q.2.1) ^ 2))) : ℝ) : ℂ) :=
      cR.comp (by fun_prop)
    have m6 : Measurable fun q : ℝ × ℝ × ℝ => ArchR.psi (a * q.1) := continuous_psi.measurable.comp (mx.const_mul a)
    have m7 : Measurable fun q : ℝ × ℝ × ℝ =>
        ((((a₁ * q.2.2 - (a₂ * q.2.2)⁻¹ : ℝ) : ℂ)) + Complex.I * (((q.1 / (a₂ * q.2.1) : ℝ) : ℂ))) ^ m :=
      ((cR.comp ((my2.const_mul a₁).sub (my2.const_mul a₂).inv)).add
        (measurable_const.mul (cR.comp (mx.div (my1.const_mul a₂))))).pow_const m
    have m8 : Measurable fun q : ℝ × ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (((a₂ * q.2.2) ^ 2)⁻¹ + (q.2.1 ^ 2)⁻¹ + a₁ ^ 2 * q.2.2 ^ 2))) : ℝ) : ℂ) :=
      cR.comp (by fun_prop)
    have m9 : Measurable fun q : ℝ × ℝ × ℝ => D.W (ArchR.diagOne (a * (q.2.1 / q.2.2))) :=
      (measurable_Fp D).comp ((my1.div my2).const_mul a)
    exact (((((((m1.mul m2).mul m3).mul m4).mul m5).mul m6).mul m7).mul m8).mul m9
  show Integrable f ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))))

  have hG : Integrable (fun p : ℝ × ℝ × ℝ => ((|a₂ * p.2.1| : ℝ) : ℂ) * f (a₂ * p.2.1 * p.1, p.2))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0)))) := by
    have my1 : Measurable fun p : ℝ × ℝ × ℝ => p.2.1 := measurable_fst.comp measurable_snd
    have hmG : Measurable (fun p : ℝ × ℝ × ℝ => ((|a₂ * p.2.1| : ℝ) : ℂ) * f (a₂ * p.2.1 * p.1, p.2)) :=
      (Complex.measurable_ofReal.comp (my1.const_mul a₂).abs).mul (hmf.comp (((my1.const_mul a₂).mul measurable_fst).prodMk measurable_snd))

    set K₁ : ℝ := |a₂| * CS * 3 ^ m * CF * |a| ^ (-σ₁) with hK₁
    set K₂ : ℝ := |a₂| * CS * 3 ^ m * CF * |a| ^ (-(N : ℝ)) with hK₂
    set Y₁ : ℝ → ℝ := fun y => |y| * |y|⁻¹ ^ n * |y| ^ β.re * |y| ^ (-σ₁) * rexp (-(Real.pi * (y ^ 2)⁻¹)) with hY₁
    set Y₂ : ℝ → ℝ := fun y => |y| * |y|⁻¹ ^ n * |y| ^ β.re * |y| ^ (-(N : ℝ)) * rexp (-(Real.pi * (y ^ 2)⁻¹)) with hY₂
    have Ta₁ := ((IU0.mul_prod (IY₁.mul_prod (hZa σ₁))).const_mul (K₁ * |a₁| ^ m))
    have Ta₂ := ((IU0.mul_prod (IY₂.mul_prod (hZa N))).const_mul (K₂ * |a₁| ^ m))
    have Tb₁ := ((IU0.mul_prod (IY₁.mul_prod (hZb σ₁))).const_mul K₁)
    have Tb₂ := ((IU0.mul_prod (IY₂.mul_prod (hZb N))).const_mul K₂)
    have Tc₁ := ((IUm.mul_prod (IY₁.mul_prod (hZc σ₁))).const_mul K₁)
    have Tc₂ := ((IUm.mul_prod (IY₂.mul_prod (hZc N))).const_mul K₂)
    refine Integrable.mono' (((Ta₁.add Ta₂).add (Tb₁.add Tb₂)).add (Tc₁.add Tc₂)) hmG.aestronglyMeasurable ?_
    filter_upwards [ae_good3] with p hp
    obtain ⟨u, y₁, y₂⟩ := p
    obtain ⟨hy₁, hy₂⟩ := hp
    simp only at hy₁ hy₂
    simp only [Pi.add_apply]
    have hY : 0 < |y₁| := abs_pos.2 hy₁
    have hay : a₂ * y₁ ≠ 0 := mul_ne_zero ha₂0 hy₁

    have n1 : ‖(((y₁⁻¹ : ℝ) : ℂ)) ^ n‖ = |y₁|⁻¹ ^ n := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_inv]
    have n3 : ‖(((|y₁| : ℝ) : ℂ)) ^ β‖ = |y₁| ^ β.re := Complex.norm_cpow_eq_rpow_re_of_pos hY _
    have n4 : ‖(((y₂ : ℝ) : ℂ)) ^ γ‖ = y₂ ^ γ.re := Complex.norm_cpow_eq_rpow_re_of_pos hy₂ _
    have n5 : ‖((Real.exp (-(Real.pi * ((a₂ * y₁ * u) ^ 2 / (a₂ * y₁) ^ 2))) : ℝ) : ℂ)‖ = rexp (-(Real.pi * u ^ 2)) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      congr 2; field_simp
    have n7 : ‖((((a₁ * y₂ - (a₂ * y₂)⁻¹ : ℝ) : ℂ)) + Complex.I * (((a₂ * y₁ * u / (a₂ * y₁) : ℝ) : ℂ))) ^ m‖ =
        ‖(((a₁ * y₂ - (a₂ * y₂)⁻¹ : ℝ) : ℂ)) + Complex.I * (((a₂ * y₁ * u / (a₂ * y₁) : ℝ) : ℂ))‖ ^ m := norm_pow _ m
    have nB : ‖(((a₁ * y₂ - (a₂ * y₂)⁻¹ : ℝ) : ℂ)) + Complex.I * (((a₂ * y₁ * u / (a₂ * y₁) : ℝ) : ℂ))‖ ≤
        |a₁| * y₂ + (a₂ * y₂)⁻¹ + |u| := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        mul_div_cancel_left₀ u hay]
      have h1 : |a₁ * y₂ - (a₂ * y₂)⁻¹| ≤ |a₁| * y₂ + (a₂ * y₂)⁻¹ := by
        calc |a₁ * y₂ - (a₂ * y₂)⁻¹| ≤ |a₁ * y₂| + |(a₂ * y₂)⁻¹| := abs_sub _ _
          _ = |a₁| * y₂ + (a₂ * y₂)⁻¹ := by
              rw [abs_mul, abs_of_pos hy₂, abs_of_pos (inv_pos.2 (mul_pos ha₂ hy₂))]
      linarith
    have nBm : ‖(((a₁ * y₂ - (a₂ * y₂)⁻¹ : ℝ) : ℂ)) + Complex.I * (((a₂ * y₁ * u / (a₂ * y₁) : ℝ) : ℂ))‖ ^ m ≤
        3 ^ m * ((|a₁| * y₂) ^ m + (a₂ * y₂)⁻¹ ^ m + |u| ^ m) :=
      (pow_le_pow_left₀ (norm_nonneg _) nB m).trans
        (add_three_pow_le m (by positivity) (inv_nonneg.2 (mul_pos ha₂ hy₂).le) (abs_nonneg u))
    have n8 : ‖((Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2))) : ℝ) : ℂ)‖ =
        rexp (-(Real.pi * (y₁ ^ 2)⁻¹)) * EZ y₂ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), hEZ]
      simp only []
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have n9 : ‖Fp D (a * (y₁ / y₂))‖ ≤
        CF * (|a| ^ (-σ₁) * |y₁| ^ (-σ₁) * y₂ ^ σ₁) + CF * (|a| ^ (-(N:ℝ)) * |y₁| ^ (-(N:ℝ)) * y₂ ^ (N:ℝ)) := by
      have hτ : a * (y₁ / y₂) ≠ 0 := mul_ne_zero ha (div_ne_zero hy₁ hy₂.ne')
      refine (hbF _ hτ).trans (le_of_eq ?_)
      rw [abs_mul, abs_div, abs_of_pos hy₂, Real.mul_rpow (abs_nonneg a) (by positivity),
        Real.mul_rpow (abs_nonneg a) (by positivity), Real.div_rpow hY.le hy₂.le, Real.div_rpow hY.le hy₂.le,
        Real.rpow_neg hy₂.le, Real.rpow_neg hy₂.le, div_inv_eq_mul, div_inv_eq_mul]
      ring
    have n0 : ‖(((|a₂ * y₁| : ℝ)) : ℂ)‖ = |a₂| * |y₁| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_abs, abs_mul]
    simp only [hf, norm_mul, n0, n1, n3, n4, n5, n7, n8, norm_psi, Fp] at n9 ⊢
    have hS := hSb y₁

    refine LE.le.trans_eq (b := |a₂| * |y₁| *
      (|y₁|⁻¹ ^ n * CS * |y₁| ^ β.re * y₂ ^ γ.re * rexp (-(Real.pi * u ^ 2)) * 1 *
        (3 ^ m * ((|a₁| * y₂) ^ m + (a₂ * y₂)⁻¹ ^ m + |u| ^ m)) *
        (rexp (-(Real.pi * (y₁ ^ 2)⁻¹)) * EZ y₂) *
        (CF * (|a| ^ (-σ₁) * |y₁| ^ (-σ₁) * y₂ ^ σ₁) + CF * (|a| ^ (-(N:ℝ)) * |y₁| ^ (-(N:ℝ)) * y₂ ^ (N:ℝ))))) ?_ ?_
    · gcongr
    · simp only [hK₁, hK₂, hY₁, hY₂]
      ring

  exact integrable_of_dilate _ f hmf.aestronglyMeasurable (fun z : ℝ × ℝ => a₂ * z.1)
    (ae_goodZ.mono fun z hz => mul_ne_zero ha₂0 hz) hG

#print axioms solution

end S_LanglandsTunnell_Converse_integrable_dualThetaFree_integrand
end P2MW
export P2MW.S_LanglandsTunnell_Converse_integrable_dualThetaFree_integrand (solution)
