-- Prove2me | solution 1 for LanglandsTunnell.Converse.setIntegral_integral_dite_eq_const_mul_GammaR_mul_integral_triple_of_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/cd06e486-856d-5ecb-bb87-9380543f75b0

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_setIntegral_integral_dite_eq_const_mul_GammaR_mul_integral_triple_of_fibre

set_option autoImplicit false

open MeasureTheory
open Set Real Complex

noncomputable section

namespace KKO9

local notation "μ0" => Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))

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

theorem cpow_ofReal_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (c : ℂ) :
    (((x * y : ℝ)) : ℂ) ^ c = (x : ℂ) ^ c * (y : ℂ) ^ c := by
  push_cast; exact Complex.mul_cpow_ofReal_nonneg hx hy c

theorem cpow_ofReal_inv {x : ℝ} (hx : 0 < x) (c : ℂ) : (((x⁻¹ : ℝ)) : ℂ) ^ c = (x : ℂ) ^ (-c) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ ?_, Complex.cpow_neg]
  rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm

theorem cpow_ofReal_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (c : ℂ) :
    (((x / y : ℝ)) : ℂ) ^ c = (x : ℂ) ^ c * (y : ℂ) ^ (-c) := by
  rw [div_eq_mul_inv, cpow_ofReal_mul hx (inv_pos.2 hy).le, cpow_ofReal_inv hy]

theorem integral_cpow_mul_exp_neg_pi_mul_sq_mul_sq {w : ℂ} (hw : -1 < w.re) {q : ℝ} (hq : q ≠ 0) :
    ∫ a in Ioi (0:ℝ), (a : ℂ) ^ w * (rexp (-(π * a ^ 2 * q ^ 2)) : ℂ) =
      (1 / 2 : ℂ) * ((|q| : ℝ) : ℂ) ^ (-w - 1) * Complex.Gammaℝ (w + 1) := by
  have hQ : 0 < |q| := abs_pos.mpr hq
  have base := integral_cpow_mul_exp_neg_pi_mul_sq (z := w + 1) (by simp; linarith)
  simp only [add_sub_cancel_right] at base

  have hsub := integral_comp_mul_left_Ioi (fun t : ℝ => (t : ℂ) ^ w * (rexp (-(π * t ^ 2)) : ℂ)) (0:ℝ) hQ
  rw [mul_zero] at hsub
  rw [base] at hsub

  have hpt : ∀ a ∈ Ioi (0:ℝ), (((|q| * a : ℝ)) : ℂ) ^ w * (rexp (-(π * (|q| * a) ^ 2)) : ℂ) =
      ((|q| : ℝ) : ℂ) ^ w * ((a : ℂ) ^ w * (rexp (-(π * a ^ 2 * q ^ 2)) : ℂ)) := by
    intro a ha
    rw [cpow_ofReal_mul hQ.le (le_of_lt ha)]
    have : (|q| * a) ^ 2 = a ^ 2 * q ^ 2 := by rw [mul_pow, sq_abs]; ring
    rw [this]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, Complex.real_smul] at hsub
  have hqc : ((|q| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  have hqw : ((|q| : ℝ) : ℂ) ^ w ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hqc h.1
  have hI : ∫ a in Ioi (0:ℝ), (a : ℂ) ^ w * (rexp (-(π * a ^ 2 * q ^ 2)) : ℂ) =
      (((|q| : ℝ) : ℂ) ^ w)⁻¹ * ((((|q| : ℝ)⁻¹ : ℝ) : ℂ) * ((1 / 2 : ℂ) * Complex.Gammaℝ (w + 1))) := by
    rw [← hsub, ← mul_assoc, inv_mul_cancel₀ hqw, one_mul]
  rw [hI, show -w - 1 = -w + (-1 : ℂ) by ring, Complex.cpow_add _ _ hqc, Complex.cpow_neg,
    Complex.cpow_neg_one, Complex.ofReal_inv]
  ring

theorem integral_prod3 (f : ℝ × ℝ × ℝ → ℂ)
    (hf : Integrable f ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod μ0))) :
    ∫ z, f z ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod μ0)) =
      ∫ t : ℝ, ∫ q : ℝ, ∫ p in Ioi (0:ℝ), f (t, q, p) := by
  rw [integral_prod f hf]
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae] with t ht
  exact integral_prod _ ht

theorem ae_q_ne_zero_p_pos :
    ∀ᵐ z : ℝ × ℝ × ℝ ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod μ0)), z.2.1 ≠ 0 ∧ 0 < z.2.2 := by
  have h0 : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 0 := by rw [ae_iff]; simp
  have h1 : ∀ᵐ y ∂(μ0), (0 : ℝ) < y := (ae_restrict_mem measurableSet_Ioi).mono fun y hy => hy
  have h2 : ∀ᵐ yz : ℝ × ℝ ∂((volume : Measure ℝ).prod μ0), yz.1 ≠ 0 ∧ 0 < yz.2 := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := μ0)).ae h0,
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := μ0)).ae h1] with yz a b
    exact ⟨a, b⟩
  exact (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ).prod μ0)).ae h2

end KKO9

end

theorem solution
    (w : ℂ) (hw : -1 < w.re) (C : ℂ) (T T' : ℝ → ℝ → ℝ → ℂ)
    (hF : Integrable (fun r : ℝ × ℝ × ℝ × ℝ =>
        (((r.1 : ℝ) : ℂ) ^ w * (Real.exp (-(Real.pi * r.1 ^ 2 * r.2.2.1 ^ 2)) : ℂ)) * T r.2.1 r.2.2.1 r.2.2.2)
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))))
    (hT' : ∀ t q p : ℝ, q ≠ 0 → 0 < p → T' t q p = ((|q| : ℝ) : ℂ) ^ (-w - 1) * T t q p)
    (Φ : ℝ → ℝ → ℂ)
    (hΦ : ∀ a₁ a₂ : ℝ, a₁ ≠ 0 → 0 < a₂ →
      Φ a₁ a₂ = C * (((a₂⁻¹ : ℝ)) : ℂ) *
        ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (((a₂ : ℝ) : ℂ) ^ w * (Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) : ℂ)) * T (a₁ / a₂) q p) :
    (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ, if ha : a₁ ≠ 0 ∧ 0 < a₂ then Φ a₁ a₂ else 0)
      = C * ((1 / 2 : ℂ) * Complex.Gammaℝ (w + 1)) *
        ∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ), T' t q p := by

  set μ0 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi 0) with hμ0
  set ν : Measure (ℝ × ℝ × ℝ) := (volume : Measure ℝ).prod ((volume : Measure ℝ).prod μ0) with hν
  set F : ℝ × ℝ × ℝ × ℝ → ℂ := fun r =>
    (((r.1 : ℝ) : ℂ) ^ w * (Real.exp (-(Real.pi * r.1 ^ 2 * r.2.2.1 ^ 2)) : ℂ)) * T r.2.1 r.2.2.1 r.2.2.2 with hFdef
  have hF' : Integrable F (μ0.prod ν) := hF

  have stepA : ∀ a₂ : ℝ, 0 < a₂ →
      (∫ a₁ : ℝ, if ha : a₁ ≠ 0 ∧ 0 < a₂ then Φ a₁ a₂ else 0) =
        C * ∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0:ℝ), F (a₂, t, q, p) := by
    intro a₂ ha₂
    set G : ℝ → ℂ := fun t => ∫ q : ℝ, ∫ p in Set.Ioi (0:ℝ), F (a₂, t, q, p) with hG
    have hae : ∀ᵐ a₁ : ℝ, a₁ ≠ 0 := by rw [ae_iff]; simp
    have h1 : (∫ a₁ : ℝ, if ha : a₁ ≠ 0 ∧ 0 < a₂ then Φ a₁ a₂ else 0) =
        ∫ a₁ : ℝ, (C * (((a₂⁻¹ : ℝ)) : ℂ)) * G (a₁ / a₂) := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with a₁ ha₁
      rw [dif_pos ⟨ha₁, ha₂⟩, hΦ a₁ a₂ ha₁ ha₂, hG, hFdef]
    rw [h1, integral_const_mul, Measure.integral_comp_div G a₂, abs_of_pos ha₂, Complex.real_smul, ← mul_assoc,
      mul_assoc C, ← Complex.ofReal_mul, inv_mul_cancel₀ ha₂.ne', Complex.ofReal_one, mul_one]

  have h4 : ∫ r, F r ∂(μ0.prod ν) = ∫ a₂ in Set.Ioi (0:ℝ), ∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0:ℝ), F (a₂, t, q, p) := by
    rw [integral_prod F hF']
    refine integral_congr_ae ?_
    filter_upwards [hF'.prod_right_ae] with a₂ ha
    exact KKO9.integral_prod3 _ ha

  have hswap : ∫ r, F r ∂(μ0.prod ν) = ∫ z, (∫ a₂ in Set.Ioi (0:ℝ), F (a₂, z)) ∂ν := integral_prod_symm F hF'
  have hinner : ∀ᵐ z ∂ν, (∫ a₂ in Set.Ioi (0:ℝ), F (a₂, z)) =
      ((1 / 2 : ℂ) * Complex.Gammaℝ (w + 1)) * T' z.1 z.2.1 z.2.2 := by
    filter_upwards [KKO9.ae_q_ne_zero_p_pos] with z hz
    obtain ⟨hq, hp⟩ := hz
    have : (fun a₂ : ℝ => F (a₂, z)) = fun a₂ : ℝ => (((a₂ : ℝ) : ℂ) ^ w * (rexp (-(Real.pi * a₂ ^ 2 * z.2.1 ^ 2)) : ℂ)) * T z.1 z.2.1 z.2.2 := by
      funext a₂; simp only [hFdef]
    rw [this, integral_mul_const, KKO9.integral_cpow_mul_exp_neg_pi_mul_sq_mul_sq hw hq, hT' z.1 z.2.1 z.2.2 hq hp]
    ring
  have hI : Integrable (fun z => ∫ a₂ in Set.Ioi (0:ℝ), F (a₂, z)) ν := hF'.integral_prod_right
  have hT'i : Integrable (fun z : ℝ × ℝ × ℝ => T' z.1 z.2.1 z.2.2) ν := by
    have hΓ : ((1 / 2 : ℂ) * Complex.Gammaℝ (w + 1)) ≠ 0 :=
      mul_ne_zero (by norm_num) (Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith))
    have := (hI.congr hinner).const_mul (((1 / 2 : ℂ) * Complex.Gammaℝ (w + 1)))⁻¹
    refine this.congr (ae_of_all _ fun z => ?_)
    simp only []
    rw [← mul_assoc, inv_mul_cancel₀ hΓ, one_mul]

  calc (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ, if ha : a₁ ≠ 0 ∧ 0 < a₂ then Φ a₁ a₂ else 0)
      = ∫ a₂ in Set.Ioi (0 : ℝ), C * ∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0:ℝ), F (a₂, t, q, p) :=
        setIntegral_congr_fun measurableSet_Ioi fun a₂ ha₂ => stepA a₂ ha₂
    _ = C * ∫ r, F r ∂(μ0.prod ν) := by rw [integral_const_mul, h4]
    _ = C * ∫ z, ((1 / 2 : ℂ) * Complex.Gammaℝ (w + 1)) * T' z.1 z.2.1 z.2.2 ∂ν := by
        rw [hswap, integral_congr_ae hinner]
    _ = C * ((1 / 2 : ℂ) * Complex.Gammaℝ (w + 1)) * ∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ), T' t q p := by
        rw [integral_const_mul, KKO9.integral_prod3 _ hT'i]
        dsimp only
        ring

end S_LanglandsTunnell_Converse_setIntegral_integral_dite_eq_const_mul_GammaR_mul_integral_triple_of_fibre
end P2MW
export P2MW.S_LanglandsTunnell_Converse_setIntegral_integral_dite_eq_const_mul_GammaR_mul_integral_triple_of_fibre (solution)
