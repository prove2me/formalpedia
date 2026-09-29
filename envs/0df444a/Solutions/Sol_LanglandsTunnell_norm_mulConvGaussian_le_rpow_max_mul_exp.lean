-- Prove2me | solution 1 for LanglandsTunnell.norm_mulConvGaussian_le_rpow_max_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/909e9d19-0863-598f-80f5-1c2a31ffdd91

import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_norm_mulConvGaussian_le_rpow_max_mul_exp

set_option autoImplicit false

open scoped Real
open MeasureTheory Set
open LanglandsTunnell

namespace GaussianConvolutionGrowthInfty

private theorem mellinConvergent_exp_neg_mul_sq (r : ℝ) (hr : 0 < r) (w : ℂ) (hw : 0 < w.re) :
    MellinConvergent (fun t : ℝ => (Real.exp (-(r * t ^ 2)) : ℂ)) w := by
  have h2 : (fun t : ℝ => (Real.exp (-(r * t ^ 2)) : ℂ)) =
      fun t : ℝ => (fun x : ℝ => (Real.exp (-(r * x)) : ℂ)) (t ^ (2 : ℝ)) := by
    funext t
    simp only [Real.rpow_two]
  rw [h2]
  refine (MellinConvergent.comp_rpow (f := fun x : ℝ => (Real.exp (-(r * x)) : ℂ))
    (s := w) (a := (2 : ℝ)) two_ne_zero).mpr ?_
  refine (MellinConvergent.comp_mul_left (f := fun u : ℝ => (Real.exp (-u) : ℂ))
    (s := w / ((2 : ℝ) : ℂ)) hr).mpr ?_
  have hz : 0 < (w / ((2 : ℝ) : ℂ)).re := by
    have : (w / ((2 : ℝ) : ℂ)).re = w.re / 2 := by
      simp
    rw [this]
    exact half_pos hw
  refine (Complex.GammaIntegral_convergent hz).congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  push_cast
  ring

private theorem integrableOn_majorant (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ ((c : ℂ) - 1) • (Real.exp (-(r * t ^ 2)) : ℂ)‖) (Ioi 0) :=
  (mellinConvergent_exp_neg_mul_sq r hr (c : ℂ) (by simpa using hc)).norm

private theorem norm_majorant (r c t : ℝ) (ht : 0 < t) :
    ‖(t : ℂ) ^ ((c : ℂ) - 1) • (Real.exp (-(r * t ^ 2)) : ℂ)‖ = t ^ (c - 1) * Real.exp (-(r * t ^ 2)) := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_of_nonneg (Real.exp_pos _).le]
  simp

private theorem exists_rpow_mul_exp_le (s r : ℝ) (hs : 0 ≤ s) (hr : 0 < r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 < x → x ^ s * Real.exp (-(r * x)) ≤ K := by
  refine ⟨max 1 ((Nat.ceil s).factorial / r ^ Nat.ceil s), le_max_of_le_left zero_le_one,
    fun x hx => ?_⟩
  rcases le_or_gt x 1 with hx1 | hx1
  · refine le_trans ?_ (le_max_left _ _)
    have hp : x ^ s ≤ 1 := Real.rpow_le_one hx.le hx1 hs
    have he : Real.exp (-(r * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hr hx])
    nlinarith [Real.exp_pos (-(r * x)), Real.rpow_nonneg hx.le s]
  · refine le_trans ?_ (le_max_right _ _)
    have h1 : x ^ s ≤ x ^ ((Nat.ceil s : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (Nat.le_ceil s)
    have h2 := Real.pow_div_factorial_le_exp (r * x) (mul_pos hr hx).le (Nat.ceil s)
    have hrn : 0 < r ^ Nat.ceil s := pow_pos hr _
    have hex : 0 < Real.exp (r * x) := Real.exp_pos _
    have hfac : (0 : ℝ) < (Nat.ceil s).factorial := by exact_mod_cast (Nat.ceil s).factorial_pos
    rw [div_le_iff₀ hfac, mul_pow] at h2
    calc x ^ s * Real.exp (-(r * x)) ≤ x ^ ((Nat.ceil s : ℕ) : ℝ) * Real.exp (-(r * x)) := by
          gcongr
      _ = x ^ Nat.ceil s * (Real.exp (r * x))⁻¹ := by rw [Real.rpow_natCast, Real.exp_neg]
      _ ≤ (Nat.ceil s).factorial / r ^ Nat.ceil s := by
          rw [← div_eq_mul_inv, div_le_div_iff₀ hex hrn]
          nlinarith [h2]

private theorem norm_integrand (α β : ℂ) (y t : ℝ) (hy : 0 < y) (ht : 0 < t) :
    ‖((t : ℂ) ^ α * (Real.exp (-(π * t ^ 2)) : ℂ)) *
        (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)‖ =
      t ^ α.re * Real.exp (-(π * t ^ 2)) * (y ^ β.re / t ^ β.re * Real.exp (-(π * (y / t) ^ 2))) / t := by
  rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hy ht), Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_of_nonneg ht.le, Real.div_rpow hy.le ht.le]

private theorem exp_neg_mul_div_sq_le (r δ K : ℝ) (hK : ∀ x : ℝ, 0 < x → x ^ (δ / 2) * Real.exp (-(r * x)) ≤ K)
    (y t : ℝ) (hy : 0 < y) (ht : 0 < t) :
    Real.exp (-(r * (y / t) ^ 2)) ≤ K * (t ^ δ / y ^ δ) := by
  have hq : 0 < y / t := div_pos hy ht
  have hx := hK ((y / t) ^ 2) (by positivity)
  have hpow : ((y / t) ^ 2 : ℝ) ^ (δ / 2) = y ^ δ / t ^ δ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le,
      show ((2 : ℕ) : ℝ) * (δ / 2) = δ by push_cast; ring, Real.div_rpow hy.le ht.le]
  rw [hpow] at hx
  have hpos : 0 < y ^ δ / t ^ δ := by positivity
  have hx' : Real.exp (-(r * (y / t) ^ 2)) ≤ K / (y ^ δ / t ^ δ) := by
    rw [le_div_iff₀ hpos]
    linarith [hx]
  calc Real.exp (-(r * (y / t) ^ 2)) ≤ K / (y ^ δ / t ^ δ) := hx'
    _ = K * (t ^ δ / y ^ δ) := by
        rw [div_div_eq_mul_div, mul_div_assoc]

end GaussianConvolutionGrowthInfty

open GaussianConvolutionGrowthInfty in

theorem solution (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ)
    (a₂ : ZMod 2) :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y →
      ‖(4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)‖
        ≤ C * y ^ (max (u₁ + signShift a₁).re (u₂ + signShift a₂).re) * Real.exp (-(π * y)) := by
  set α : ℂ := u₁ + signShift a₁ with hα
  set β : ℂ := u₂ + signShift a₂ with hβ
  set δ : ℝ := 1 + max 0 (β.re - α.re) with hδ
  have hδ0 : 0 < δ := by
    rw [hδ]
    positivity
  set c : ℝ := α.re - β.re + δ with hc
  have hc0 : 0 < c := by
    have := le_max_right 0 (β.re - α.re)
    rw [hc, hδ]
    linarith
  have hbd : β.re - δ ≤ max α.re β.re := by
    have := le_max_right α.re β.re
    linarith
  have hr : (0 : ℝ) < π / 2 := by positivity
  obtain ⟨K, hK0, hK⟩ := exists_rpow_mul_exp_le (δ / 2) (π / 2) (half_pos hδ0).le hr
  have hg := integrableOn_majorant (π / 2) c hr hc0
  have hJ : 0 ≤ ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ ((c : ℂ) - 1) • (Real.exp (-(π / 2 * t ^ 2)) : ℂ)‖ :=
    integral_nonneg fun _ => norm_nonneg _
  refine ⟨4 * K * ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ ((c : ℂ) - 1) • (Real.exp (-(π / 2 * t ^ 2)) : ℂ)‖,
    fun y hy1 => ?_⟩
  have hy : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy1
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      ‖((t : ℂ) ^ α * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)‖ ≤
        (K * y ^ (β.re - δ) * Real.exp (-(π * y))) *
          ‖(t : ℂ) ^ ((c : ℂ) - 1) • (Real.exp (-(π / 2 * t ^ 2)) : ℂ)‖ := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have htne : t ≠ 0 := ht'.ne'
    rw [norm_integrand α β y t hy ht', norm_majorant (π / 2) c t ht']

    have hsplit : Real.exp (-(π * t ^ 2)) * Real.exp (-(π * (y / t) ^ 2)) ≤
        Real.exp (-(π * y)) * (Real.exp (-(π / 2 * t ^ 2)) * Real.exp (-(π / 2 * (y / t) ^ 2))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hty : t * (y / t) = y := by
        field_simp
      have h2y : 2 * y ≤ t ^ 2 + (y / t) ^ 2 := by
        nlinarith [sq_nonneg (t - y / t), hty]
      nlinarith [Real.pi_pos, h2y]
    have htool := exp_neg_mul_div_sq_le (π / 2) δ K hK y t hy ht'
    have hTb : t ^ β.re ≠ 0 := (Real.rpow_pos_of_pos ht' _).ne'
    have hYd : y ^ δ ≠ 0 := (Real.rpow_pos_of_pos hy _).ne'
    have hB : 0 ≤ t ^ α.re * (y ^ β.re / t ^ β.re) / t := by positivity
    calc t ^ α.re * Real.exp (-(π * t ^ 2)) * (y ^ β.re / t ^ β.re * Real.exp (-(π * (y / t) ^ 2))) / t
        = (t ^ α.re * (y ^ β.re / t ^ β.re) / t) *
            (Real.exp (-(π * t ^ 2)) * Real.exp (-(π * (y / t) ^ 2))) := by ring
      _ ≤ (t ^ α.re * (y ^ β.re / t ^ β.re) / t) *
            (Real.exp (-(π * y)) *
              (Real.exp (-(π / 2 * t ^ 2)) * Real.exp (-(π / 2 * (y / t) ^ 2)))) :=
          mul_le_mul_of_nonneg_left hsplit hB
      _ ≤ (t ^ α.re * (y ^ β.re / t ^ β.re) / t) *
            (Real.exp (-(π * y)) * (Real.exp (-(π / 2 * t ^ 2)) * (K * (t ^ δ / y ^ δ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left htool (Real.exp_pos _).le) (Real.exp_pos _).le) hB
      _ = (K * y ^ (β.re - δ) * Real.exp (-(π * y))) *
            (t ^ (c - 1) * Real.exp (-(π / 2 * t ^ 2))) := by
          have hyd : y ^ (β.re - δ) = y ^ β.re / y ^ δ := Real.rpow_sub hy _ _
          have htc1 : t ^ (c - 1) = t ^ c / t ^ (1 : ℝ) := Real.rpow_sub ht' _ _
          have htcs : t ^ c = t ^ (α.re - β.re) * t ^ δ := by rw [hc]; exact Real.rpow_add ht' _ _
          have htab : t ^ (α.re - β.re) = t ^ α.re / t ^ β.re := Real.rpow_sub ht' _ _
          rw [hyd, htc1, Real.rpow_one, htcs, htab]
          field_simp
  have hbound : ‖∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ α * (Real.exp (-(π * t ^ 2)) : ℂ)) *
      (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)‖ ≤
        (K * y ^ (β.re - δ) * Real.exp (-(π * y))) *
          ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ ((c : ℂ) - 1) • (Real.exp (-(π / 2 * t ^ 2)) : ℂ)‖ := by
    refine (norm_integral_le_of_norm_le (hg.const_mul (K * y ^ (β.re - δ) * Real.exp (-(π * y))))
      ((ae_restrict_mem measurableSet_Ioi).mono hpt)).trans ?_
    rw [integral_const_mul]
  have hymax : y ^ (β.re - δ) ≤ y ^ max α.re β.re := Real.rpow_le_rpow_of_exponent_le hy1 hbd
  calc ‖(4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ), ((t : ℂ) ^ α * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)‖
      = 4 * ‖∫ t in Set.Ioi (0 : ℝ), ((t : ℂ) ^ α * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)‖ := by
        rw [norm_mul]
        congr 1
        simp
    _ ≤ 4 * ((K * y ^ (β.re - δ) * Real.exp (-(π * y))) *
          ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ ((c : ℂ) - 1) • (Real.exp (-(π / 2 * t ^ 2)) : ℂ)‖) :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ ≤ 4 * ((K * y ^ max α.re β.re * Real.exp (-(π * y))) *
          ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ ((c : ℂ) - 1) • (Real.exp (-(π / 2 * t ^ 2)) : ℂ)‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hymax hK0) (Real.exp_pos _).le) hJ) (by norm_num)
    _ = (4 * K * ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ ((c : ℂ) - 1) • (Real.exp (-(π / 2 * t ^ 2)) : ℂ)‖) *
          y ^ max α.re β.re * Real.exp (-(π * y)) := by ring

end S_LanglandsTunnell_norm_mulConvGaussian_le_rpow_max_mul_exp
end P2MW
export P2MW.S_LanglandsTunnell_norm_mulConvGaussian_le_rpow_max_mul_exp (solution)
