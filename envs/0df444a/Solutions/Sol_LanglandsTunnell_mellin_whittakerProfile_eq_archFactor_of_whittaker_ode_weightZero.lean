-- Prove2me | solution 1 for LanglandsTunnell.mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/00cc3635-cce3-58b9-8006-293edf20b57c

import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Theorems.Thm_LanglandsTunnell_mellin_mulConvGaussian_eq_archFactor_principal
import Theorems.Thm_LanglandsTunnell_principal_profile_solves_whittaker_ode
import Theorems.Thm_LanglandsTunnell_principal_profile_exists_ne_zero
import Theorems.Thm_LanglandsTunnell_norm_mulConvGaussian_le_rpow_max_mul_exp
import Theorems.Thm_LanglandsTunnell_linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightZero

set_option autoImplicit false

open scoped Real

open MeasureTheory Set Filter Topology LanglandsTunnell

noncomputable section

namespace WhittakerWeightZero

private def term (γ p : ℂ) (y t : ℝ) : ℂ :=
  ((t : ℂ) ^ γ * (Real.exp (-(π * t ^ 2)) : ℂ)) * ((y : ℂ) ^ p * (Real.exp (-(π * (y / t) ^ 2)) : ℂ))

private def I (γ p : ℂ) (y : ℝ) : ℂ := ∫ t in Ioi (0 : ℝ), term γ p y t

private theorem norm_term (γ p : ℂ) (y t : ℝ) (hy : 0 < y) (ht : 0 < t) :
    ‖term γ p y t‖ =
      t ^ γ.re * Real.exp (-(π * t ^ 2)) * (y ^ p.re * Real.exp (-(π * (y / t) ^ 2))) := by
  simp only [term]
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_of_nonneg (Real.exp_pos _).le]

private theorem continuousOn_term (γ p : ℂ) (y : ℝ) : ContinuousOn (term γ p y) (Ioi 0) := by
  intro t ht
  have ht' : (t : ℝ) ≠ 0 := (ne_of_gt ht)
  apply ContinuousAt.continuousWithinAt
  have h1 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ γ) t :=
    Complex.continuousAt_ofReal_cpow_const t γ (Or.inr ht')
  have h2 : ContinuousAt (fun t : ℝ => (Real.exp (-(π * t ^ 2)) : ℂ)) t :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))).continuousAt
  have h3 : ContinuousAt (fun t : ℝ => (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) t := by
    have hq : ContinuousAt (fun t : ℝ => y / t) t := continuousAt_const.div continuousAt_id ht'
    exact Complex.continuous_ofReal.continuousAt.comp
      (Real.continuous_exp.continuousAt.comp ((hq.pow 2).const_mul π).neg)
  exact (h1.mul h2).mul (continuousAt_const.mul h3)

private theorem exists_rpow_mul_exp_le (s r : ℝ) (hs : 0 ≤ s) (hr : 0 < r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 < x → x ^ s * Real.exp (-(r * x)) ≤ K := by
  refine ⟨max 1 ((Nat.ceil s).factorial / r ^ Nat.ceil s), le_max_of_le_left zero_le_one,
    fun x hx => ?_⟩
  rcases le_or_gt x 1 with hx1 | hx1
  · refine le_trans ?_ (le_max_left _ _)
    have hp : x ^ s ≤ 1 := Real.rpow_le_one hx.le hx1 hs
    have he : Real.exp (-(r * x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    calc x ^ s * Real.exp (-(r * x)) ≤ 1 * 1 :=
          mul_le_mul hp he (Real.exp_pos _).le zero_le_one
      _ = 1 := one_mul 1
  · refine le_trans ?_ (le_max_right _ _)
    set n := Nat.ceil s with hn
    have hsn : s ≤ n := Nat.le_ceil s
    have hxn : x ^ s ≤ x ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le hsn
    rw [Real.rpow_natCast] at hxn
    have hfac : (r * x) ^ n / (n.factorial : ℝ) ≤ Real.exp (r * x) :=
      Real.pow_div_factorial_le_exp (r * x) (by positivity) n
    have hrx : 0 < r * x := by positivity
    have hexp : Real.exp (-(r * x)) = (Real.exp (r * x))⁻¹ := Real.exp_neg _
    rw [hexp]
    have hrn : 0 < r ^ n := pow_pos hr n
    have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    calc x ^ s * (Real.exp (r * x))⁻¹ ≤ x ^ n * (Real.exp (r * x))⁻¹ :=
          mul_le_mul_of_nonneg_right hxn (by positivity)
      _ ≤ x ^ n * ((r * x) ^ n / (n.factorial : ℝ))⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact inv_anti₀ (by positivity) hfac
      _ = (n.factorial : ℝ) / r ^ n := by
          rw [mul_pow]; field_simp

private theorem exp_neg_div_sq_le (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y t : ℝ, 0 < y → 0 < t →
      Real.exp (-(π * (y / t) ^ 2)) ≤ K * (t ^ δ / y ^ δ) := by
  obtain ⟨K, hK0, hK⟩ := exists_rpow_mul_exp_le (δ / 2) π (by positivity) Real.pi_pos
  refine ⟨K, hK0, fun y t hy ht => ?_⟩
  have hq : 0 < y / t := div_pos hy ht
  have hx := hK ((y / t) ^ 2) (by positivity)
  have hpow : (((y / t) ^ 2 : ℝ)) ^ (δ / 2) = y ^ δ / t ^ δ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, Real.div_rpow hy.le ht.le]
    norm_num
    rw [show (2 : ℝ) * (δ / 2) = δ by ring]
  rw [hpow] at hx
  have hyd : 0 < y ^ δ := Real.rpow_pos_of_pos hy δ
  have htd : 0 < t ^ δ := Real.rpow_pos_of_pos ht δ

  rw [div_mul_eq_mul_div, div_le_iff₀ htd] at hx
  rw [mul_div_assoc', le_div_iff₀ hyd]
  linarith [hx]

private theorem integrableOn_term (γ p : ℂ) (y : ℝ) (hy : 0 < y) :
    IntegrableOn (term γ p y) (Ioi 0) := by
  set δ : ℝ := |γ.re| + 1 with hδ
  have hδ0 : 0 ≤ δ := by positivity
  obtain ⟨K, hK0, hK⟩ := exp_neg_div_sq_le δ hδ0
  set c : ℝ := γ.re + δ + 1 with hc
  have hcpos : 0 < c := by
    have : -γ.re ≤ |γ.re| := neg_le_abs γ.re
    rw [hc, hδ]; linarith

  have hmaj : IntegrableOn
      (fun t : ℝ => (y ^ p.re * K / y ^ δ) * (t ^ (c - 1) * Real.exp (-π * t ^ 2))) (Ioi 0) := by
    have hs : (-1 : ℝ) < c - 1 := by linarith
    exact (integrableOn_rpow_mul_exp_neg_mul_sq Real.pi_pos hs).const_mul _
  refine (hmaj.mono' ((continuousOn_term γ p y).aestronglyMeasurable measurableSet_Ioi) ?_)
  refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
  have ht : (0 : ℝ) < t := ht
  rw [norm_term γ p y t hy ht]
  have hE := hK y t hy ht
  have h1 : 0 ≤ t ^ γ.re * Real.exp (-(π * t ^ 2)) := by positivity
  have h2 : 0 ≤ y ^ p.re := Real.rpow_nonneg hy.le _
  calc t ^ γ.re * Real.exp (-(π * t ^ 2)) * (y ^ p.re * Real.exp (-(π * (y / t) ^ 2)))
      ≤ t ^ γ.re * Real.exp (-(π * t ^ 2)) * (y ^ p.re * (K * (t ^ δ / y ^ δ))) := by
        gcongr
    _ = (y ^ p.re * K / y ^ δ) * (t ^ (c - 1) * Real.exp (-π * t ^ 2)) := by
        rw [hc, show γ.re + δ + 1 - 1 = γ.re + δ by ring, Real.rpow_add ht γ.re δ, neg_mul]
        ring

private theorem hasDerivAt_ofReal_cpow (p : ℂ) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ p) (p * (y : ℂ) ^ (p - 1)) y := by
  have h : HasDerivAt (fun z : ℂ => z ^ p) (p * (y : ℂ) ^ (p - 1) * 1) (y : ℂ) :=
    (hasDerivAt_id (y : ℂ)).cpow_const (Complex.ofReal_mem_slitPlane.2 hy)
  have h' := h.comp_ofReal
  simpa using h'

private theorem hasDerivAt_gauss_y (t : ℝ) (_ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun x : ℝ => (Real.exp (-(π * (x / t) ^ 2)) : ℂ))
      (((-(2 * π * y / t ^ 2) * Real.exp (-(π * (y / t) ^ 2)) : ℝ) : ℂ)) y := by
  have hq : HasDerivAt (fun x : ℝ => x / t) (1 / t) y := (hasDerivAt_id y).div_const t
  have hin : HasDerivAt (fun x : ℝ => -(π * (x / t) ^ 2)) (-(2 * π * y / t ^ 2)) y := by
    convert ((hq.pow 2).const_mul π).neg using 1
    all_goals try rfl
    norm_num; ring1
  exact (hin.exp.ofReal_comp).congr_deriv (by push_cast; ring)

private theorem term_y_deriv (γ p : ℂ) (t : ℝ) (ht : 0 < t) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun x : ℝ => term γ p x t)
      (p * term γ (p - 1) y t - ((2 * π : ℝ) : ℂ) * term (γ - 2) (p + 1) y t) y := by
  have hin := (hasDerivAt_ofReal_cpow p y hy).mul (hasDerivAt_gauss_y t ht y)
  have h := hin.const_mul ((t : ℂ) ^ γ * (Real.exp (-(π * t ^ 2)) : ℂ))
  refine h.congr_deriv ?_
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have hy' : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  simp only [term]
  rw [Complex.cpow_sub _ _ ht', Complex.cpow_two, Complex.cpow_add _ _ hy', Complex.cpow_one,
    Complex.cpow_sub _ _ hy', Complex.cpow_one]
  push_cast
  field_simp
  ring

private theorem norm_term_le_of_mem (γ q : ℂ) (y₀ : ℝ) (hy₀ : 0 < y₀) (y t : ℝ) (ht : 0 < t)
    (hy : y ∈ Icc (y₀ / 2) (2 * y₀)) :
    ‖term γ q y t‖ ≤ ((y₀ / 2) ^ q.re + (2 * y₀) ^ q.re) * ‖term γ 0 (y₀ / 2) t‖ := by
  have hh : 0 < y₀ / 2 := by positivity
  have hypos : 0 < y := lt_of_lt_of_le hh hy.1
  rw [norm_term γ q y t hypos ht, norm_term γ 0 (y₀ / 2) t hh ht, Complex.zero_re, Real.rpow_zero,
    one_mul]
  have hpow : y ^ q.re ≤ (y₀ / 2) ^ q.re + (2 * y₀) ^ q.re := by
    rcases le_or_gt 0 q.re with hq | hq
    · have : y ^ q.re ≤ (2 * y₀) ^ q.re := Real.rpow_le_rpow hypos.le hy.2 hq
      linarith [Real.rpow_nonneg hh.le q.re]
    · have : y ^ q.re ≤ (y₀ / 2) ^ q.re := Real.rpow_le_rpow_of_nonpos hh hy.1 hq.le
      linarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * y₀) q.re]
  have hexp : Real.exp (-(π * (y / t) ^ 2)) ≤ Real.exp (-(π * (y₀ / 2 / t) ^ 2)) := by
    apply Real.exp_le_exp.2
    have h1 : y₀ / 2 / t ≤ y / t := div_le_div_of_nonneg_right hy.1 ht.le
    have h2 : (y₀ / 2 / t) ^ 2 ≤ (y / t) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    nlinarith [Real.pi_pos]
  have hA : 0 ≤ t ^ γ.re * Real.exp (-(π * t ^ 2)) := by positivity
  calc t ^ γ.re * Real.exp (-(π * t ^ 2)) * (y ^ q.re * Real.exp (-(π * (y / t) ^ 2)))
      ≤ t ^ γ.re * Real.exp (-(π * t ^ 2)) *
          (((y₀ / 2) ^ q.re + (2 * y₀) ^ q.re) * Real.exp (-(π * (y₀ / 2 / t) ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ hA
        exact mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
    _ = ((y₀ / 2) ^ q.re + (2 * y₀) ^ q.re) *
          (t ^ γ.re * Real.exp (-(π * t ^ 2)) * Real.exp (-(π * (y₀ / 2 / t) ^ 2))) := by ring

private theorem hasDerivAt_I (γ p : ℂ) (y₀ : ℝ) (hy₀ : 0 < y₀) :
    HasDerivAt (I γ p) (p * I γ (p - 1) y₀ - ((2 * π : ℝ) : ℂ) * I (γ - 2) (p + 1) y₀) y₀ := by
  have hh : 0 < y₀ / 2 := by positivity
  set M₁ : ℝ := (y₀ / 2) ^ (p - 1).re + (2 * y₀) ^ (p - 1).re with hM₁
  set M₂ : ℝ := (y₀ / 2) ^ (p + 1).re + (2 * y₀) ^ (p + 1).re with hM₂
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (x : ℝ) (t : ℝ) => term γ p x t)
    (F' := fun (x : ℝ) (t : ℝ) => p * term γ (p - 1) x t - ((2 * π : ℝ) : ℂ) * term (γ - 2) (p + 1) x t)
    (x₀ := y₀) (s := Ioo (y₀ / 2) (2 * y₀))
    (bound := fun t : ℝ => ‖p‖ * M₁ * ‖term γ 0 (y₀ / 2) t‖ + (2 * π) * M₂ * ‖term (γ - 2) 0 (y₀ / 2) t‖)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.eventually_of_mem (Ioi_mem_nhds hy₀) fun x hx =>
      (continuousOn_term γ p x).aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_term γ p y₀ hy₀)
    (((continuousOn_const.mul (continuousOn_term γ (p - 1) y₀)).sub
      (continuousOn_const.mul (continuousOn_term (γ - 2) (p + 1) y₀))).aestronglyMeasurable
        measurableSet_Ioi)
    ?_ ?_ ?_
  · refine key.2.congr_deriv ?_
    simp only [I]
    rw [integral_sub, integral_const_mul, integral_const_mul]
    · exact (integrableOn_term γ (p - 1) y₀ hy₀).const_mul _
    · exact (integrableOn_term (γ - 2) (p + 1) y₀ hy₀).const_mul _
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht x hx => ?_
    have ht : (0 : ℝ) < t := ht
    have hx' : x ∈ Icc (y₀ / 2) (2 * y₀) := Ioo_subset_Icc_self hx
    calc ‖p * term γ (p - 1) x t - ((2 * π : ℝ) : ℂ) * term (γ - 2) (p + 1) x t‖
        ≤ ‖p * term γ (p - 1) x t‖ + ‖((2 * π : ℝ) : ℂ) * term (γ - 2) (p + 1) x t‖ := norm_sub_le _ _
      _ = ‖p‖ * ‖term γ (p - 1) x t‖ + (2 * π) * ‖term (γ - 2) (p + 1) x t‖ := by
          rw [norm_mul, norm_mul, Complex.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π)]
      _ ≤ ‖p‖ * (M₁ * ‖term γ 0 (y₀ / 2) t‖) + (2 * π) * (M₂ * ‖term (γ - 2) 0 (y₀ / 2) t‖) := by
          gcongr
          · exact norm_term_le_of_mem γ (p - 1) y₀ hy₀ x t ht hx'
          · exact norm_term_le_of_mem (γ - 2) (p + 1) y₀ hy₀ x t ht hx'
      _ = ‖p‖ * M₁ * ‖term γ 0 (y₀ / 2) t‖ + (2 * π) * M₂ * ‖term (γ - 2) 0 (y₀ / 2) t‖ := by ring
  · exact ((integrableOn_term γ 0 (y₀ / 2) hh).norm.const_mul _).add
      ((integrableOn_term (γ - 2) 0 (y₀ / 2) hh).norm.const_mul _)
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht x hx => ?_
    exact term_y_deriv γ p t ht x (by linarith [hx.1])

private theorem I_y (γ p : ℂ) (y : ℝ) (hy : 0 < y) : (y : ℂ) * I γ p y = I γ (p + 1) y := by
  have hy' : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  simp only [I]
  rw [← integral_const_mul]
  congr 1
  funext t
  simp only [term]
  rw [Complex.cpow_add _ _ hy', Complex.cpow_one]
  ring

private theorem profile_regroup (α β c : ℂ) (y : ℝ) (hy : 0 < y) :
    (y : ℂ) ^ (1 / 2 - c) *
      ((4 : ℂ) * ∫ t in Ioi (0 : ℝ),
        ((t : ℂ) ^ α * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)) =
    4 * I (α - β - 1) (1 / 2 - c + β) y := by
  simp only [I]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : (0 : ℝ) < t := ht
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have hy' : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have hquot : (((y / t : ℝ) : ℂ)) ^ β = (y : ℂ) ^ β * ((t : ℂ) ^ β)⁻¹ := by
    rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hy.le (inv_nonneg.2 ht.le),
      Complex.ofReal_inv,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg ht.le]; exact Real.pi_ne_zero.symm)]
  have hypow : (y : ℂ) ^ (1 / 2 - c) * (y : ℂ) ^ β = (y : ℂ) ^ (1 / 2 - c + β) := by
    rw [← Complex.cpow_add _ _ hy']
  have htpow : (t : ℂ) ^ (α - β - 1) = (t : ℂ) ^ α / (t : ℂ) ^ β / (t : ℂ) := by
    rw [Complex.cpow_sub _ _ ht', Complex.cpow_sub _ _ ht', Complex.cpow_one]
  simp only [term]
  rw [hquot, htpow, ← hypow]
  have h2 : (t : ℂ) ^ β ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero ht']
    exact Complex.exp_ne_zero _
  field_simp

private theorem hasDerivAt_profile (α β : ℂ) (y : ℝ) (hy : 0 < y) :
    HasDerivAt
      (fun x : ℝ => (4 : ℂ) * ∫ t in Ioi (0 : ℝ),
        ((t : ℂ) ^ α * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((x / t : ℝ) : ℂ) ^ β * (Real.exp (-(π * (x / t) ^ 2)) : ℂ)) / (t : ℂ))
      ((β * ((4 : ℂ) * ∫ t in Ioi (0 : ℝ),
        ((t : ℂ) ^ α * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))
        - 2 * (π : ℂ) * ((4 : ℂ) * ∫ t in Ioi (0 : ℝ),
        ((t : ℂ) ^ α * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (β + 2) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))) / (y : ℂ)) y := by
  have hP : ∀ (β' : ℂ) (x : ℝ), 0 < x →
      ((4 : ℂ) * ∫ t in Ioi (0 : ℝ),
        ((t : ℂ) ^ α * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((x / t : ℝ) : ℂ) ^ β' * (Real.exp (-(π * (x / t) ^ 2)) : ℂ)) / (t : ℂ)) = 4 * I (α - β' - 1) β' x := by
    intro β' x hx
    have h := profile_regroup α β' (1 / 2) x hx
    rwa [sub_self, Complex.cpow_zero, one_mul, zero_add] at h
  have hy' : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have hF : (fun x : ℝ => (4 : ℂ) * ∫ t in Ioi (0 : ℝ),
        ((t : ℂ) ^ α * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((x / t : ℝ) : ℂ) ^ β * (Real.exp (-(π * (x / t) ^ 2)) : ℂ)) / (t : ℂ)) =ᶠ[𝓝 y]
      fun x => 4 * I (α - β - 1) β x :=
    Filter.eventually_of_mem (Ioi_mem_nhds hy) fun x hx => hP β x hx
  refine (((hasDerivAt_I (α - β - 1) β y hy).const_mul (4 : ℂ)).congr_of_eventuallyEq hF).congr_deriv ?_
  rw [hP β y hy, hP (β + 2) y hy]
  have e1 : I (α - (β + 2) - 1) (β + 2) y = I (α - β - 1 - 2) (β + 2) y := by congr 1; ring
  have s1 : (y : ℂ) * I (α - β - 1) (β - 1) y = I (α - β - 1) β y := by
    rw [I_y (α - β - 1) (β - 1) y hy]; congr 1; ring
  have s2 : (y : ℂ) * I (α - β - 1 - 2) (β + 1) y = I (α - β - 1 - 2) (β + 2) y := by
    rw [I_y (α - β - 1 - 2) (β + 1) y hy]; congr 1; ring
  rw [e1, ← s1, ← s2]
  push_cast
  field_simp

private noncomputable def prof (u₁ u₂ : ℂ) (y : ℝ) : ℂ :=
  (4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
    ((t : ℂ) ^ (u₁ + signShift 0) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
      (((y / t : ℝ) : ℂ) ^ (u₂ + signShift 0) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)

private theorem exists_eq_const_mul_profile (u₁ u₂ : ℂ) (f₀ : ℝ → ℂ)
    (hf₀ : DifferentiableOn ℝ f₀ (Set.Ioi 0)) (hf₀' : DifferentiableOn ℝ (deriv f₀) (Set.Ioi 0))
    (hode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv f₀) y
          + (1 / 4 - ((u₁ - u₂) / 2) ^ 2 - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f₀ y = 0)
    (hgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f₀ y‖ ≤ C * y ^ N)
    (hne : ∃ y : ℝ, 0 < y ∧ f₀ y ≠ 0) :
    ∃ A : ℂ, A ≠ 0 ∧ ∀ y : ℝ, 0 < y → f₀ y = A * ((y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ y) := by

  set F : ℝ → ℂ := fun y => (y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ y with hFdef
  have hFsol := principal_profile_solves_whittaker_ode u₁ 0 u₂ 0 rfl rfl ((u₁ + u₂) / 2) ((u₁ - u₂) / 2) rfl rfl
    0 rfl F (fun y => rfl)
  obtain ⟨hFd, hFd', hFeq⟩ := hFsol

  have hFgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖F y‖ ≤ C * y ^ N := by
    obtain ⟨C, hC⟩ := norm_mulConvGaussian_le_rpow_max_mul_exp u₁ 0 u₂ 0
    refine ⟨max C 0, (1 / 2 - (u₁ + u₂) / 2).re + max (u₁ + signShift 0).re (u₂ + signShift 0).re, fun y hy => ?_⟩
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
    have hP := hC y hy
    have hexp : Real.exp (-(π * y)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    have hM : 0 ≤ y ^ (max (u₁ + signShift 0).re (u₂ + signShift 0).re) := Real.rpow_nonneg hy0.le _
    have hP' : ‖prof u₁ u₂ y‖ ≤ max C 0 * y ^ (max (u₁ + signShift 0).re (u₂ + signShift 0).re) := by
      calc ‖prof u₁ u₂ y‖ ≤ C * y ^ (max (u₁ + signShift 0).re (u₂ + signShift 0).re) * Real.exp (-(π * y)) := hP
        _ ≤ max C 0 * y ^ (max (u₁ + signShift 0).re (u₂ + signShift 0).re) * Real.exp (-(π * y)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hM) (Real.exp_pos _).le
        _ ≤ max C 0 * y ^ (max (u₁ + signShift 0).re (u₂ + signShift 0).re) * 1 :=
            mul_le_mul_of_nonneg_left hexp (mul_nonneg (le_max_right _ _) hM)
        _ = _ := mul_one _
    calc ‖F y‖ = ‖(y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2)‖ * ‖prof u₁ u₂ y‖ := norm_mul _ _
      _ = y ^ (1 / 2 - (u₁ + u₂) / 2).re * ‖prof u₁ u₂ y‖ := by rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      _ ≤ y ^ (1 / 2 - (u₁ + u₂) / 2).re
            * (max C 0 * y ^ (max (u₁ + signShift 0).re (u₂ + signShift 0).re)) := by
          gcongr
      _ = max C 0 * y ^ ((1 / 2 - (u₁ + u₂) / 2).re + max (u₁ + signShift 0).re (u₂ + signShift 0).re) := by
          rw [Real.rpow_add hy0]
          ring

  have hfeq : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv f₀) y
        + (1 / 4 - ((u₁ - u₂) / 2) ^ 2 + 2 * (π : ℂ) * ((0 : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
          * f₀ y = 0 := by
    intro y hy
    have e : (2 : ℂ) * (π : ℂ) * ((0 : ℝ) : ℂ) * (y : ℂ) = 0 := by simp
    linear_combination hode y hy + f₀ y * e

  obtain ⟨c₁, c₂, hcne, hlin⟩ :=
    linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam ((u₁ - u₂) / 2) 0 f₀ F hf₀ hf₀' hfeq hgr
      hFd hFd' hFeq hFgr
  obtain ⟨y₀, hy₀, hFy₀⟩ := principal_profile_exists_ne_zero u₁ 0 u₂ 0 ((u₁ + u₂) / 2) F (fun y => rfl)
  have hc₁ : c₁ ≠ 0 := by
    intro h0
    have hc₂ : c₂ ≠ 0 := by
      intro h2
      exact hcne (by rw [h0, h2]; rfl)
    have := hlin y₀ hy₀
    rw [h0, zero_mul, zero_add] at this
    exact hFy₀ ((mul_eq_zero.1 this).resolve_left hc₂)
  obtain ⟨y₁, hy₁, hfy₁⟩ := hne
  refine ⟨-c₂ / c₁, ?_, fun y hy => ?_⟩
  · intro hA
    have h := hlin y₁ hy₁
    have hc₂ : c₂ = 0 := by
      have := div_eq_zero_iff.1 hA
      rcases this with h1 | h1
      · exact neg_eq_zero.1 h1
      · exact absurd h1 hc₁
    rw [hc₂, zero_mul, add_zero] at h
    exact hfy₁ ((mul_eq_zero.1 h).resolve_left hc₁)
  · have h := hlin y hy
    rw [div_mul_eq_mul_div, eq_div_iff hc₁]
    linear_combination h

private theorem mellin_prof (u₁ u₂ s : ℂ) (h₁ : 0 < (s + u₁).re) (h₂ : 0 < (s + u₂).re) :
    mellin (prof u₁ u₂) s = (RealArchParam.principal u₁ 0 u₂ 0).archFactor s :=
  mellin_mulConvGaussian_eq_archFactor_principal u₁ 0 u₂ 0 s
    (by simpa only [signShift_zero, add_zero] using h₁) (by simpa only [signShift_zero, add_zero] using h₂)

private theorem archFactor_principal_ne_zero (v₁ v₂ : ℂ) (b₁ b₂ : ZMod 2) (s : ℂ)
    (h₁ : 0 < (s + (v₁ + signShift b₁)).re) (h₂ : 0 < (s + (v₂ + signShift b₂)).re) :
    (RealArchParam.principal v₁ b₁ v₂ b₂).archFactor s ≠ 0 := by
  simp [RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC,
    Complex.Gammaℝ_ne_zero_of_re_pos h₁, Complex.Gammaℝ_ne_zero_of_re_pos h₂]

private theorem twist_self (u₁ u₂ : ℂ) (a : ZMod 2) :
    (RealArchParam.principal u₁ a u₂ a).twist 0 a = RealArchParam.principal u₁ 0 u₂ 0 := by
  have ha : a + a = 0 := by
    revert a
    decide
  simp [RealArchParam.twist, ha]

private theorem twist_self_add_one (u₁ u₂ : ℂ) (a : ZMod 2) :
    (RealArchParam.principal u₁ a u₂ a).twist 0 (a + 1) = RealArchParam.principal u₁ 1 u₂ 1 := by
  have ha : a + (a + 1) = 1 := by
    revert a
    decide
  simp [RealArchParam.twist, ha]

private theorem archFactor_shift (u₁ u₂ s : ℂ) :
    (RealArchParam.principal u₁ 0 u₂ 0).archFactor (s + 1) = (RealArchParam.principal u₁ 1 u₂ 1).archFactor s := by
  simp only [RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC, signShift_zero, signShift_one,
    Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
    Multiset.map_zero, Multiset.prod_zero]
  ring_nf

private theorem neg_one_pow_mul_self (a : ZMod 2) : (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ a.val = 1 := by
  rw [← mul_pow]
  norm_num

private theorem neg_one_pow_succ_mul (a : ZMod 2) : (-1 : ℂ) ^ (a + 1).val * (-1 : ℂ) ^ a.val = -1 := by
  have h : a = 0 ∨ a = 1 := by
    revert a
    decide
  have e0 : ((0 : ZMod 2) + 1).val = 1 := by decide
  have e1 : ((1 : ZMod 2) + 1).val = 0 := by decide
  have v0 : (0 : ZMod 2).val = 0 := by decide
  have v1 : (1 : ZMod 2).val = 1 := by decide
  rcases h with rfl | rfl
  · rw [e0, v0]
    norm_num
  · rw [e1, v1]
    norm_num

private theorem sqrt_cpow (t : ℝ) (ht : 0 < t) (w : ℂ) :
    ((Real.sqrt t : ℝ) : ℂ) ^ w = (t : ℂ) ^ (w / 2) := by
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hs.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 ht.ne'),
    ← Complex.ofReal_log hs.le, ← Complex.ofReal_log ht.le, Real.log_sqrt ht.le]
  congr 1
  push_cast
  ring

private theorem mellin_symm_W0_and_antisymm_W2 (u₁ u₂ A ρ : ℂ) (a : ZMod 2) (W₀ W₂ : ℂ → ℂ) (f₀ : ℝ → ℂ)
    (hρ : ρ * (2 * A) = 1)
    (hprop : ∀ y : ℝ, 0 < y → f₀ y = A * ((y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ y))
    (hW0p : ∀ t : ℝ, 0 < t → W₀ t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * f₀ t)
    (hW0m : ∀ t : ℝ, 0 < t →
      W₀ (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * ((-1 : ℂ) ^ a.val * f₀ t))
    (hW2p : ∀ t : ℝ, 0 < t →
      W₂ t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
        * (-(1 / (4 * (π : ℂ))) * (2 * (t : ℂ) * deriv f₀ t - 4 * (π : ℂ) * (t : ℂ) * f₀ t)))
    (hW2m : ∀ t : ℝ, 0 < t →
      W₂ (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
        * (-(1 / (4 * (π : ℂ))) * ((-1 : ℂ) ^ a.val * (2 * (t : ℂ) * deriv f₀ t + 4 * (π : ℂ) * (t : ℂ) * f₀ t)))) :
    (∀ s : ℂ, max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (ρ * W₀ t + (-1 : ℂ) ^ a.val * (ρ * W₀ (-t))) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (ρ * W₀ t + (-1 : ℂ) ^ a.val * (ρ * W₀ (-t))) / (t : ℂ)) s
            = ((RealArchParam.principal u₁ a u₂ a).twist 0 a).archFactor s) ∧
      (∀ s : ℂ, max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ (a + 1).val * (ρ * W₂ (-t))) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ (a + 1).val * (ρ * W₂ (-t))) / (t : ℂ)) s
            = ((RealArchParam.principal u₁ a u₂ a).twist 0 (a + 1)).archFactor s) := by

  have hpow : ∀ t : ℝ, 0 < t →
      (t : ℂ) ^ ((u₁ + u₂ + 1) / 2) * (t : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) = (t : ℂ) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    rw [← Complex.cpow_add _ _ ht0]
    rw [show (u₁ + u₂ + 1) / 2 + (1 / 2 - (u₁ + u₂) / 2) = (1 : ℂ) by ring, Complex.cpow_one]
  have hre : ∀ s : ℂ, max (-u₁.re) (-u₂.re) < s.re → 0 < (s + u₁).re ∧ 0 < (s + u₂).re := by
    intro s hs
    have h₁ := le_max_left (-u₁.re) (-u₂.re)
    have h₂ := le_max_right (-u₁.re) (-u₂.re)
    rw [Complex.add_re, Complex.add_re]
    exact ⟨by linarith, by linarith⟩
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  ·
    obtain ⟨h₁, h₂⟩ := hre s hs
    have hEq : ∀ t : ℝ, t ∈ Ioi (0 : ℝ) →
        (t : ℂ) ^ (s - 1) • ((ρ * W₀ t + (-1 : ℂ) ^ a.val * (ρ * W₀ (-t))) / (t : ℂ))
          = (t : ℂ) ^ (s - 1) • prof u₁ u₂ t := by
      intro t ht
      have ht' : (0 : ℝ) < t := ht
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht'.ne'
      congr 1
      rw [hW0p t ht', hW0m t ht', hprop t ht', sqrt_cpow t ht', div_eq_iff ht0]
      linear_combination
        (ρ * (t : ℂ) ^ ((u₁ + u₂ + 1) / 2) * (A * ((t : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ t)))
            * neg_one_pow_mul_self a
          + (2 * ρ * A * prof u₁ u₂ t) * hpow t ht'
          + ((t : ℂ) * prof u₁ u₂ t) * hρ
    have hmel : mellin (fun t : ℝ => (ρ * W₀ t + (-1 : ℂ) ^ a.val * (ρ * W₀ (-t))) / (t : ℂ)) s
        = ((RealArchParam.principal u₁ a u₂ a).twist 0 a).archFactor s := by
      rw [twist_self, ← mellin_prof u₁ u₂ s h₁ h₂]
      simp only [mellin]
      exact setIntegral_congr_fun measurableSet_Ioi hEq
    refine ⟨?_, hmel⟩
    by_contra hcv
    have h0 : mellin (fun t : ℝ => (ρ * W₀ t + (-1 : ℂ) ^ a.val * (ρ * W₀ (-t))) / (t : ℂ)) s = 0 :=
      integral_undef hcv
    rw [hmel, twist_self] at h0
    exact archFactor_principal_ne_zero u₁ u₂ 0 0 s (by simpa only [signShift_zero, add_zero] using h₁)
      (by simpa only [signShift_zero, add_zero] using h₂) h0
  ·
    obtain ⟨h₁, h₂⟩ := hre s hs
    have h₁' : 0 < (s + 1 + u₁).re := by
      rw [Complex.add_re, Complex.add_re, Complex.one_re]
      rw [Complex.add_re] at h₁
      linarith
    have h₂' : 0 < (s + 1 + u₂).re := by
      rw [Complex.add_re, Complex.add_re, Complex.one_re]
      rw [Complex.add_re] at h₂
      linarith
    have hc4 : (-(1 / (4 * (π : ℂ)))) * (4 * (π : ℂ)) = -1 := by
      have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
      field_simp
    have hEq : ∀ t : ℝ, t ∈ Ioi (0 : ℝ) →
        (t : ℂ) ^ (s - 1) • ((ρ * W₂ t + (-1 : ℂ) ^ (a + 1).val * (ρ * W₂ (-t))) / (t : ℂ))
          = (t : ℂ) ^ (s - 1) • ((t : ℂ) ^ (1 : ℂ) • prof u₁ u₂ t) := by
      intro t ht
      have ht' : (0 : ℝ) < t := ht
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht'.ne'
      congr 1
      rw [smul_eq_mul, Complex.cpow_one, hW2p t ht', hW2m t ht', hprop t ht', sqrt_cpow t ht', div_eq_iff ht0]
      linear_combination
        (ρ * (t : ℂ) ^ ((u₁ + u₂ + 1) / 2) * (-(1 / (4 * (π : ℂ))))
              * (2 * (t : ℂ) * deriv f₀ t
                  + 4 * (π : ℂ) * (t : ℂ) * (A * ((t : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ t))))
            * neg_one_pow_succ_mul a
          + (-2 * ρ * (t : ℂ) ^ ((u₁ + u₂ + 1) / 2) * (t : ℂ)
              * (A * ((t : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ t))) * hc4
          + (2 * ρ * A * (t : ℂ) * prof u₁ u₂ t) * hpow t ht'
          + ((t : ℂ) * (t : ℂ) * prof u₁ u₂ t) * hρ
    have hmel : mellin (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ (a + 1).val * (ρ * W₂ (-t))) / (t : ℂ)) s
        = ((RealArchParam.principal u₁ a u₂ a).twist 0 (a + 1)).archFactor s := by
      rw [twist_self_add_one, ← archFactor_shift, ← mellin_prof u₁ u₂ (s + 1) h₁' h₂',
        ← mellin_cpow_smul (prof u₁ u₂) s 1]
      simp only [mellin]
      exact setIntegral_congr_fun measurableSet_Ioi hEq
    refine ⟨?_, hmel⟩
    by_contra hcv
    have h0 : mellin (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ (a + 1).val * (ρ * W₂ (-t))) / (t : ℂ)) s = 0 :=
      integral_undef hcv
    rw [hmel, twist_self_add_one] at h0
    have g₁ : 0 < (s + (u₁ + signShift 1)).re := by
      rw [signShift_one, Complex.add_re, Complex.add_re, Complex.one_re]
      rw [Complex.add_re, Complex.add_re, Complex.one_re] at h₁'
      linarith
    have g₂ : 0 < (s + (u₂ + signShift 1)).re := by
      rw [signShift_one, Complex.add_re, Complex.add_re, Complex.one_re]
      rw [Complex.add_re, Complex.add_re, Complex.one_re] at h₂'
      linarith
    exact archFactor_principal_ne_zero u₁ u₂ 1 1 s g₁ g₂ h0

private theorem mellinConvergent_prof (u₁ u₂ s : ℂ) (h₁ : 0 < (s + u₁).re) (h₂ : 0 < (s + u₂).re) :
    MellinConvergent (prof u₁ u₂) s := by
  by_contra hcv
  have h0 : mellin (prof u₁ u₂) s = 0 := integral_undef hcv
  rw [mellin_prof u₁ u₂ s h₁ h₂] at h0
  exact archFactor_principal_ne_zero u₁ u₂ 0 0 s (by simpa only [signShift_zero, add_zero] using h₁)
    (by simpa only [signShift_zero, add_zero] using h₂) h0

private theorem archFactor_shift_two (u₁ u₂ s : ℂ) (h₂ : s + u₂ ≠ 0) :
    (RealArchParam.principal u₁ 0 (u₂ + 2) 0).archFactor s
      = (RealArchParam.principal u₁ 0 u₂ 0).archFactor s * ((s + u₂) / (2 * (π : ℂ))) := by
  simp only [RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC, signShift_zero, add_zero,
    Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
    Multiset.map_zero, Multiset.prod_zero, mul_one]
  rw [show s + (u₂ + 2) = (s + u₂) + 2 by ring, Complex.Gammaℝ_add_two h₂]
  ring

private theorem mellin_symm_W2 (u₁ u₂ A ρ : ℂ) (a : ZMod 2) (W₂ : ℂ → ℂ) (f₀ : ℝ → ℂ) (hρ : ρ * (2 * A) = 1)
    (hprop : ∀ y : ℝ, 0 < y → f₀ y = A * ((y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ y))
    (hP' : ∀ y : ℝ, 0 < y →
      HasDerivAt (prof u₁ u₂) ((u₂ * prof u₁ u₂ y - 2 * (π : ℂ) * prof u₁ (u₂ + 2) y) / (y : ℂ)) y)
    (hW2p : ∀ t : ℝ, 0 < t →
      W₂ t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
        * (-(1 / (4 * (π : ℂ))) * (2 * (t : ℂ) * deriv f₀ t - 4 * (π : ℂ) * (t : ℂ) * f₀ t)))
    (hW2m : ∀ t : ℝ, 0 < t →
      W₂ (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
        * (-(1 / (4 * (π : ℂ))) * ((-1 : ℂ) ^ a.val * (2 * (t : ℂ) * deriv f₀ t + 4 * (π : ℂ) * (t : ℂ) * f₀ t)))) :
    ∀ s : ℂ, max (-u₁.re) (-u₂.re) < s.re →
      MellinConvergent (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ a.val * (ρ * W₂ (-t))) / (t : ℂ)) s ∧
        mellin (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ a.val * (ρ * W₂ (-t))) / (t : ℂ)) s
          = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ))
              * ((RealArchParam.principal u₁ a u₂ a).twist 0 a).archFactor s := by
  intro s hs

  have hm₁ := le_max_left (-u₁.re) (-u₂.re)
  have hm₂ := le_max_right (-u₁.re) (-u₂.re)
  have h₁ : 0 < (s + u₁).re := by rw [Complex.add_re]; linarith
  have h₂ : 0 < (s + u₂).re := by rw [Complex.add_re]; linarith
  have h₂' : 0 < (s + (u₂ + 2)).re := by
    rw [Complex.add_re, Complex.add_re]
    norm_num
    linarith
  have hne₂ : s + u₂ ≠ 0 := fun h => by rw [h, Complex.zero_re] at h₂; exact lt_irrefl 0 h₂

  set k₁ : ℂ := 1 / 2 - (u₁ + u₂) / 2 with hk₁
  set κ : ℂ := -(ρ * A / (π : ℂ)) with hκ
  set Q : ℝ → ℂ := fun t => κ * ((k₁ + u₂) * prof u₁ u₂ t - 2 * (π : ℂ) * prof u₁ (u₂ + 2) t) with hQ

  have hEq : ∀ t : ℝ, t ∈ Ioi (0 : ℝ) →
      (t : ℂ) ^ (s - 1) • ((ρ * W₂ t + (-1 : ℂ) ^ a.val * (ρ * W₂ (-t))) / (t : ℂ)) = (t : ℂ) ^ (s - 1) • Q t := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht'.ne'

    have hF : HasDerivAt (fun x : ℝ => A * ((x : ℂ) ^ k₁ * prof u₁ u₂ x))
        (A * (k₁ * (t : ℂ) ^ (k₁ - 1) * prof u₁ u₂ t
          + (t : ℂ) ^ k₁ * ((u₂ * prof u₁ u₂ t - 2 * (π : ℂ) * prof u₁ (u₂ + 2) t) / (t : ℂ)))) t :=
      (((hasDerivAt_ofReal_cpow k₁ t ht').mul (hP' t ht'))).const_mul A
    have hev : f₀ =ᶠ[nhds t] fun x : ℝ => A * ((x : ℂ) ^ k₁ * prof u₁ u₂ x) :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht') fun x hx => by rw [hprop x hx]
    have hD : deriv f₀ t = A * (k₁ * (t : ℂ) ^ (k₁ - 1) * prof u₁ u₂ t
        + (t : ℂ) ^ k₁ * ((u₂ * prof u₁ u₂ t - 2 * (π : ℂ) * prof u₁ (u₂ + 2) t) / (t : ℂ))) :=
      (hF.congr_of_eventuallyEq hev).deriv

    have hpow : (t : ℂ) ^ ((u₁ + u₂ + 1) / 2) * (t : ℂ) ^ k₁ = (t : ℂ) := by
      rw [← Complex.cpow_add _ _ ht0, hk₁]
      rw [show (u₁ + u₂ + 1) / 2 + (1 / 2 - (u₁ + u₂) / 2) = (1 : ℂ) by ring, Complex.cpow_one]
    have htw : (t : ℂ) * (t : ℂ) ^ (k₁ - 1) = (t : ℂ) ^ k₁ := by
      rw [Complex.cpow_sub _ _ ht0, Complex.cpow_one]
      field_simp
    have hdiv : (t : ℂ) * ((u₂ * prof u₁ u₂ t - 2 * (π : ℂ) * prof u₁ (u₂ + 2) t) / (t : ℂ))
        = u₂ * prof u₁ u₂ t - 2 * (π : ℂ) * prof u₁ (u₂ + 2) t := mul_div_cancel₀ _ ht0
    congr 1
    rw [hW2p t ht', hW2m t ht', hD, hprop t ht', sqrt_cpow t ht', div_eq_iff ht0, hQ]
    simp only []
    linear_combination
      (ρ * (t : ℂ) ^ ((u₁ + u₂ + 1) / 2) * (-(1 / (4 * (π : ℂ))))
            * (2 * (t : ℂ) * (A * (k₁ * (t : ℂ) ^ (k₁ - 1) * prof u₁ u₂ t
                + (t : ℂ) ^ k₁ * ((u₂ * prof u₁ u₂ t - 2 * (π : ℂ) * prof u₁ (u₂ + 2) t) / (t : ℂ))))
              + 4 * (π : ℂ) * (t : ℂ) * (A * ((t : ℂ) ^ k₁ * prof u₁ u₂ t)))) * neg_one_pow_mul_self a
        + (4 * ρ * (t : ℂ) ^ ((u₁ + u₂ + 1) / 2) * (-(1 / (4 * (π : ℂ)))) * A * k₁ * prof u₁ u₂ t) * htw
        + (4 * ρ * (t : ℂ) ^ ((u₁ + u₂ + 1) / 2) * (-(1 / (4 * (π : ℂ)))) * A * (t : ℂ) ^ k₁) * hdiv
        + (4 * (-(1 / (4 * (π : ℂ)))) * ρ * A
            * ((k₁ + u₂) * prof u₁ u₂ t - 2 * (π : ℂ) * prof u₁ (u₂ + 2) t)) * hpow

  have hcP : MellinConvergent (prof u₁ u₂) s := mellinConvergent_prof u₁ u₂ s h₁ h₂
  have hcP₂ : MellinConvergent (prof u₁ (u₂ + 2)) s := mellinConvergent_prof u₁ (u₂ + 2) s h₁ h₂'
  have hsum := hasMellin_add (hcP.const_smul (κ * (k₁ + u₂))) (hcP₂.const_smul (κ * (-(2 * (π : ℂ)))))
  have hQfun : Q = fun t : ℝ => (κ * (k₁ + u₂)) • prof u₁ u₂ t + (κ * (-(2 * (π : ℂ)))) • prof u₁ (u₂ + 2) t := by
    funext t
    simp only [hQ, smul_eq_mul]
    ring
  have hQconv : MellinConvergent Q s := by rw [hQfun]; exact hsum.1
  have hQmel : mellin Q s = κ * (k₁ + u₂) * mellin (prof u₁ u₂) s
      + κ * (-(2 * (π : ℂ))) * mellin (prof u₁ (u₂ + 2)) s := by
    rw [hQfun, hsum.2, mellin_const_smul, mellin_const_smul, smul_eq_mul, smul_eq_mul]

  have hconv : MellinConvergent (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ a.val * (ρ * W₂ (-t))) / (t : ℂ)) s :=
    (integrableOn_congr_fun hEq measurableSet_Ioi).2 hQconv
  refine ⟨hconv, ?_⟩
  have hmel : mellin (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ a.val * (ρ * W₂ (-t))) / (t : ℂ)) s = mellin Q s := by
    simp only [mellin]
    exact setIntegral_congr_fun measurableSet_Ioi hEq
  rw [hmel, hQmel, mellin_prof u₁ u₂ s h₁ h₂, mellin_prof u₁ (u₂ + 2) s h₁ h₂', archFactor_shift_two u₁ u₂ s hne₂,
    twist_self, hκ, hk₁]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  linear_combination 2 * (2 * s + u₁ + u₂ - 1) * (RealArchParam.principal u₁ 0 u₂ 0).archFactor s * hρ

end WhittakerWeightZero

end

open WhittakerWeightZero in

theorem solution (u₁ u₂ : ℂ)
    (a : ZMod 2) (W₀ W₂ : ℂ → ℂ) (f₀ : ℝ → ℂ)
    (hf₀ : DifferentiableOn ℝ f₀ (Set.Ioi 0)) (hf₀' : DifferentiableOn ℝ (deriv f₀) (Set.Ioi 0))
    (hode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv f₀) y
          + (1 / 4 - ((u₁ - u₂) / 2) ^ 2 - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f₀ y = 0)
    (hgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f₀ y‖ ≤ C * y ^ N)
    (hne : ∃ y : ℝ, 0 < y ∧ f₀ y ≠ 0)
    (hW0p : ∀ t : ℝ, 0 < t → W₀ t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * f₀ t)
    (hW0m : ∀ t : ℝ, 0 < t →
      W₀ (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * ((-1 : ℂ) ^ a.val * f₀ t))
    (hW2p : ∀ t : ℝ, 0 < t →
      W₂ t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
        * (-(1 / (4 * (π : ℂ))) * (2 * (t : ℂ) * deriv f₀ t - 4 * (π : ℂ) * (t : ℂ) * f₀ t)))
    (hW2m : ∀ t : ℝ, 0 < t →
      W₂ (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
        * (-(1 / (4 * (π : ℂ))) * ((-1 : ℂ) ^ a.val * (2 * (t : ℂ) * deriv f₀ t + 4 * (π : ℂ) * (t : ℂ) * f₀ t)))) :
    ∃ ρ : ℂ, ρ ≠ 0 ∧
      (∀ s : ℂ, max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (ρ * W₀ t + (-1 : ℂ) ^ a.val * (ρ * W₀ (-t))) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (ρ * W₀ t + (-1 : ℂ) ^ a.val * (ρ * W₀ (-t))) / (t : ℂ)) s
            = ((RealArchParam.principal u₁ a u₂ a).twist 0 a).archFactor s) ∧
      (∀ s : ℂ, max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ a.val * (ρ * W₂ (-t))) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ a.val * (ρ * W₂ (-t))) / (t : ℂ)) s
            = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ))
                * ((RealArchParam.principal u₁ a u₂ a).twist 0 a).archFactor s) ∧
      (∀ s : ℂ, max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ (a + 1).val * (ρ * W₂ (-t))) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ (a + 1).val * (ρ * W₂ (-t))) / (t : ℂ)) s
            = ((RealArchParam.principal u₁ a u₂ a).twist 0 (a + 1)).archFactor s) := by
  obtain ⟨A, hA, hprop⟩ := exists_eq_const_mul_profile u₁ u₂ f₀ hf₀ hf₀' hode hgr hne
  have h2A : (2 : ℂ) * A ≠ 0 := mul_ne_zero two_ne_zero hA
  have hρ : 1 / (2 * A) * (2 * A) = 1 := one_div_mul_cancel h2A
  have hP' : ∀ y : ℝ, 0 < y →
      HasDerivAt (prof u₁ u₂) ((u₂ * prof u₁ u₂ y - 2 * (π : ℂ) * prof u₁ (u₂ + 2) y) / (y : ℂ)) y := by
    intro y hy
    have h := hasDerivAt_profile (u₁ + signShift 0) (u₂ + signShift 0) y hy
    rw [show u₂ + signShift 0 + 2 = u₂ + 2 + signShift 0 by ring] at h
    have h' : HasDerivAt (prof u₁ u₂)
        (((u₂ + signShift 0) * prof u₁ u₂ y - 2 * (π : ℂ) * prof u₁ (u₂ + 2) y) / (y : ℂ)) y := h
    exact h'.congr_deriv (by rw [signShift_zero, add_zero])
  obtain ⟨h1, h3⟩ := mellin_symm_W0_and_antisymm_W2 u₁ u₂ A (1 / (2 * A)) a W₀ W₂ f₀ hρ hprop hW0p hW0m hW2p hW2m
  exact ⟨1 / (2 * A), one_div_ne_zero h2A, h1,
    mellin_symm_W2 u₁ u₂ A (1 / (2 * A)) a W₂ f₀ hρ hprop hP' hW2p hW2m, h3⟩

end S_LanglandsTunnell_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightZero
end P2MW
export P2MW.S_LanglandsTunnell_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightZero (solution)
