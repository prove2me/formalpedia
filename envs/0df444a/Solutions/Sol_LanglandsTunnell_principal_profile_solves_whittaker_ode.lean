-- Prove2me | solution 1 for LanglandsTunnell.principal_profile_solves_whittaker_ode
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e39f720a-a21f-582f-adbc-b0b671f5468a

import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_principal_profile_solves_whittaker_ode

set_option autoImplicit false

open scoped Real
open MeasureTheory Set Filter Topology
open LanglandsTunnell

noncomputable section

namespace C2PrincipalOde

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
    convert ((hq.pow 2).const_mul π).neg using 1 <;> first | rfl | (norm_num <;> ring1)
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

private theorem I_sq (γ p : ℂ) (y : ℝ) (hy : 0 < y) : (y : ℂ) ^ 2 * I γ p y = I γ (p + 2) y := by
  have hy' : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  simp only [I]
  rw [← integral_const_mul]
  congr 1
  funext t
  simp only [term]
  rw [Complex.cpow_add _ _ hy', Complex.cpow_two]
  ring

private theorem hasDerivAt_gauss_t (y : ℝ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => (Real.exp (-(π * (y / x) ^ 2)) : ℂ))
      (((2 * π * y ^ 2 / t ^ 3) * Real.exp (-(π * (y / t) ^ 2)) : ℝ) : ℂ) t := by
  have hq : HasDerivAt (fun x : ℝ => y / x) (-(y / t ^ 2)) t := by
    convert (hasDerivAt_inv ht.ne').const_mul y using 1 <;> first | rfl | ring
  have hin : HasDerivAt (fun x : ℝ => -(π * (y / x) ^ 2)) (2 * π * y ^ 2 / t ^ 3) t := by
    convert ((hq.pow 2).const_mul π).neg using 1 <;> first | rfl | (norm_num <;> ring1)
  exact (hin.exp.ofReal_comp).congr_deriv (by push_cast; ring)

private theorem hasDerivAt_B (g : ℂ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ g * (Real.exp (-(π * x ^ 2)) : ℂ))
      (g * (t : ℂ) ^ (g - 1) * (Real.exp (-(π * t ^ 2)) : ℂ) +
        (t : ℂ) ^ g * (((-(2 * π * t)) * Real.exp (-(π * t ^ 2)) : ℝ) : ℂ)) t := by
  have h1 := hasDerivAt_ofReal_cpow g t ht
  have h2 : HasDerivAt (fun x : ℝ => (Real.exp (-(π * x ^ 2)) : ℂ))
      ((((-(2 * π * t)) * Real.exp (-(π * t ^ 2)) : ℝ)) : ℂ) t := by
    have hin : HasDerivAt (fun x : ℝ => -(π * x ^ 2)) (-(2 * π * t)) t := by
      convert (((hasDerivAt_id t).pow 2).const_mul π).neg using 1 <;> first | rfl | (norm_num <;> ring1)
    exact (hin.exp.ofReal_comp).congr_deriv (by push_cast; ring)
  exact h1.mul h2

private theorem term_t_deriv (g q : ℂ) (y : ℝ) (hy : 0 < y) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => term g q y x)
      (g * term (g - 1) q y t - ((2 * π : ℝ) : ℂ) * term (g + 1) q y t +
        ((2 * π : ℝ) : ℂ) * term (g - 3) (q + 2) y t) t := by
  have h := (hasDerivAt_B g t ht).mul ((hasDerivAt_gauss_t y t ht).const_mul ((y : ℂ) ^ q))
  refine h.congr_deriv ?_
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have hy' : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  simp only [term]
  rw [Complex.cpow_sub _ _ ht', Complex.cpow_one, Complex.cpow_add _ _ ht', Complex.cpow_one,
    Complex.cpow_sub (g) (3 : ℂ) ht', Complex.cpow_add _ _ hy', Complex.cpow_two,
    show ((3 : ℂ)) = ((3 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  push_cast
  field_simp
  ring

private theorem tendsto_term_zero (g q : ℂ) (y : ℝ) (hy : 0 < y) :
    Tendsto (fun t : ℝ => term g q y t) (𝓝[>] 0) (𝓝 0) := by
  set δ : ℝ := |g.re| + 1 with hδ
  obtain ⟨K, hK0, hK⟩ := exp_neg_div_sq_le δ (by positivity)
  have he : 0 < g.re + δ := by have := neg_le_abs g.re; rw [hδ]; linarith
  have hlim : Tendsto (fun t : ℝ => (y ^ q.re * K / y ^ δ) * t ^ (g.re + δ)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => t ^ (g.re + δ)) (𝓝 0) (𝓝 ((0 : ℝ) ^ (g.re + δ))) :=
      (Real.continuousAt_rpow_const 0 _ (Or.inr he.le)).tendsto
    rw [Real.zero_rpow he.ne'] at h
    simpa using (h.mono_left nhdsWithin_le_nhds).const_mul (y ^ q.re * K / y ^ δ)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht : (0 : ℝ) < t := ht
  rw [norm_term g q y t hy ht]
  have hE := hK y t hy ht
  have hexp1 : Real.exp (-(π * t ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, sq_nonneg t]
  have hA : 0 ≤ t ^ g.re := Real.rpow_nonneg ht.le _
  have hq : 0 ≤ y ^ q.re := Real.rpow_nonneg hy.le _
  calc t ^ g.re * Real.exp (-(π * t ^ 2)) * (y ^ q.re * Real.exp (-(π * (y / t) ^ 2)))
      ≤ t ^ g.re * 1 * (y ^ q.re * (K * (t ^ δ / y ^ δ))) := by gcongr
    _ = (y ^ q.re * K / y ^ δ) * t ^ (g.re + δ) := by
        rw [Real.rpow_add ht g.re δ]; ring

private theorem tendsto_term_atTop (g q : ℂ) (y : ℝ) (hy : 0 < y) :
    Tendsto (fun t : ℝ => term g q y t) atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => y ^ q.re * (t ^ g.re * Real.exp (-π * t))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero g.re π Real.pi_pos).const_mul (y ^ q.re)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht1
  have ht : (0 : ℝ) < t := by linarith
  rw [norm_term g q y t hy ht]
  have h1 : Real.exp (-(π * t ^ 2)) ≤ Real.exp (-π * t) := by
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_pos, mul_nonneg (mul_nonneg Real.pi_pos.le ht.le) (sub_nonneg.2 ht1)]
  have h2 : Real.exp (-(π * (y / t) ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, sq_nonneg (y / t)]
  have hA : 0 ≤ t ^ g.re := Real.rpow_nonneg ht.le _
  have hq : 0 ≤ y ^ q.re := Real.rpow_nonneg hy.le _
  calc t ^ g.re * Real.exp (-(π * t ^ 2)) * (y ^ q.re * Real.exp (-(π * (y / t) ^ 2)))
      ≤ t ^ g.re * Real.exp (-π * t) * (y ^ q.re * 1) := by gcongr
    _ = y ^ q.re * (t ^ g.re * Real.exp (-π * t)) := by ring

private theorem ftc_relation (g q : ℂ) (y : ℝ) (hy : 0 < y) :
    g * I (g - 1) q y - ((2 * π : ℝ) : ℂ) * I (g + 1) q y + ((2 * π : ℝ) : ℂ) * I (g - 3) (q + 2) y = 0 := by
  set H : ℝ → ℂ := fun t => if 0 < t then term g q y t else 0 with hH
  have hH0 : H 0 = 0 := by simp [hH]
  have hHpos : ∀ t : ℝ, 0 < t → H t = term g q y t := fun t ht => by simp [hH, ht]
  have hcont : ContinuousWithinAt H (Ici 0) 0 := by
    have hright : Tendsto H (𝓝[>] 0) (𝓝 0) :=
      (tendsto_term_zero g q y hy).congr'
        (eventually_nhdsWithin_of_forall fun t (ht : (0 : ℝ) < t) => (hHpos t ht).symm)
    have hleft : Tendsto H (𝓝[≤] 0) (𝓝 0) := by
      refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t (ht : t ≤ 0) => ?_)
      simp [hH, not_lt.2 ht]
    have hfull : Tendsto H (𝓝 0) (𝓝 0) := by
      rw [← nhdsLE_sup_nhdsGT (0 : ℝ)]
      exact tendsto_sup.2 ⟨hleft, hright⟩
    rw [ContinuousWithinAt, hH0]
    exact hfull.mono_left nhdsWithin_le_nhds
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt H
      (g * term (g - 1) q y t - ((2 * π : ℝ) : ℂ) * term (g + 1) q y t +
        ((2 * π : ℝ) : ℂ) * term (g - 3) (q + 2) y t) t := by
    intro t ht
    have ht : (0 : ℝ) < t := ht
    refine (term_t_deriv g q y hy t ht).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact hHpos s hs
  have hint : IntegrableOn
      (fun t : ℝ => g * term (g - 1) q y t - ((2 * π : ℝ) : ℂ) * term (g + 1) q y t +
        ((2 * π : ℝ) : ℂ) * term (g - 3) (q + 2) y t) (Ioi 0) :=
    (((integrableOn_term (g - 1) q y hy).const_mul g).sub
      ((integrableOn_term (g + 1) q y hy).const_mul _)).add
        ((integrableOn_term (g - 3) (q + 2) y hy).const_mul _)
  have hatTop : Tendsto H atTop (𝓝 0) := by
    refine (tendsto_term_atTop g q y hy).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (hHpos t ht).symm
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hatTop
  rw [hH0, sub_zero] at hres
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, integral_const_mul] at hres
  · simpa only [I] using hres
  · exact (integrableOn_term (g - 1) q y hy).const_mul _
  · exact (integrableOn_term (g + 1) q y hy).const_mul _
  · exact ((integrableOn_term (g - 1) q y hy).const_mul g).sub
      ((integrableOn_term (g + 1) q y hy).const_mul _)
  · exact (integrableOn_term (g - 3) (q + 2) y hy).const_mul _

private theorem profile_regroup (u₁ u₂ : ℂ) (y : ℝ) (hy : 0 < y) :
    (y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) *
      ((4 : ℂ) * ∫ t in Ioi (0 : ℝ),
        ((t : ℂ) ^ u₁ * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ u₂ * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)) =
    4 * I (u₁ - u₂ - 1) (1 / 2 - (u₁ - u₂) / 2) y := by
  simp only [I]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : (0 : ℝ) < t := ht
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have hy' : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have hquot : (((y / t : ℝ) : ℂ)) ^ u₂ = (y : ℂ) ^ u₂ * ((t : ℂ) ^ u₂)⁻¹ := by
    rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hy.le (inv_nonneg.2 ht.le),
      Complex.ofReal_inv,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg ht.le]; exact Real.pi_ne_zero.symm)]
  have hypow : (y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * (y : ℂ) ^ u₂ = (y : ℂ) ^ (1 / 2 - (u₁ - u₂) / 2) := by
    rw [← Complex.cpow_add _ _ hy']
    congr 1
    ring
  have htpow : (t : ℂ) ^ (u₁ - u₂ - 1) = (t : ℂ) ^ u₁ / (t : ℂ) ^ u₂ / (t : ℂ) := by
    rw [Complex.cpow_sub _ _ ht', Complex.cpow_sub _ _ ht', Complex.cpow_one]
  simp only [term]
  rw [hquot, htpow, ← hypow]
  have h2 : (t : ℂ) ^ u₂ ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero ht']
    exact Complex.exp_ne_zero _
  field_simp

private theorem final_identity (ν y A0 A1 A2 A3 J2 J4 J02 : ℂ)
    (s1 : y ^ 2 * A1 = A0) (s2 : y ^ 2 * A2 = J2) (s3 : y ^ 2 * A3 = J4) (s4 : y ^ 2 * A0 = J02)
    (F : (2 * ν - 2) * J2 - ((2 * π : ℝ) : ℂ) * J02 + ((2 * π : ℝ) : ℂ) * J4 = 0) :
    y ^ 2 * (4 * ((1 / 2 - ν) * ((1 / 2 - ν - 1) * A1 - ((2 * π : ℝ) : ℂ) * A2) -
        ((2 * π : ℝ) : ℂ) * ((1 / 2 - ν + 1) * A2 - ((2 * π : ℝ) : ℂ) * A3)))
      + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((0 : ℝ) : ℂ) * y - 4 * (π : ℂ) ^ 2 * y ^ 2) * (4 * A0) = 0 := by
  push_cast at F ⊢
  linear_combination (4 * (1 / 2 - ν) * (1 / 2 - ν - 1)) * s1
    + (-(8 * (π : ℂ)) * (2 * (1 / 2 - ν) + 1)) * s2 + (16 * (π : ℂ) ^ 2) * s3
    + (-(16 * (π : ℂ) ^ 2)) * s4 + (8 * (π : ℂ)) * F

end C2PrincipalOde

open C2PrincipalOde in

theorem solution (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ)
    (a₂ : ZMod 2) (ha₁ : a₁ = 0) (ha₂ : a₂ = 0) (c ν : ℂ) (hc : c = (u₁ + u₂) / 2)
    (hν : ν = (u₁ - u₂) / 2) (k : ℝ) (hk : k = 0) (f : ℝ → ℂ)
    (hf : ∀ y : ℝ, f y = (y : ℂ) ^ (1 / 2 - c) *
      ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))) :
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0 := by
  subst ha₁ ha₂ hc hν hk
  simp only [signShift_zero, add_zero] at hf

  set γ₀ : ℂ := u₁ - u₂ - 1 with hγ₀
  set m : ℂ := 1 / 2 - (u₁ - u₂) / 2 with hm

  set F : ℝ → ℂ := fun y => 4 * I γ₀ m y with hF
  have hfF : ∀ y : ℝ, 0 < y → f y = F y := fun y hy => by
    rw [hf y, hF]
    exact profile_regroup u₁ u₂ y hy
  have hfF' : ∀ y : ℝ, 0 < y → f =ᶠ[𝓝 y] F := fun y hy =>
    Filter.eventually_of_mem (Ioi_mem_nhds hy) fun z hz => hfF z hz

  set F₁ : ℝ → ℂ := fun y => 4 * (m * I γ₀ (m - 1) y - ((2 * π : ℝ) : ℂ) * I (γ₀ - 2) (m + 1) y) with hF₁
  have hD1 : ∀ y : ℝ, 0 < y → HasDerivAt F (F₁ y) y := fun y hy =>
    (hasDerivAt_I γ₀ m y hy).const_mul 4

  set F₂ : ℝ → ℂ := fun y => 4 * (m * ((m - 1) * I γ₀ (m - 1 - 1) y - ((2 * π : ℝ) : ℂ) * I (γ₀ - 2) (m - 1 + 1) y)
      - ((2 * π : ℝ) : ℂ) * ((m + 1) * I (γ₀ - 2) (m + 1 - 1) y - ((2 * π : ℝ) : ℂ) * I (γ₀ - 2 - 2) (m + 1 + 1) y))
    with hF₂
  have hD2 : ∀ y : ℝ, 0 < y → HasDerivAt F₁ (F₂ y) y := fun y hy =>
    (((hasDerivAt_I γ₀ (m - 1) y hy).const_mul m).sub
      ((hasDerivAt_I (γ₀ - 2) (m + 1) y hy).const_mul _)).const_mul 4

  have hf1 : ∀ y : ℝ, 0 < y → HasDerivAt f (F₁ y) y := fun y hy =>
    (hD1 y hy).congr_of_eventuallyEq (hfF' y hy)
  have hderiv_f : ∀ y : ℝ, 0 < y → deriv f y = F₁ y := fun y hy => (hf1 y hy).deriv
  have hderiv_f' : ∀ y : ℝ, 0 < y → deriv f =ᶠ[𝓝 y] F₁ := fun y hy =>
    Filter.eventually_of_mem (Ioi_mem_nhds hy) fun z hz => hderiv_f z hz
  have hf2 : ∀ y : ℝ, 0 < y → HasDerivAt (deriv f) (F₂ y) y := fun y hy =>
    (hD2 y hy).congr_of_eventuallyEq (hderiv_f' y hy)
  refine ⟨fun y hy => (hf1 y hy).differentiableAt.differentiableWithinAt,
    fun y hy => (hf2 y hy).differentiableAt.differentiableWithinAt, fun y hy => ?_⟩
  rw [(hf2 y hy).deriv, hfF y hy]

  have e1 : I γ₀ (m - 1 - 1) y = I γ₀ (m - 2) y := by congr 1; ring
  have e2 : I (γ₀ - 2) (m - 1 + 1) y = I (γ₀ - 2) m y := by congr 1; ring
  have e3 : I (γ₀ - 2) (m + 1 - 1) y = I (γ₀ - 2) m y := by congr 1; ring
  have e4 : I (γ₀ - 2 - 2) (m + 1 + 1) y = I (γ₀ - 4) (m + 2) y := by congr 1 <;> ring
  simp only [hF₂, hF, e1, e2, e3, e4]

  have s1 : (y : ℂ) ^ 2 * I γ₀ (m - 2) y = I γ₀ m y := by
    rw [I_sq γ₀ (m - 2) y hy]; congr 1; ring
  have s2 : (y : ℂ) ^ 2 * I (γ₀ - 2) m y = I (γ₀ - 2) (m + 2) y := I_sq (γ₀ - 2) m y hy
  have s3 : (y : ℂ) ^ 2 * I (γ₀ - 4) (m + 2) y = I (γ₀ - 4) (m + 4) y := by
    rw [I_sq (γ₀ - 4) (m + 2) y hy]; congr 1; ring
  have s4 : (y : ℂ) ^ 2 * I γ₀ m y = I γ₀ (m + 2) y := I_sq γ₀ m y hy

  have hftc := ftc_relation (γ₀ - 1) (m + 2) y hy
  have r1 : I (γ₀ - 1 - 1) (m + 2) y = I (γ₀ - 2) (m + 2) y := by congr 1; ring
  have r2 : I (γ₀ - 1 + 1) (m + 2) y = I γ₀ (m + 2) y := by congr 1; ring
  have r3 : I (γ₀ - 1 - 3) (m + 2 + 2) y = I (γ₀ - 4) (m + 4) y := by congr 1 <;> ring
  rw [r1, r2, r3] at hftc
  have hγm : γ₀ - 1 = 2 * ((u₁ - u₂) / 2) - 2 := by rw [hγ₀]; ring
  rw [hγm] at hftc
  have hm' : m = 1 / 2 - (u₁ - u₂) / 2 := hm
  rw [hm']
  exact final_identity ((u₁ - u₂) / 2) (y : ℂ) (I γ₀ m y) (I γ₀ (m - 2) y) (I (γ₀ - 2) m y)
    (I (γ₀ - 4) (m + 2) y) (I (γ₀ - 2) (m + 2) y) (I (γ₀ - 4) (m + 4) y) (I γ₀ (m + 2) y)
    s1 s2 s3 s4 hftc

end
end S_LanglandsTunnell_principal_profile_solves_whittaker_ode
end P2MW
export P2MW.S_LanglandsTunnell_principal_profile_solves_whittaker_ode (solution)
