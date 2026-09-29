-- Prove2me | solution 1 for LanglandsTunnell.setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/9fd3b323-7c2f-51d6-8347-778d661d9dd7

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Theorems.Thm_LanglandsTunnell_exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv
import Theorems.Thm_LanglandsTunnell_integrableOn_and_integral_Ioi_exp_neg_pi_mul_sq_add_sq_div_sq_eq_half_exp
import Theorems.Thm_LanglandsTunnell_integral_Ioi_cpow_mul_iteratedDeriv_exp_neg_pi_mul_sq_eq_prod_mul_integral_cpow_sub_mul_exp
import Theorems.Thm_LanglandsTunnell_integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion
import Theorems.Thm_LanglandsTunnell_integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous

set_option autoImplicit false

open MeasureTheory Set Real Complex

namespace FiberAsm

noncomputable def gz (z : ℝ) : ℂ := (Real.exp (-(Real.pi * z ^ 2)) : ℂ)

noncomputable def Hn (n : ℕ) (σ : ℝ) : ℂ := ∫ z : ℝ, ((σ : ℂ) - I * (z : ℂ)) ^ n * gz z

theorem pow_le_exp_half (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k ≤ (k.factorial : ℝ) * Real.exp (1 / (2 * Real.pi)) * Real.exp (Real.pi / 2 * x ^ 2) := by
  have h1 : x ^ k / (k.factorial : ℝ) ≤ Real.exp x := Real.pow_div_factorial_le_exp x hx k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h2 : x ^ k ≤ (k.factorial : ℝ) * Real.exp x := by
    rw [div_le_iff₀ hk] at h1; linarith
  have h3 : x ≤ 1 / (2 * Real.pi) + Real.pi / 2 * x ^ 2 := by
    have hπ := Real.pi_pos
    have : 0 ≤ (Real.pi * x - 1) ^ 2 := sq_nonneg _
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    nlinarith
  calc x ^ k ≤ (k.factorial : ℝ) * Real.exp x := h2
    _ ≤ (k.factorial : ℝ) * Real.exp (1 / (2 * Real.pi) + Real.pi / 2 * x ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h3) hk.le
    _ = _ := by rw [Real.exp_add]; ring

theorem integrable_abs_pow_mul_exp (k : ℕ) : Integrable (fun z : ℝ => |z| ^ k * Real.exp (-(Real.pi * z ^ 2))) := by
  have hb : Integrable (fun z : ℝ => Real.exp (-(Real.pi / 2) * z ^ 2)) := integrable_exp_neg_mul_sq (by positivity)
  refine Integrable.mono' (hb.const_mul ((k.factorial : ℝ) * Real.exp (1 / (2 * Real.pi)))) ?_ ?_
  · exact ((continuous_abs.pow k).mul (by fun_prop)).aestronglyMeasurable
  · refine ae_of_all _ fun z => ?_
    have h := pow_le_exp_half k (abs_nonneg z)
    rw [sq_abs] at h
    have hg : 0 < Real.exp (-(Real.pi * z ^ 2)) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg z) k) hg.le)]
    have hE : Real.exp (Real.pi / 2 * z ^ 2) * Real.exp (-(Real.pi * z ^ 2)) = Real.exp (-(Real.pi / 2) * z ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc |z| ^ k * Real.exp (-(Real.pi * z ^ 2))
        ≤ ((k.factorial : ℝ) * Real.exp (1 / (2 * Real.pi)) * Real.exp (Real.pi / 2 * z ^ 2)) * Real.exp (-(Real.pi * z ^ 2)) :=
          mul_le_mul_of_nonneg_right h hg.le
      _ = (k.factorial : ℝ) * Real.exp (1 / (2 * Real.pi)) * Real.exp (-(Real.pi / 2) * z ^ 2) := by rw [← hE]; ring

theorem add_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) : (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by
  have h : a + b ≤ 2 * max a b := by
    rcases le_total a b with hab | hab
    · rw [max_eq_right hab]; linarith
    · rw [max_eq_left hab]; linarith
  calc (a + b) ^ n ≤ (2 * max a b) ^ n := pow_le_pow_left₀ (by positivity) h n
    _ = 2 ^ n * (max a b) ^ n := by rw [mul_pow]
    _ ≤ 2 ^ n * (a ^ n + b ^ n) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rcases le_total a b with hab | hab
        · rw [max_eq_right hab]; linarith [pow_nonneg ha n]
        · rw [max_eq_left hab]; linarith [pow_nonneg hb n]

theorem integrable_moment (x : ℝ) (n : ℕ) : Integrable (fun z : ℝ => ((x : ℂ) - I * (z : ℂ)) ^ n * gz z) := by
  have hmaj := (((integrable_abs_pow_mul_exp 0).const_mul (2 ^ n * |x| ^ n)).add
    ((integrable_abs_pow_mul_exp n).const_mul ((2 : ℝ) ^ n)))
  refine Integrable.mono' hmaj (by unfold gz; exact Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun z => ?_)
  rw [norm_mul, norm_pow, gz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 : ‖(x : ℂ) - I * (z : ℂ)‖ ≤ |x| + |z| := by
    calc ‖(x : ℂ) - I * (z : ℂ)‖ ≤ ‖(x : ℂ)‖ + ‖I * (z : ℂ)‖ := norm_sub_le _ _
      _ = |x| + |z| := by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have h2 : ‖(x : ℂ) - I * (z : ℂ)‖ ^ n ≤ 2 ^ n * (|x| ^ n + |z| ^ n) :=
    (pow_le_pow_left₀ (norm_nonneg _) h1 n).trans (add_pow_le _ _ (abs_nonneg _) (abs_nonneg _) n)
  simp only [Pi.add_apply, pow_zero, one_mul]
  have := Real.exp_pos (-(Real.pi * z ^ 2))
  nlinarith [h2, pow_nonneg (abs_nonneg z) n, pow_nonneg (abs_nonneg x) n]

theorem eval_fin_two (x : Fin 2 → ℂ) (p : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval x p = ∑ d ∈ p.support, p.coeff d * (x 0 ^ d 0 * x 1 ^ d 1) := by
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fin.prod_univ_two]

theorem gaussAverage_eq_sum (p : MvPolynomial (Fin 2) ℂ) (σ w : ℝ) :
    (∫ z : ℝ, MvPolynomial.eval ![(σ : ℂ) - I * (z : ℂ), (w : ℂ)] p * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) =
      ∑ d ∈ p.support, p.coeff d * ((w : ℂ) ^ d 1 * Hn (d 0) σ) := by
  have hpt : ∀ z : ℝ, MvPolynomial.eval ![(σ : ℂ) - I * (z : ℂ), (w : ℂ)] p * (Real.exp (-(Real.pi * z ^ 2)) : ℂ) =
      ∑ d ∈ p.support, p.coeff d * (w : ℂ) ^ d 1 * (((σ : ℂ) - I * (z : ℂ)) ^ d 0 * gz z) := by
    intro z
    rw [eval_fin_two, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, gz]
    ring
  simp_rw [hpt]
  rw [integral_finset_sum _ fun d _ => (integrable_moment σ (d 0)).const_mul _]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [integral_const_mul, Hn]
  ring

theorem isHomogeneous_fin_two {p : MvPolynomial (Fin 2) ℂ} {m : ℕ} (hp : p.IsHomogeneous m)
    {d : Fin 2 →₀ ℕ} (hd : d ∈ p.support) : d 0 + d 1 = m := by
  have h := hp (MvPolynomial.mem_support_iff.mp hd)
  have h2 : d.degree = m := by
    rw [Finsupp.degree_eq_weight_one]
    exact h
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at h2
  exact h2

theorem eval_one_one (p : MvPolynomial (Fin 2) ℂ) : MvPolynomial.eval ![(1 : ℂ), 1] p = ∑ d ∈ p.support, p.coeff d := by
  rw [eval_fin_two]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp

end FiberAsm

namespace FiberAsm

theorem integral_Ioi_cpow_sub_mul_exp (b : ℂ) (hb : -1 < b.re) (v r : ℝ) (hr : 0 < r) :
    ∫ ρ in Ioi v, ((ρ - v : ℝ) : ℂ) ^ b * (Real.exp (-(r * ρ)) : ℂ) =
      (Real.exp (-(r * v)) : ℂ) * ((1 / r : ℂ) ^ (b + 1) * Complex.Gamma (b + 1)) := by
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun t : ℝ => t + v) (1 : ℝ) (Ioi 0) t :=
    fun t _ => ((hasDerivAt_id t).add_const v).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => t + v) (Ioi 0) := fun x _ y _ h => by simpa using h
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun ρ : ℝ => ((ρ - v : ℝ) : ℂ) ^ b * (Real.exp (-(r * ρ)) : ℂ))
  rw [image_add_const_Ioi, zero_add] at hcv
  rw [hcv]
  have hG := integral_cpow_mul_exp_neg_mul_Ioi (a := b + 1) (by simp; linarith) hr
  rw [← hG, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : 0 < t := ht
  rw [abs_one, one_smul, show t + v - v = t by ring, show b + 1 - 1 = b by ring, Complex.ofReal_exp, Complex.ofReal_exp]
  push_cast
  rw [show -((r : ℂ) * ((t : ℂ) + (v : ℂ))) = -((r : ℂ) * (v : ℂ)) + -((r : ℂ) * (t : ℂ)) by ring, Complex.exp_add]
  ring

theorem integrableOn_Ioi_cpow_sub_mul_exp (b : ℂ) (hb : -1 < b.re) (v r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun ρ : ℝ => ((ρ - v : ℝ) : ℂ) ^ b * (Real.exp (-(r * ρ)) : ℂ)) (Ioi v) := by
  by_contra h
  have h0 := integral_undef h
  rw [integral_Ioi_cpow_sub_mul_exp b hb v r hr] at h0
  have h1 : (Real.exp (-(r * v)) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  have h2 : ((1 / r : ℂ)) ^ (b + 1) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]; left
    exact one_div_ne_zero (by exact_mod_cast hr.ne')
  have h3 : Complex.Gamma (b + 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp only [add_re, one_re]; linarith)
  exact (mul_ne_zero h1 (mul_ne_zero h2 h3)) h0

theorem exp_hyp_le {w : ℝ} (hw : 0 < w) (ρ : ℝ) :
    Real.exp (-(Real.pi * (w ^ 2 + ρ ^ 2 / w ^ 2))) ≤ Real.exp (-(Real.pi / 2) * w ^ 2) * Real.exp (-(Real.pi * ρ)) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have hw2 : 0 < w ^ 2 := by positivity
  have key : Real.pi * ρ ≤ Real.pi * (w ^ 2 / 2 + ρ ^ 2 / w ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    rw [div_add_div _ _ (two_ne_zero) hw2.ne', le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (w ^ 2 - ρ), sq_nonneg ρ]
  nlinarith [key]

theorem integrable_prod_cpow_sub_mul_exp_hyp (b : ℂ) (hb : -1 < b.re) (v : ℝ) (hv : 0 < v) :
    Integrable (fun q : ℝ × ℝ => ((q.2 - v : ℝ) : ℂ) ^ b * (Real.exp (-(Real.pi * (q.1 ^ 2 + q.2 ^ 2 / q.1 ^ 2))) : ℂ))
      (((volume : Measure ℝ).restrict (Ioi 0)).prod ((volume : Measure ℝ).restrict (Ioi v))) := by
  have hw : Integrable (fun w : ℝ => Real.exp (-(Real.pi / 2) * w ^ 2)) ((volume : Measure ℝ).restrict (Ioi 0)) :=
    (integrable_exp_neg_mul_sq (by positivity)).integrableOn
  have hρ : Integrable (fun ρ : ℝ => ‖((ρ - v : ℝ) : ℂ) ^ b * (Real.exp (-(Real.pi * ρ)) : ℂ)‖)
      ((volume : Measure ℝ).restrict (Ioi v)) := (integrableOn_Ioi_cpow_sub_mul_exp b hb v Real.pi Real.pi_pos).norm
  have hprod := hw.mul_prod hρ
  have hmeas : Measurable (fun q : ℝ × ℝ => ((q.2 - v : ℝ) : ℂ) ^ b *
      (Real.exp (-(Real.pi * (q.1 ^ 2 + q.2 ^ 2 / q.1 ^ 2))) : ℂ)) :=
    ((Complex.measurable_ofReal.comp (measurable_snd.sub_const v)).pow_const b).mul
      (Complex.measurable_ofReal.comp (by fun_prop))
  refine Integrable.mono' hprod hmeas.aestronglyMeasurable ?_
  have h1 : ∀ᵐ q : ℝ × ℝ ∂(((volume : Measure ℝ).restrict (Ioi 0)).prod ((volume : Measure ℝ).restrict (Ioi v))), 0 < q.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [h1] with q hq
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  have := exp_hyp_le hq q.2
  have hn := norm_nonneg (((q.2 - v : ℝ) : ℂ) ^ b)
  nlinarith

theorem integral_subst (b : ℂ) (v : ℝ) {w : ℝ} (hw : 0 < w) :
    ∫ σ in Ioi (v / w), ((σ * w - v : ℝ) : ℂ) ^ b * (Real.exp (-(Real.pi * σ ^ 2)) : ℂ) =
      (w : ℂ)⁻¹ * ∫ ρ in Ioi v, ((ρ - v : ℝ) : ℂ) ^ b * (Real.exp (-(Real.pi * (ρ / w) ^ 2)) : ℂ) := by
  have h := integral_comp_mul_left_Ioi (fun ρ : ℝ => ((ρ - v : ℝ) : ℂ) ^ b * (Real.exp (-(Real.pi * (ρ / w) ^ 2)) : ℂ))
    (v / w) hw
  rw [mul_div_cancel₀ _ hw.ne', Complex.real_smul, ofReal_inv] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun σ _ => ?_
  show _ = ((w * σ - v : ℝ) : ℂ) ^ b * (Real.exp (-(Real.pi * (w * σ / w) ^ 2)) : ℂ)
  rw [mul_comm w σ, mul_div_cancel_right₀ _ hw.ne']

end FiberAsm

namespace FiberAsm

theorem prod_mul_Gamma (a : ℂ) : ∀ n : ℕ, (∀ k : ℕ, k < n → a - (k : ℂ) ≠ 0) →
    (∏ k ∈ Finset.range n, (a - (k : ℂ))) * Complex.Gamma (a - (n : ℂ) + 1) = Complex.Gamma (a + 1) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hk
    rw [Finset.prod_range_succ]
    have h1 : a - ((n + 1 : ℕ) : ℂ) + 1 = a - (n : ℂ) := by push_cast; ring
    have h2 : Complex.Gamma (a - (n : ℂ) + 1) = (a - (n : ℂ)) * Complex.Gamma (a - (n : ℂ)) :=
      Complex.Gamma_add_one _ (hk n (Nat.lt_succ_self n))
    rw [h1, ← ih (fun k hk' => hk k (Nat.lt_succ_of_lt hk')), h2]
    ring

theorem zpow_collapse {w : ℂ} (hw : w ≠ 0) {m n : ℕ} (hn : n ≤ m) :
    w ^ ((1 : ℤ) - (m : ℤ)) * w ^ (m - n) * (-w) ^ n * w⁻¹ = (-1) ^ n := by
  have h1 : w ^ (m - n) * w ^ n = w ^ m := by rw [← pow_add, Nat.sub_add_cancel hn]
  have h2 : w ^ ((1 : ℤ) - (m : ℤ)) * w ^ m = w := by
    rw [← zpow_natCast, ← zpow_add₀ hw]; simp
  calc w ^ ((1 : ℤ) - (m : ℤ)) * w ^ (m - n) * (-w) ^ n * w⁻¹
      = (w ^ ((1 : ℤ) - (m : ℤ)) * (w ^ (m - n) * w ^ n)) * w⁻¹ * (-1) ^ n := by rw [neg_pow w n]; ring
    _ = (-1) ^ n := by rw [h1, h2, mul_inv_cancel₀ hw, one_mul]

theorem zpow_collapse' {w : ℂ} (hw : w ≠ 0) {m n : ℕ} (hn : n ≤ m) :
    w ^ ((1 : ℤ) - (m : ℤ)) * w ^ (m - n) = w ^ ((1 : ℤ) - (n : ℤ)) := by
  rw [← zpow_natCast, ← zpow_add₀ hw, Nat.cast_sub hn]
  congr 1; ring

theorem const_collapse (a : ℂ) (n : ℕ) :
    ((-(2 * (Real.pi : ℂ)))⁻¹) ^ n * (-1) ^ n * ((1 / (2 * Real.pi) : ℂ) ^ (a - (n : ℂ) + 1)) =
      (2 * (Real.pi : ℂ)) ^ (-a - 1) := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have harg : (2 * (Real.pi : ℂ)).arg ≠ Real.pi := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_ne_zero.symm
  have h1 : ((-(2 * (Real.pi : ℂ)))⁻¹) ^ n * (-1) ^ n = (2 * (Real.pi : ℂ)) ^ (-(n : ℂ)) := by
    rw [← mul_pow, show (-(2 * (Real.pi : ℂ)))⁻¹ * -1 = (2 * (Real.pi : ℂ))⁻¹ by field_simp, inv_pow,
      cpow_neg, cpow_natCast]
  have h2 : ((1 / (2 * Real.pi) : ℂ)) ^ (a - (n : ℂ) + 1) = (2 * (Real.pi : ℂ)) ^ (-(a - (n : ℂ) + 1)) := by
    rw [cpow_neg, one_div]
    push_cast
    rw [inv_cpow _ _ harg]
  rw [h1, h2, ← cpow_add _ _ hπ]
  congr 1; ring

def R (v : ℝ) : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}

noncomputable def Qn (m : ℕ) (a : ℂ) (v : ℝ) (n : ℕ) (q : ℝ × ℝ) : ℂ :=
  ((q.1 * q.2 - v : ℝ) : ℂ) ^ a * (q.2 : ℂ) ^ ((1 : ℤ) - (m : ℤ)) *
    (Real.exp (-(Real.pi * (q.1 ^ 2 + q.2 ^ 2))) : ℂ) * ((q.2 : ℂ) ^ (m - n) * Hn n q.1)

noncomputable def K (a : ℂ) (v : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-a - 1) * Complex.Gamma (a + 1) * (Real.exp (-(2 * Real.pi * v)) : ℂ)

theorem integrableOn_Qn (m : ℕ) (a : ℂ) (ha : (m : ℝ) - 1 < a.re) (v : ℝ) (hv : 0 < v) (n : ℕ) (hn : n ≤ m) :
    IntegrableOn (Qn m a v n) {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2} := by
  have ha' : -1 < a.re := lt_of_le_of_lt (by have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith) ha
  have h := LanglandsTunnell.integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion a ha' ((1 : ℤ) - (n : ℤ)) n v hv
  refine h.congr_fun (fun q hq => ?_)
    ((isOpen_lt continuous_const continuous_fst).inter ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_const (continuous_fst.mul continuous_snd)))).measurableSet
  obtain ⟨-, hq2, -⟩ := hq
  have hw : (q.2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq2.ne'
  unfold Qn Hn gz
  dsimp only
  rw [← zpow_collapse' hw hn]
  ring

theorem inner_eq (m : ℕ) (a : ℂ) (ha : (m : ℝ) - 1 < a.re) (v : ℝ) (n : ℕ) (hn : n ≤ m) {w : ℝ} (hw : 0 < w) :
    ∫ σ in Ioi (v / w), Qn m a v n (σ, w) =
      (((-(2 * (Real.pi : ℂ)))⁻¹) ^ n * (-1) ^ n * ∏ k ∈ Finset.range n, (a - (k : ℂ))) *
        ∫ ρ in Ioi v, ((ρ - v : ℝ) : ℂ) ^ (a - (n : ℂ)) * (Real.exp (-(Real.pi * (w ^ 2 + ρ ^ 2 / w ^ 2))) : ℂ) := by
  have hw0 : (w : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw.ne'
  have hnm : (n : ℝ) ≤ m := by exact_mod_cast hn
  have han : ((n : ℕ) : ℝ) - 1 < a.re := by push_cast; linarith
  set c : ℂ := (-(2 * (Real.pi : ℂ)))⁻¹ with hc

  have hpt : ∀ σ : ℝ, Qn m a v n (σ, w) =
      ((w : ℂ) ^ ((1 : ℤ) - (m : ℤ)) * (w : ℂ) ^ (m - n) * (Real.exp (-(Real.pi * w ^ 2)) : ℂ) * c ^ n) *
        (((σ * w - v : ℝ) : ℂ) ^ a * iteratedDeriv n (fun s : ℝ => (Real.exp (-(Real.pi * s ^ 2)) : ℂ)) σ) := by
    intro σ
    have hB := LanglandsTunnell.exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv n σ
    have hsplit : (Real.exp (-(Real.pi * (σ ^ 2 + w ^ 2))) : ℂ) =
        (Real.exp (-(Real.pi * w ^ 2)) : ℂ) * (Real.exp (-(Real.pi * σ ^ 2)) : ℂ) := by
      rw [← ofReal_mul, ← Real.exp_add]; congr 1; congr 1; ring
    unfold Qn
    simp only []
    rw [hsplit]
    unfold Hn gz
    rw [← hc] at hB
    calc ((σ * w - v : ℝ) : ℂ) ^ a * (w : ℂ) ^ ((1 : ℤ) - (m : ℤ)) *
          ((Real.exp (-(Real.pi * w ^ 2)) : ℂ) * (Real.exp (-(Real.pi * σ ^ 2)) : ℂ)) *
          ((w : ℂ) ^ (m - n) * ∫ z : ℝ, ((σ : ℂ) - I * (z : ℂ)) ^ n * (Real.exp (-(Real.pi * z ^ 2)) : ℂ))
        = ((w : ℂ) ^ ((1 : ℤ) - (m : ℤ)) * (w : ℂ) ^ (m - n) * (Real.exp (-(Real.pi * w ^ 2)) : ℂ)) *
          (((σ * w - v : ℝ) : ℂ) ^ a * ((Real.exp (-(Real.pi * σ ^ 2)) : ℂ) *
            ∫ z : ℝ, ((σ : ℂ) - I * (z : ℂ)) ^ n * (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) := by ring
      _ = _ := by rw [hB]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun σ _ => hpt σ), integral_const_mul,
    LanglandsTunnell.integral_Ioi_cpow_mul_iteratedDeriv_exp_neg_pi_mul_sq_eq_prod_mul_integral_cpow_sub_mul_exp n a han w hw v,
    integral_subst (a - (n : ℂ)) v hw]
  simp only [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun ρ _ => ?_
  have hexp : (Real.exp (-(Real.pi * w ^ 2)) : ℂ) * (Real.exp (-(Real.pi * (ρ / w) ^ 2)) : ℂ) =
      (Real.exp (-(Real.pi * (w ^ 2 + ρ ^ 2 / w ^ 2))) : ℂ) := by
    rw [← ofReal_mul, ← Real.exp_add]; congr 1; congr 1; rw [div_pow]; ring
  have hz := zpow_collapse hw0 hn
  calc _ = ((w : ℂ) ^ ((1 : ℤ) - (m : ℤ)) * (w : ℂ) ^ (m - n) * (-(w : ℂ)) ^ n * (w : ℂ)⁻¹) *
          (c ^ n * (∏ k ∈ Finset.range n, (a - (k : ℂ))) * ((ρ - v : ℝ) : ℂ) ^ (a - (n : ℂ))) *
          ((Real.exp (-(Real.pi * w ^ 2)) : ℂ) * (Real.exp (-(Real.pi * (ρ / w) ^ 2)) : ℂ)) := by ring
    _ = _ := by rw [hz, hexp]; ring

end FiberAsm

namespace FiberAsm

theorem mono (m : ℕ) (a : ℂ) (ha : (m : ℝ) - 1 < a.re) (v : ℝ) (hv : 0 < v) (n : ℕ) (hn : n ≤ m) :
    ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, Qn m a v n q = K a v := by
  have hnm : (n : ℝ) ≤ m := by exact_mod_cast hn
  have han : -1 < (a - (n : ℂ)).re := by simp only [sub_re, natCast_re]; linarith
  have hk : ∀ k : ℕ, k < n → a - (k : ℂ) ≠ 0 := by
    intro k hk h0
    have h1 : (a - (k : ℂ)).re = 0 := by rw [h0]; simp
    simp only [sub_re, natCast_re] at h1
    have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    linarith
  have hint := integrableOn_Qn m a ha v hv n hn
  obtain ⟨-, hswap⟩ :=
    LanglandsTunnell.integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion v hv (Qn m a v n) hint
  rw [← hswap, setIntegral_congr_fun measurableSet_Ioi (fun w hw => inner_eq m a ha v n hn hw), integral_const_mul]

  have hsw := integral_integral_swap
    (f := fun (w : ℝ) (ρ : ℝ) => ((ρ - v : ℝ) : ℂ) ^ (a - (n : ℂ)) * (Real.exp (-(Real.pi * (w ^ 2 + ρ ^ 2 / w ^ 2))) : ℂ))
    (integrable_prod_cpow_sub_mul_exp_hyp (a - (n : ℂ)) han v hv)
  rw [hsw]

  have h3 : ∀ ρ ∈ Ioi v, (∫ w in Ioi (0 : ℝ), ((ρ - v : ℝ) : ℂ) ^ (a - (n : ℂ)) *
      (Real.exp (-(Real.pi * (w ^ 2 + ρ ^ 2 / w ^ 2))) : ℂ)) =
      ((ρ - v : ℝ) : ℂ) ^ (a - (n : ℂ)) * ((1 / 2 : ℂ) * (Real.exp (-(2 * Real.pi * ρ)) : ℂ)) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hv.trans hρ
    rw [integral_const_mul, integral_complex_ofReal,
      (LanglandsTunnell.integrableOn_and_integral_Ioi_exp_neg_pi_mul_sq_add_sq_div_sq_eq_half_exp ρ hρ0).2]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h3]

  have h4 : (∫ ρ in Ioi v, ((ρ - v : ℝ) : ℂ) ^ (a - (n : ℂ)) * ((1 / 2 : ℂ) * (Real.exp (-(2 * Real.pi * ρ)) : ℂ))) =
      (1 / 2 : ℂ) * ((Real.exp (-(2 * Real.pi * v)) : ℂ) *
        (((1 / (2 * Real.pi : ℝ) : ℂ)) ^ (a - (n : ℂ) + 1) * Complex.Gamma (a - (n : ℂ) + 1))) := by
    rw [← integral_Ioi_cpow_sub_mul_exp (a - (n : ℂ)) han v (2 * Real.pi) (by positivity), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ _ => ?_
    ring
  rw [h4]

  unfold K
  rw [← prod_mul_Gamma a n hk, ← const_collapse a n]
  push_cast
  ring

theorem main (m : ℕ) (a : ℂ) (ha : (m : ℝ) - 1 < a.re) (v : ℝ) (hv : 0 < v)
    (p : MvPolynomial (Fin 2) ℂ) (hp : p.IsHomogeneous m) :
    ∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
        (((σ * w - v : ℝ) : ℂ) ^ a) * ((w : ℂ) ^ ((1 : ℤ) - (m : ℤ))) *
          (Real.exp (-(Real.pi * (σ ^ 2 + w ^ 2))) : ℂ) *
          (∫ z : ℝ, MvPolynomial.eval ![(σ : ℂ) - Complex.I * (z : ℂ), (w : ℂ)] p * (Real.exp (-(Real.pi * z ^ 2)) : ℂ))
      = (1 / 2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-a - 1) * Complex.Gamma (a + 1) *
          (Real.exp (-(2 * Real.pi * v)) : ℂ) * MvPolynomial.eval ![(1 : ℂ), 1] p := by
  set P : ℝ × ℝ → ℂ := fun q => (((q.1 * q.2 - v : ℝ) : ℂ) ^ a) * ((q.2 : ℂ) ^ ((1 : ℤ) - (m : ℤ))) *
      (Real.exp (-(Real.pi * (q.1 ^ 2 + q.2 ^ 2))) : ℂ) *
      (∫ z : ℝ, MvPolynomial.eval ![(q.1 : ℂ) - Complex.I * (z : ℂ), (q.2 : ℂ)] p * (Real.exp (-(Real.pi * z ^ 2)) : ℂ))
    with hPdef
  have hP : P = fun q => ∑ d ∈ p.support, p.coeff d * Qn m a v (d 0) q := by
    funext q
    simp only [hPdef, Qn]
    rw [gaussAverage_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd' := isHomogeneous_fin_two hp hd
    rw [show d 1 = m - d 0 by omega]
    ring
  have hdeg : ∀ d ∈ p.support, d 0 ≤ m := fun d hd => by have := isHomogeneous_fin_two hp hd; omega
  have hPint : IntegrableOn P {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2} := by
    rw [hP]
    exact integrable_finset_sum _ fun d hd => (integrableOn_Qn m a ha v hv (d 0) (hdeg d hd)).const_mul _
  obtain ⟨h1, -⟩ :=
    LanglandsTunnell.integral_Ioi_integral_Ioi_div_eq_setIntegral_and_swap_of_integrableOn_hyperbolicRegion v hv P hPint
  have hL : (∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
        (((σ * w - v : ℝ) : ℂ) ^ a) * ((w : ℂ) ^ ((1 : ℤ) - (m : ℤ))) *
          (Real.exp (-(Real.pi * (σ ^ 2 + w ^ 2))) : ℂ) *
          (∫ z : ℝ, MvPolynomial.eval ![(σ : ℂ) - Complex.I * (z : ℂ), (w : ℂ)] p * (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) =
      ∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ), P (σ, w) := by simp only [hPdef]
  rw [hL, h1, hP]
  beta_reduce
  rw [integral_finset_sum _ fun d hd => (integrableOn_Qn m a ha v hv (d 0) (hdeg d hd)).const_mul _]
  have hsum : ∑ d ∈ p.support, ∫ q in {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}, p.coeff d * Qn m a v (d 0) q =
      ∑ d ∈ p.support, p.coeff d * K a v := by
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [integral_const_mul, mono m a ha v hv (d 0) (hdeg d hd)]
  rw [hsum, ← Finset.sum_mul, ← eval_one_one, K]
  ring

end FiberAsm

theorem solution
    (m : ℕ) (a : ℂ) (ha : (m : ℝ) - 1 < a.re) (v : ℝ) (hv : 0 < v)
    (p : MvPolynomial (Fin 2) ℂ) (hp : p.IsHomogeneous m) :
    ∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
        (((σ * w - v : ℝ) : ℂ) ^ a) * ((w : ℂ) ^ ((1 : ℤ) - (m : ℤ))) *
          (Real.exp (-(Real.pi * (σ ^ 2 + w ^ 2))) : ℂ) *
          (∫ z : ℝ, MvPolynomial.eval ![(σ : ℂ) - Complex.I * (z : ℂ), (w : ℂ)] p * (Real.exp (-(Real.pi * z ^ 2)) : ℂ))
      = (1 / 2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-a - 1) * Complex.Gamma (a + 1) *
          (Real.exp (-(2 * Real.pi * v)) : ℂ) * MvPolynomial.eval ![(1 : ℂ), 1] p :=
  FiberAsm.main m a ha v hv p hp

end S_LanglandsTunnell_setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous
end P2MW
export P2MW.S_LanglandsTunnell_setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous (solution)
