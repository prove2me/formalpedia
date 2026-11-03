-- Prove2me | solution 1 for Grothendieck.ErComplex_derivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T16:04:39.960055+00:00
-- url     : https://prove2.me/submissions/6fac9b77-744d-4e97-9503-75495be63916

import Mathlib
import Definitions.Def_Grothendieck_Series

set_option autoImplicit false

/-!
# The power series `E_r` on the closed unit disc: summability, continuity, circle decomposition

Auxiliary material shared by Lemma 3.2, Lemma 3.5 and Proposition 4.2 of
Briët–de Oliveira Filho–Vallentin, *Grothendieck inequalities for semidefinite programs with
rank constraint*, Theory of Computing 10(4), 2014, pp. 77--105.

Main results (all for `r ≥ 2` unless stated otherwise):

* `Cr_pos`, `ErCoeff_nonneg`, `ErCoeff_pos`;
* `summable_ErCoeff : Summable (fun k => ErCoeff r k)` — the coefficients of `E_r` are summable;
* `continuous_erCoeff_cos`, `continuous_erCoeff_sin` — the real and imaginary parts of the
  boundary values of `E_r` are continuous in the angle;
* `erComplex_circle` — the boundary value `E_r(e^{iθ})` as the series `Σ_k a_k e^{i(2k+1)θ}`,
  and its factorisation `E_r(e^{iθ}) = e^{iθ} Σ_k a_k e^{2ikθ}`;
* `continuous_erComplex_circle` and `cr_eq_min` — `c_r` is attained, i.e. `c_r` is the minimum of
  `θ ↦ ‖E_r(e^{iθ})‖` on `[0,2π]`.
-/

noncomputable section

open scoped BigOperators Real Topology
open Filter MeasureTheory Topology

namespace Grothendieck

/-! ### Positivity of the coefficients -/

/-- `C_r > 0` for `r ≥ 1`. -/
theorem Cr_pos {r : ℕ} (hr : 1 ≤ r) : 0 < Cr r := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h1 : 0 < Real.Gamma (((r : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Real.Gamma ((r : ℝ) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  have h3 : 0 < 2 / (r : ℝ) := by positivity
  unfold Cr
  have : 0 < (Real.Gamma (((r : ℝ) + 1) / 2) / Real.Gamma ((r : ℝ) / 2)) ^ 2 := by positivity
  exact mul_pos h3 this

theorem risingFact_half_pos (k : ℕ) : 0 < risingFact (1 / 2) k := by
  rw [risingFact]
  exact Finset.prod_pos fun i _ => by positivity

theorem risingFact_half_nonneg (k : ℕ) : 0 ≤ risingFact (1 / 2) k :=
  (risingFact_half_pos k).le

theorem risingFact_cc_pos {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    0 < risingFact ((r : ℝ) / 2 + 1) k := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  rw [risingFact]
  exact Finset.prod_pos fun i _ => by positivity

/-- `0 ≤ ErCoeff r k` for `r ≥ 1`. -/
theorem ErCoeff_nonneg {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : 0 ≤ ErCoeff r k := by
  unfold ErCoeff
  have h0 := Cr_pos hr
  have h1 := risingFact_half_nonneg k
  have h2 := (risingFact_cc_pos hr k).le
  have h3 : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have h4 : (0 : ℝ) ≤ (risingFact (1 / 2) k) ^ 2 := by positivity
  have h5 : (0 : ℝ) ≤ risingFact ((r : ℝ) / 2 + 1) k * (k.factorial : ℝ) := by positivity
  exact div_nonneg (mul_nonneg h0.le h4) h5

/-- `0 < ErCoeff r k` for `r ≥ 1`. -/
theorem ErCoeff_pos {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : 0 < ErCoeff r k := by
  unfold ErCoeff
  have h0 := Cr_pos hr
  have h1 := risingFact_half_pos k
  have h2 := risingFact_cc_pos hr k
  have h3 : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have h4 : (0 : ℝ) < (risingFact (1 / 2) k) ^ 2 := by positivity
  exact div_pos (mul_pos h0 h4) (mul_pos h2 h3)

/-! ### The coefficient bound `a_k ≤ 1/(k+1)²` (from the Vietoris leaf) -/

/-- `cc r = r/2 + 1`, the parameter `r/2+1` of the hypergeometric series. -/
def cc (r : ℕ) : ℝ := (r : ℝ)/2 + 1

def ak (r k : ℕ) : ℝ :=
  risingFact (1/2) k * risingFact (1/2) k / (risingFact (cc r) k * (k.factorial : ℝ))

theorem ak_eq (r k : ℕ) :
    ak r k = risingFact (1/2) k * risingFact (1/2) k
      / (risingFact (cc r) k * (k.factorial : ℝ)) := rfl

theorem risingFact_succ' (a : ℝ) (k : ℕ) :
    risingFact a (k+1) = risingFact a k * (a + (k:ℝ)) := by
  rw [risingFact, risingFact, Finset.prod_range_succ]

theorem risingFact_pos_one_half (k : ℕ) : 0 < risingFact (1/2) k := by
  rw [risingFact]
  exact Finset.prod_pos fun i _ => by positivity

theorem cc_pos (r : ℕ) : 0 < cc r := by simp only [cc]; positivity

theorem risingFact_pos_cc (r k : ℕ) : 0 < risingFact (cc r) k := by
  rw [risingFact]
  exact Finset.prod_pos fun i _ => by
    have h : (0:ℝ) < cc r := cc_pos r
    positivity

theorem ak_nonneg (r k : ℕ) : 0 ≤ ak r k := by
  rw [ak_eq]
  exact div_nonneg (mul_nonneg (risingFact_pos_one_half k).le (risingFact_pos_one_half k).le)
    (mul_nonneg (risingFact_pos_cc r k).le (by positivity))

theorem ak_pos (r k : ℕ) : 0 < ak r k := by
  rw [ak_eq]
  exact div_pos (mul_pos (risingFact_pos_one_half k) (risingFact_pos_one_half k))
    (mul_pos (risingFact_pos_cc r k) (by positivity))

theorem ak_ratio (r k : ℕ) :
    ak r (k+1) = ak r k * ((1/2 + (k:ℝ))^2 / ((cc r + (k:ℝ)) * ((k:ℝ)+1))) := by
  have h1 : risingFact (1/2) (k+1) = risingFact (1/2) k * (1/2 + (k:ℝ)) := risingFact_succ' (1/2) k
  have h2 : risingFact (cc r) (k+1) = risingFact (cc r) k * (cc r + (k:ℝ)) :=
    risingFact_succ' (cc r) k
  have h3 : (((k+1).factorial : ℕ) : ℝ) = (k.factorial : ℝ) * ((k:ℝ)+1) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hA : (0:ℝ) < risingFact (1/2) k := risingFact_pos_one_half k
  have hB : (0:ℝ) < risingFact (cc r) k := risingFact_pos_cc r k
  have hC : (0:ℝ) < (k.factorial : ℝ) := by positivity
  have hD : (0:ℝ) < cc r + (k:ℝ) := by have := cc_pos r; positivity
  have hE : (0:ℝ) < (k:ℝ) + 1 := by positivity
  rw [ak_eq, ak_eq, h1, h2, h3]
  field_simp

theorem ak_step (r k : ℕ) (hr : 2 ≤ r) :
    ak r (k+1) * ((k:ℝ)+2)^2 ≤ ak r k * ((k:ℝ)+1)^2 := by
  have h2r : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hcc : (2:ℝ) ≤ cc r := by simp only [cc]; linarith
  have hA : (0:ℝ) < ak r k := ak_pos r k
  have hD : (0:ℝ) < cc r + (k:ℝ) := by have := cc_pos r; positivity
  have hE : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hF : (0:ℝ) < (k:ℝ) + 2 := by positivity
  have hkey : (1/2 + (k:ℝ))^2 * ((k:ℝ)+2) ≤ ((k:ℝ)+1)^3 := by nlinarith
  have hfrac : (1/2 + (k:ℝ))^2 / ((cc r + (k:ℝ)) * ((k:ℝ)+1)) * ((k:ℝ)+2)^2
      ≤ ((k:ℝ)+1)^2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h1 : (2:ℝ) + (k:ℝ) ≤ cc r + (k:ℝ) := by linarith
    have h2 : (1/2 + (k:ℝ))^2 * ((k:ℝ)+2)^2 ≤ ((k:ℝ)+1)^3 * ((k:ℝ)+2) := by
      have hm := mul_le_mul_of_nonneg_right hkey hF.le
      linarith [hm]
    have h3 : ((k:ℝ)+1)^3 * ((k:ℝ)+2) ≤ ((k:ℝ)+1)^3 * (cc r + (k:ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith : (k:ℝ)+2 ≤ cc r + (k:ℝ)) (by positivity)
    nlinarith [h2, h3]
  rw [ak_ratio]
  calc ak r k * ((1/2 + (k:ℝ))^2 / ((cc r + (k:ℝ)) * ((k:ℝ)+1))) * ((k:ℝ)+2)^2
      = ak r k * ((1/2 + (k:ℝ))^2 / ((cc r + (k:ℝ)) * ((k:ℝ)+1)) * ((k:ℝ)+2)^2) := by ring
    _ ≤ ak r k * ((k:ℝ)+1)^2 := by
        exact mul_le_mul_of_nonneg_left hfrac hA.le

theorem ak_mul_le (r k : ℕ) (hr : 2 ≤ r) : ak r k * ((k:ℝ)+1)^2 ≤ 1 := by
  induction k with
  | zero =>
    rw [ak_eq]
    norm_num [risingFact]
  | succ k ih =>
    have h1 : ak r (k+1) * (((k:ℝ)+1)+1)^2 ≤ ak r k * ((k:ℝ)+1)^2 := by
      have h := ak_step r k hr
      rwa [show ((k:ℝ)+1)+1 = (k:ℝ)+2 by ring]
    have h1' : ak r (k+1) * ((↑(k+1) : ℝ)+1)^2 ≤ ak r k * ((↑k : ℝ)+1)^2 := by
      push_cast
      exact h1
    have h2 : ak r k * ((↑k : ℝ)+1)^2 ≤ 1 := ih
    linarith

theorem ak_le (r k : ℕ) (hr : 2 ≤ r) : ak r k ≤ 1/((k:ℝ)+1)^2 := by
  have h := ak_mul_le r k hr
  have hpos : (0:ℝ) < ((k:ℝ)+1)^2 := by positivity
  rw [le_div_iff₀ hpos]
  exact h

theorem summable_inv_sq : Summable (fun k : ℕ => 1/((k:ℝ)+1)^2) := by
  have h : Summable (fun n : ℕ => 1/((n:ℝ))^2) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num : 1 < 2)
  have h' : Summable (fun n : ℕ => 1/(((n+1 : ℕ) : ℝ))^2) :=
    (summable_nat_add_iff (f := fun n : ℕ => 1/((n:ℝ))^2) 1).mpr h
  simpa [Nat.cast_add, Nat.cast_one] using h'

/-! ### Summability of the coefficients of `E_r` -/

theorem ErCoeff_eq_Cr_mul_ak (r k : ℕ) : ErCoeff r k = Cr r * ak r k := by
  unfold ErCoeff ak cc
  rw [pow_two, mul_div_assoc]

/-- For `r ≥ 2` the coefficients of the series `E_r` are summable. -/
theorem summable_ErCoeff {r : ℕ} (hr : 2 ≤ r) : Summable (fun k : ℕ => ErCoeff r k) := by
  have h : Summable (fun k : ℕ => ak r k) :=
    Summable.of_nonneg_of_le (fun k => ak_nonneg r k) (fun k => ak_le r k hr) summable_inv_sq
  have h2 : Summable (fun k : ℕ => Cr r * ak r k) := h.mul_left (Cr r)
  simpa [ErCoeff_eq_Cr_mul_ak] using h2

/-! ### The boundary series of `E_r`: cosine, sine and circle parametrisations -/

/-- The point `e^{ix}` of the unit circle. -/
def circlePt (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

theorem circlePt_norm (x : ℝ) : ‖circlePt x‖ = 1 := by
  rw [circlePt]
  exact Complex.norm_exp_ofReal_mul_I _

theorem circlePt_re (x : ℝ) : (circlePt x).re = Real.cos x := by
  rw [circlePt, Complex.exp_ofReal_mul_I]
  simp [Complex.cos_ofReal_re]

theorem circlePt_im (x : ℝ) : (circlePt x).im = Real.sin x := by
  rw [circlePt, Complex.exp_ofReal_mul_I]
  simp [Complex.sin_ofReal_re]

theorem circlePt_nat_mul (n : ℕ) (θ : ℝ) : circlePt ((n : ℝ) * θ) = circlePt θ ^ n := by
  rw [circlePt, circlePt, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem circlePt_add (x y : ℝ) : circlePt (x + y) = circlePt x * circlePt y := by
  rw [circlePt, circlePt, circlePt, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The boundary cosine series `R_r(θ) = Σ_k a_k cos(kθ)`, the real part of the hypergeometric
series on the unit circle. -/
def ErCos (r : ℕ) (θ : ℝ) : ℝ := ∑' k : ℕ, ErCoeff r k * Real.cos ((k : ℝ) * θ)

/-- The boundary sine series `I_r(θ) = Σ_k a_k sin(kθ)`. -/
def ErSin (r : ℕ) (θ : ℝ) : ℝ := ∑' k : ℕ, ErCoeff r k * Real.sin ((k : ℝ) * θ)

/-- The boundary value `F_r(θ) = Σ_k a_k e^{ikθ}` of the hypergeometric series. -/
def ErCirc (r : ℕ) (θ : ℝ) : ℂ := ∑' k : ℕ, (ErCoeff r k : ℂ) * circlePt ((k : ℝ) * θ)

theorem ErCoeff_nonneg' {r : ℕ} (hr : 2 ≤ r) (k : ℕ) : 0 ≤ ErCoeff r k :=
  ErCoeff_nonneg (by linarith) k

theorem summable_erCoeff_circlePt (r : ℕ) (hr : 2 ≤ r) (φ : ℕ → ℝ) :
    Summable fun k : ℕ => (ErCoeff r k : ℂ) * circlePt (φ k) := by
  refine Summable.of_norm_bounded (summable_ErCoeff hr) (fun k => ?_)
  rw [norm_mul, circlePt_norm, mul_one, Complex.norm_def, Complex.normSq_ofReal,
    Real.sqrt_mul_self (ErCoeff_nonneg' hr k)]

theorem summable_erCos (r : ℕ) (hr : 2 ≤ r) (θ : ℝ) :
    Summable fun k : ℕ => ErCoeff r k * Real.cos ((k : ℝ) * θ) := by
  refine Summable.of_norm_bounded (summable_ErCoeff hr) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ErCoeff_nonneg' hr k)]
  exact mul_le_of_le_one_right (ErCoeff_nonneg' hr k) (Real.abs_cos_le_one _)

theorem summable_erSin (r : ℕ) (hr : 2 ≤ r) (θ : ℝ) :
    Summable fun k : ℕ => ErCoeff r k * Real.sin ((k : ℝ) * θ) := by
  refine Summable.of_norm_bounded (summable_ErCoeff hr) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ErCoeff_nonneg' hr k)]
  exact mul_le_of_le_one_right (ErCoeff_nonneg' hr k) (Real.abs_sin_le_one _)

theorem ErCirc_re (r : ℕ) (hr : 2 ≤ r) (θ : ℝ) : (ErCirc r θ).re = ErCos r θ := by
  unfold ErCirc ErCos
  rw [Complex.re_tsum (summable_erCoeff_circlePt r hr (fun k => (k : ℝ) * θ))]
  exact tsum_congr fun k => by
    rw [Complex.mul_re, circlePt_re, circlePt_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

theorem ErCirc_im (r : ℕ) (hr : 2 ≤ r) (θ : ℝ) : (ErCirc r θ).im = ErSin r θ := by
  unfold ErCirc ErSin
  rw [Complex.im_tsum (summable_erCoeff_circlePt r hr (fun k => (k : ℝ) * θ))]
  exact tsum_congr fun k => by
    rw [Complex.mul_im, circlePt_re, circlePt_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

theorem ErCirc_eq_re_add_im (r : ℕ) (hr : 2 ≤ r) (θ : ℝ) :
    ErCirc r θ = (ErCos r θ : ℂ) + (ErSin r θ : ℂ) * Complex.I := by
  refine Complex.ext ?_ ?_
  · rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, ErCirc_re r hr θ]
    ring
  · rw [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, ErCirc_im r hr θ]
    ring

theorem normSq_ErCirc (r : ℕ) (hr : 2 ≤ r) (θ : ℝ) :
    Complex.normSq (ErCirc r θ) = ErCos r θ ^ 2 + ErSin r θ ^ 2 := by
  rw [ErCirc_eq_re_add_im r hr θ, Complex.normSq_apply]
  simp
  ring

/-! ### Continuity of the boundary series -/

theorem continuous_ErCos (r : ℕ) (hr : 2 ≤ r) : Continuous (ErCos r) := by
  unfold ErCos
  refine continuous_tsum (fun k => ?_) (summable_ErCoeff hr) (fun k x => ?_)
  · fun_prop
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ErCoeff_nonneg' hr k)]
    exact mul_le_of_le_one_right (ErCoeff_nonneg' hr k) (Real.abs_cos_le_one _)

theorem continuous_ErSin (r : ℕ) (hr : 2 ≤ r) : Continuous (ErSin r) := by
  unfold ErSin
  refine continuous_tsum (fun k => ?_) (summable_ErCoeff hr) (fun k x => ?_)
  · fun_prop
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ErCoeff_nonneg' hr k)]
    exact mul_le_of_le_one_right (ErCoeff_nonneg' hr k) (Real.abs_sin_le_one _)

theorem continuous_ErCirc (r : ℕ) (hr : 2 ≤ r) : Continuous (ErCirc r) := by
  have h : ErCirc r = fun θ => (ErCos r θ : ℂ) + (ErSin r θ : ℂ) * Complex.I :=
    funext fun θ => ErCirc_eq_re_add_im r hr θ
  rw [h]
  exact (RCLike.continuous_ofReal.comp (continuous_ErCos r hr)).add
    ((RCLike.continuous_ofReal.comp (continuous_ErSin r hr)).mul continuous_const)

/-! ### The circle parametrisation of `E_r` -/

theorem ErComplex_exp_tsum (r : ℕ) (θ : ℝ) :
    ErComplex r (Complex.exp (θ * Complex.I)) =
      ∑' k : ℕ, (ErCoeff r k : ℂ) * circlePt (((2 * k + 1 : ℕ) : ℝ) * θ) := by
  unfold ErComplex
  exact tsum_congr fun k => by rw [circlePt_nat_mul]; rfl

theorem summable_erComplex_circle (r : ℕ) (hr : 2 ≤ r) (θ : ℝ) :
    Summable fun k : ℕ => (ErCoeff r k : ℂ) * circlePt (((2 * k + 1 : ℕ) : ℝ) * θ) :=
  summable_erCoeff_circlePt r hr (fun k => ((2 * k + 1 : ℕ) : ℝ) * θ)

theorem circlePt_two_mul_add_one (k : ℕ) (θ : ℝ) :
    circlePt (((2 * k + 1 : ℕ) : ℝ) * θ) =
      Complex.exp (θ * Complex.I) * circlePt ((k : ℝ) * (2 * θ)) := by
  rw [circlePt, circlePt, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The circle parametrisation**: `E_r(e^{iθ}) = e^{iθ} F_r(2θ)`. -/
theorem ErComplex_exp_eq (r : ℕ) (hr : 2 ≤ r) (θ : ℝ) :
    ErComplex r (Complex.exp (θ * Complex.I)) =
      Complex.exp (θ * Complex.I) * ErCirc r (2 * θ) := by
  rw [ErComplex_exp_tsum]
  have hterm : ∀ k : ℕ, (ErCoeff r k : ℂ) * circlePt (((2 * k + 1 : ℕ) : ℝ) * θ)
      = Complex.exp (θ * Complex.I) * ((ErCoeff r k : ℂ) * circlePt ((k : ℝ) * (2 * θ))) := by
    intro k
    rw [circlePt_two_mul_add_one]
    ring
  simp only [hterm]
  rw [tsum_mul_left]
  rfl

/-- `‖E_r(e^{iθ})‖ = ‖F_r(2θ)‖`. -/
theorem norm_ErComplex_exp (r : ℕ) (hr : 2 ≤ r) (θ : ℝ) :
    ‖ErComplex r (Complex.exp (θ * Complex.I))‖ = ‖ErCirc r (2 * θ)‖ := by
  rw [ErComplex_exp_eq r hr θ, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem continuous_norm_ErComplex_circle (r : ℕ) (hr : 2 ≤ r) :
    Continuous fun θ : ℝ => ‖ErComplex r (Complex.exp (θ * Complex.I))‖ := by
  have h : Continuous fun θ : ℝ => ‖ErCirc r (2 * θ)‖ :=
    ((continuous_ErCirc r hr).comp (by fun_prop)).norm
  simpa only [norm_ErComplex_exp r hr] using h

/-- `c_r` is attained: it is the minimum of `‖E_r(e^{iθ})‖` over `θ ∈ [0, 2π]`. -/
theorem cr_eq_min (r : ℕ) (hr : 2 ≤ r) :
    ∃ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      cr r = ‖ErComplex r (Complex.exp (θ * Complex.I))‖ ∧
        ∀ θ' ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
          cr r ≤ ‖ErComplex r (Complex.exp (θ' * Complex.I))‖ := by
  have hcont : ContinuousOn (fun θ : ℝ => ‖ErComplex r (Complex.exp (θ * Complex.I))‖)
      (Set.Icc (0 : ℝ) (2 * Real.pi)) := (continuous_norm_ErComplex_circle r hr).continuousOn
  obtain ⟨θ₀, hθ₀, hmin⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * Real.pi)).exists_isMinOn
    ⟨0, Set.left_mem_Icc.mpr (by positivity)⟩ hcont
  have hS : {y : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        y = ‖ErComplex r (Complex.exp (Complex.I * t))‖}
      = {y : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        y = ‖ErComplex r (Complex.exp (t * Complex.I))‖} := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, by rw [mul_comm Complex.I (t : ℂ)]⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, by rw [mul_comm (t : ℂ) Complex.I]⟩
  have hbdd : BddBelow {y : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      y = ‖ErComplex r (Complex.exp (t * Complex.I))‖} :=
    ⟨_, fun y hy => by rcases hy with ⟨t, ht, rfl⟩; exact hmin ht⟩
  have hmem : ‖ErComplex r (Complex.exp (θ₀ * Complex.I))‖ ∈
      {y : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        y = ‖ErComplex r (Complex.exp (t * Complex.I))‖} := ⟨θ₀, hθ₀, rfl⟩
  have hcr : cr r = ‖ErComplex r (Complex.exp (θ₀ * Complex.I))‖ := by
    simp only [cr, hS]
    exact le_antisymm (csInf_le hbdd hmem)
      (le_csInf ⟨_, hmem⟩ fun y hy => by rcases hy with ⟨t, ht, rfl⟩; exact hmin ht)
  exact ⟨θ₀, hθ₀, hcr, fun θ' hθ' => hcr ▸ hmin hθ'⟩

/-! ### Periodicity and the reflection about `π` -/

theorem circlePt_two_pi : circlePt (2 * Real.pi) = 1 := by
  rw [circlePt, Complex.exp_ofReal_mul_I]
  simp

theorem circlePt_add_two_pi_nat (k : ℕ) (θ : ℝ) :
    circlePt ((k : ℝ) * (θ + 2 * Real.pi)) = circlePt ((k : ℝ) * θ) := by
  rw [show (k : ℝ) * (θ + 2 * Real.pi) = (k : ℝ) * θ + (k : ℝ) * (2 * Real.pi) by ring,
    circlePt_add, circlePt_nat_mul, circlePt_nat_mul k (2 * Real.pi), circlePt_two_pi, one_pow,
    mul_one]

theorem ErCirc_add_two_pi (r : ℕ) (hr : 2 ≤ r) (θ : ℝ) :
    ErCirc r (θ + 2 * Real.pi) = ErCirc r θ := by
  unfold ErCirc
  exact tsum_congr fun k => by rw [circlePt_add_two_pi_nat]

theorem ErCos_add_two_pi (r : ℕ) (θ : ℝ) : ErCos r (θ + 2 * Real.pi) = ErCos r θ := by
  unfold ErCos
  refine tsum_congr fun k => ?_
  rw [show (k : ℝ) * (θ + 2 * Real.pi) = (k : ℝ) * θ + (k : ℝ) * (2 * Real.pi) by ring,
    Real.cos_add_nat_mul_two_pi]

theorem ErSin_add_two_pi (r : ℕ) (θ : ℝ) : ErSin r (θ + 2 * Real.pi) = ErSin r θ := by
  unfold ErSin
  refine tsum_congr fun k => ?_
  rw [show (k : ℝ) * (θ + 2 * Real.pi) = (k : ℝ) * θ + (k : ℝ) * (2 * Real.pi) by ring,
    Real.sin_add_nat_mul_two_pi]

theorem ErCos_zero (r : ℕ) : ErCos r 0 = ∑' k : ℕ, ErCoeff r k := by
  unfold ErCos
  simp

theorem ErSin_zero (r : ℕ) : ErSin r 0 = 0 := by
  unfold ErSin
  simp

theorem ErSin_pi (r : ℕ) : ErSin r Real.pi = 0 := by
  unfold ErSin
  simp [Real.sin_nat_mul_pi]

/-- `R_r(π + x) = R_r(π - x)`: the cosine series is symmetric about `π`. -/
theorem ErCos_pi_add_eq_pi_sub (r : ℕ) (x : ℝ) :
    ErCos r (Real.pi + x) = ErCos r (Real.pi - x) := by
  unfold ErCos
  refine tsum_congr fun k => ?_
  have h1 : Real.cos ((k : ℝ) * (Real.pi + x)) = (-1) ^ k * Real.cos ((k : ℝ) * x) := by
    rw [show (k : ℝ) * (Real.pi + x) = (k : ℝ) * x + (k : ℝ) * Real.pi by ring,
      Real.cos_add_nat_mul_pi]
  have h2 : Real.cos ((k : ℝ) * (Real.pi - x)) = (-1) ^ k * Real.cos ((k : ℝ) * x) := by
    rw [show (k : ℝ) * (Real.pi - x) = (k : ℝ) * Real.pi - (k : ℝ) * x by ring,
      Real.cos_nat_mul_pi_sub]
  rw [h1, h2]

/-- `I_r(π + x) = - I_r(π - x)`: the sine series is antisymmetric about `π`. -/
theorem ErSin_pi_add_eq_neg_pi_sub (r : ℕ) (hr : 2 ≤ r) (x : ℝ) :
    ErSin r (Real.pi + x) = -ErSin r (Real.pi - x) := by
  unfold ErSin
  rw [← tsum_neg]
  refine tsum_congr fun k => ?_
  have h1 : Real.sin ((k : ℝ) * (Real.pi + x)) = (-1) ^ k * Real.sin ((k : ℝ) * x) := by
    rw [show (k : ℝ) * (Real.pi + x) = (k : ℝ) * x + (k : ℝ) * Real.pi by ring,
      Real.sin_add_nat_mul_pi]
  have h2 : Real.sin ((k : ℝ) * (Real.pi - x)) = -((-1) ^ k * Real.sin ((k : ℝ) * x)) := by
    rw [show (k : ℝ) * (Real.pi - x) = -((k : ℝ) * x - (k : ℝ) * Real.pi) by ring,
      Real.sin_neg, Real.sin_sub_nat_mul_pi]
  rw [h1, h2]
  ring

/-! ### The modulus of the boundary value -/

theorem norm_sq_ErCirc (r : ℕ) (hr : 2 ≤ r) (θ : ℝ) :
    ‖ErCirc r θ‖ ^ 2 = ErCos r θ ^ 2 + ErSin r θ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, normSq_ErCirc r hr θ]

/-- The real part is bounded above by the modulus. -/
theorem ErCos_le_norm_ErCirc (r : ℕ) (hr : 2 ≤ r) (θ : ℝ) :
    ErCos r θ ≤ ‖ErCirc r θ‖ := by
  have h2 := norm_sq_ErCirc r hr θ
  have h3 : (0 : ℝ) ≤ ErSin r θ ^ 2 := sq_nonneg _
  have h4 : (0 : ℝ) ≤ ‖ErCirc r θ‖ := norm_nonneg _
  nlinarith

/-- `i = e^{iπ/2}` as a point of the unit circle. -/
theorem I_eq_circlePt : Complex.I = circlePt (Real.pi / 2) := by
  refine Complex.ext ?_ ?_
  · rw [Complex.I_re, circlePt_re, Real.cos_pi_div_two]
  · rw [Complex.I_im, circlePt_im, Real.sin_pi_div_two]

theorem norm_ErComplex_circlePt (r : ℕ) (hr : 2 ≤ r) (x : ℝ) :
    ‖ErComplex r (circlePt x)‖ = ‖ErCirc r (2 * x)‖ := by
  simpa [circlePt] using norm_ErComplex_exp r hr x

/-- `R_r(π) ≤ R_r(0)`: the terms with `cos(kπ) = -1` are dominated by those with `cos 0 = 1`. -/
theorem ErCos_pi_le_zero (r : ℕ) (hr : 2 ≤ r) : ErCos r Real.pi ≤ ErCos r 0 := by
  rw [ErCos_zero]
  unfold ErCos
  refine (summable_erCos r hr Real.pi).tsum_le_tsum (fun k => ?_) (summable_ErCoeff hr)
  simpa using mul_le_mul_of_nonneg_left (Real.cos_le_one ((k : ℝ) * Real.pi))
    (ErCoeff_nonneg' hr k)

/-- `R_r` is bounded below by `R_r(π)` on the whole of `[0, 2π]`, as a consequence of
`R_r(π + s) = R_r(π - s)`, `R_r(0) ≥ R_r(π)` and the monotonicity hypothesis on `(0, π)`. -/
theorem ErCos_pi_le_norm_ErCirc_of_mono (r : ℕ) (hr : 2 ≤ r)
    (hmono : ∀ x : ℝ, 0 < x → x < Real.pi → ErCos r Real.pi ≤ ErCos r x)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 2 * Real.pi) :
    ErCos r Real.pi ≤ ‖ErCirc r θ‖ := by
  rcases lt_or_ge θ Real.pi with h | h
  · rcases eq_or_lt_of_le hθ0 with h0 | h0
    · rw [← h0]
      exact le_trans (ErCos_pi_le_zero r hr) (ErCos_le_norm_ErCirc r hr 0)
    · exact le_trans (hmono θ h0 h) (ErCos_le_norm_ErCirc r hr θ)
  · have hs : θ = Real.pi + (θ - Real.pi) := by ring
    have hs0 : 0 ≤ θ - Real.pi := by linarith
    have hs1 : θ - Real.pi ≤ Real.pi := by linarith
    have hstep : ErCos r Real.pi ≤ ErCos r (Real.pi - (θ - Real.pi)) := by
      rcases eq_or_lt_of_le hs0 with h0 | h0
      · rw [show Real.pi - (θ - Real.pi) = Real.pi by rw [← h0]; ring]
      rcases eq_or_lt_of_le hs1 with h1 | h1
      · rw [show Real.pi - (θ - Real.pi) = 0 by rw [h1]; ring]
        exact ErCos_pi_le_zero r hr
      · exact hmono _ (by linarith) (by linarith)
    have hgoal : ‖ErCirc r θ‖ = ‖ErCirc r (Real.pi + (θ - Real.pi))‖ := by
      rw [show Real.pi + (θ - Real.pi) = θ by ring]
    refine le_trans hstep ?_
    rw [← ErCos_pi_add_eq_pi_sub r (θ - Real.pi), hgoal]
    exact ErCos_le_norm_ErCirc r hr (Real.pi + (θ - Real.pi))

/-- The same bound on `[0, 4π]`, using `2π`-periodicity. -/
theorem ErCos_pi_le_norm_ErCirc_of_mem (r : ℕ) (hr : 2 ≤ r)
    (hmono : ∀ x : ℝ, 0 < x → x < Real.pi → ErCos r Real.pi ≤ ErCos r x)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 4 * Real.pi) :
    ErCos r Real.pi ≤ ‖ErCirc r θ‖ := by
  rcases le_or_gt θ (2 * Real.pi) with h | h
  · exact ErCos_pi_le_norm_ErCirc_of_mono r hr hmono θ hθ0 h
  · have h2 : θ = (θ - 2 * Real.pi) + 2 * Real.pi := by ring
    rw [h2, ErCirc_add_two_pi r hr]
    exact ErCos_pi_le_norm_ErCirc_of_mono r hr hmono (θ - 2 * Real.pi) (by linarith)
      (by linarith)

/-- **Reduction of Lemma 3.5 to the monotonicity of `R_r` on `(0, π)`.**

If `R_r(π) ≤ R_r(x)` for `0 < x < π` and `R_r(π) ≥ 0`, then `c_r = |E_r(i)|`.  The analytic input
`R_r' < 0` on `(0, π)` (obtained in the paper from the moment representation (3.9) and the
differentiated Poisson kernel) is the only remaining ingredient. -/
theorem cr_eq_norm_I_of_mono (r : ℕ) (hr : 2 ≤ r)
    (hmono : ∀ x : ℝ, 0 < x → x < Real.pi → ErCos r Real.pi ≤ ErCos r x)
    (hpos : 0 ≤ ErCos r Real.pi) :
    cr r = ‖ErComplex r Complex.I‖ := by
  have hmod : ‖ErCirc r Real.pi‖ = ErCos r Real.pi := by
    have h4 : ‖ErCirc r Real.pi‖ ^ 2 = ErCos r Real.pi ^ 2 := by
      rw [norm_sq_ErCirc r hr, ErSin_pi r]
      ring
    nlinarith [norm_nonneg (ErCirc r Real.pi)]
  have hI : ‖ErComplex r Complex.I‖ = ErCos r Real.pi := by
    rw [I_eq_circlePt, norm_ErComplex_circlePt r hr (Real.pi / 2),
      show 2 * (Real.pi / 2) = Real.pi by ring, hmod]
  obtain ⟨θ₀, hθ₀, hcr, hmin⟩ := cr_eq_min r hr
  refine le_antisymm ?_ ?_
  · rw [hI]
    have h := hmin (Real.pi / 2) ⟨by positivity, by linarith [Real.pi_pos]⟩
    rwa [norm_ErComplex_exp r hr (Real.pi / 2), show 2 * (Real.pi / 2) = Real.pi by ring,
      hmod] at h
  · rw [hcr, norm_ErComplex_exp r hr θ₀, hI]
    exact ErCos_pi_le_norm_ErCirc_of_mem r hr hmono (2 * θ₀)
      (mul_nonneg (by norm_num) hθ₀.1) (by linarith [hθ₀.2])

/-! ### Analyticity of `E_r` inside the unit disc -/

theorem ErCoeff_le_Cr {r : ℕ} (hr : 2 ≤ r) (k : ℕ) : ErCoeff r k ≤ Cr r := by
  rw [ErCoeff_eq_Cr_mul_ak]
  have h : ak r k ≤ 1 := by
    have h2 := ak_mul_le r k hr
    have hk : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    nlinarith [ak_nonneg r k]
  have hCr := Cr_pos (by linarith : 1 ≤ r)
  nlinarith

/-- The coefficient series of `E_r` converges at every point of the open unit disc. -/
theorem summable_ErCoeff_mul_pow (r : ℕ) (hr : 2 ≤ r) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun k : ℕ => (ErCoeff r k : ℂ) * z ^ (2 * k + 1) := by
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith
  have hgeo : Summable fun k : ℕ => ‖z‖ ^ (2 * k + 1) := by
    have h1 : Summable fun k : ℕ => (‖z‖ ^ 2) ^ k :=
      summable_geometric_of_lt_one (by positivity) hz2
    have h2 : Summable fun k : ℕ => ‖z‖ * (‖z‖ ^ 2) ^ k := h1.mul_left ‖z‖
    refine h2.congr fun k => ?_
    have h3 : ‖z‖ ^ (2 * k + 1) = ‖z‖ * (‖z‖ ^ 2) ^ k := by
      rw [pow_add, pow_mul, pow_one]
      ring
    exact h3.symm
  refine Summable.of_norm_bounded (g := fun k => Cr r * ‖z‖ ^ (2 * k + 1))
    (hgeo.mul_left (Cr r)) (fun k => ?_)
  rw [norm_mul, norm_pow,
    show ‖((ErCoeff r k : ℝ) : ℂ)‖ = ErCoeff r k from by
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (ErCoeff_nonneg' hr k)]]
  exact mul_le_mul_of_nonneg_right (ErCoeff_le_Cr hr k) (by positivity)

set_option maxHeartbeats 2000000 in
/-- **`E_r` is complex differentiable inside the unit disc**, with derivative
`Σ_k (2k+1) a_k z^{2k}`. -/
theorem hasDerivAt_ErComplex (r : ℕ) (hr : 2 ≤ r) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (ErComplex r)
      (∑' k : ℕ, (ErCoeff r k : ℂ) * (((2 * k + 1 : ℕ) : ℂ) * z ^ (2 * k))) z := by
  obtain ⟨ρ, hzρ, hρ1⟩ : ∃ ρ : ℝ, ‖z‖ < ρ ∧ ρ < 1 :=
    ⟨(‖z‖ + 1) / 2, by linarith, by linarith⟩
  have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg z) hzρ
  have hρ2 : ρ ^ 2 < 1 := by nlinarith
  have hr2 : ‖ρ ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hρ2
  have hu : Summable fun k : ℕ => Cr r * (((2 * (k : ℝ) + 1)) * ρ ^ (2 * k)) := by
    have hA : Summable fun k : ℕ => (k : ℝ) * (ρ ^ 2) ^ k := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr2
    have hB : Summable fun k : ℕ => (ρ ^ 2) ^ k :=
      summable_geometric_of_lt_one (by positivity) hρ2
    have hsum : Summable fun k : ℕ => (2 * (k : ℝ) + 1) * (ρ ^ 2) ^ k := by
      have h := (hA.mul_left 2).add hB
      refine h.congr fun k => ?_
      ring
    have hC := hsum.mul_left (Cr r)
    refine hC.congr fun k => ?_
    rw [pow_mul]
  have hzρ' : z ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball.mpr (by simpa using hzρ)
  have hterm : ∀ n : ℕ, ∀ y ∈ Metric.ball (0 : ℂ) ρ,
      HasDerivAt (fun y => (ErCoeff r n : ℂ) * y ^ (2 * n + 1))
        ((ErCoeff r n : ℂ) * (((2 * n + 1 : ℕ) : ℂ) * y ^ (2 * n + 1 - 1))) y := by
    intro n y _
    have h := (hasDerivAt_pow (2 * n + 1) y).const_mul ((ErCoeff r n : ℂ))
    simpa using h
  have hbound : ∀ n : ℕ, ∀ y ∈ Metric.ball (0 : ℂ) ρ,
      ‖(ErCoeff r n : ℂ) * (((2 * n + 1 : ℕ) : ℂ) * y ^ (2 * n + 1 - 1))‖
        ≤ Cr r * ((2 * (n : ℝ) + 1) * ρ ^ (2 * n)) := by
    intro n y hy
    have hyρ : ‖y‖ ≤ ρ := le_of_lt (by simpa using Metric.mem_ball.mp hy)
    have h1 : ‖((ErCoeff r n : ℝ) : ℂ)‖ = ErCoeff r n := by
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (ErCoeff_nonneg' hr n)]
    rw [norm_mul, h1, norm_mul, norm_pow,
      show ‖(((2 * n + 1 : ℕ)) : ℂ)‖ = (2 * (n : ℝ) + 1) from by
        rw [Complex.norm_def, Complex.normSq_natCast,
          Real.sqrt_mul_self (show (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) by positivity)]
        push_cast
        ring]
    have h2 : ‖y‖ ^ (2 * n + 1 - 1) ≤ ρ ^ (2 * n) := by
      have h3 : 2 * n + 1 - 1 = 2 * n := by omega
      rw [h3]
      exact pow_le_pow_left₀ (norm_nonneg y) hyρ _
    have hc : (0 : ℝ) ≤ 2 * (n : ℝ) + 1 := by positivity
    have hCr : (0 : ℝ) ≤ Cr r := (Cr_pos (by linarith : 1 ≤ r)).le
    have hd : (0 : ℝ) ≤ ‖y‖ ^ (2 * n + 1 - 1) := pow_nonneg (norm_nonneg y) _
    have hb : (0 : ℝ) ≤ Cr r * (2 * (n : ℝ) + 1) := mul_nonneg hCr hc
    have h4 : ErCoeff r n * (2 * (n : ℝ) + 1) * ‖y‖ ^ (2 * n + 1 - 1)
        ≤ Cr r * (2 * (n : ℝ) + 1) * ρ ^ (2 * n) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (ErCoeff_le_Cr hr n) hc) h2 hd hb
    calc ErCoeff r n * ((2 * (n : ℝ) + 1) * ‖y‖ ^ (2 * n + 1 - 1))
        = ErCoeff r n * (2 * (n : ℝ) + 1) * ‖y‖ ^ (2 * n + 1 - 1) := by ring
      _ ≤ Cr r * (2 * (n : ℝ) + 1) * ρ ^ (2 * n) := h4
      _ = Cr r * ((2 * (n : ℝ) + 1) * ρ ^ (2 * n)) := by ring
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (𝕜 := ℂ) (u := fun k : ℕ => Cr r * ((2 * (k : ℝ) + 1) * ρ ^ (2 * k)))
    (t := Metric.ball (0 : ℂ) ρ) (y₀ := z)
    (g := fun n y => (ErCoeff r n : ℂ) * y ^ (2 * n + 1))
    (g' := fun n y => (ErCoeff r n : ℂ) * (((2 * n + 1 : ℕ) : ℂ) * y ^ (2 * n + 1 - 1)))
    hu Metric.isOpen_ball (convex_ball (0 : ℂ) ρ).isPreconnected hterm hbound hzρ'
    (summable_ErCoeff_mul_pow r hr hz) hzρ'
  have hder : (∑' n : ℕ, (ErCoeff r n : ℂ) * (((2 * n + 1 : ℕ) : ℂ) * z ^ (2 * n + 1 - 1)))
      = (∑' k : ℕ, (ErCoeff r k : ℂ) * (((2 * k + 1 : ℕ) : ℂ) * z ^ (2 * k))) := by
    refine tsum_congr fun n => ?_
    rw [show 2 * n + 1 - 1 = 2 * n from by omega]
  rw [hder] at hmain
  exact hmain

theorem differentiableAt_ErComplex (r : ℕ) (hr : 2 ≤ r) {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (ErComplex r) z :=
  (hasDerivAt_ErComplex r hr hz).differentiableAt

theorem differentiableOn_ErComplex (r : ℕ) (hr : 2 ≤ r) :
    DifferentiableOn ℂ (ErComplex r) (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  exact DifferentiableAt.differentiableWithinAt (s := Metric.ball (0 : ℂ) 1)
    (differentiableAt_ErComplex r hr (by simpa using Metric.mem_ball.mp hz))

/-- `R_r(π) ≥ 0`: a limit of the strict positivity on `(0, π)` (Vietoris's theorem,
`Grothendieck.vietoris_pos`, after normalising by `Cr r > 0`). -/
theorem ErCos_pi_nonneg (r : ℕ) (hr : 2 ≤ r)
    (hpos : ∀ t : ℝ, 0 < t → t < Real.pi → 0 < ErCos r t) : 0 ≤ ErCos r Real.pi := by
  have htend : Tendsto (ErCos r) (𝓝[<] Real.pi) (𝓝 (ErCos r Real.pi)) :=
    (continuous_ErCos r hr).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto tendsto_const_nhds htend ?_
  filter_upwards [Ioo_mem_nhdsLT Real.pi_pos] with t ht
  exact le_of_lt (hpos t ht.1 ht.2)

/-- `R_r` is antitone on `(0, π)` as soon as `R_r' ≤ 0` there, hence `R_r(π) ≤ R_r(x)`. -/
theorem ErCos_pi_le_of_deriv_nonpos (r : ℕ) (hr : 2 ≤ r)
    (hdiff : DifferentiableOn ℝ (ErCos r) (Set.Ioo (0 : ℝ) Real.pi))
    (hneg : ∀ t ∈ Set.Ioo (0 : ℝ) Real.pi, deriv (ErCos r) t ≤ 0)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) Real.pi) :
    ErCos r Real.pi ≤ ErCos r x := by
  have hanti : AntitoneOn (ErCos r) (Set.Ioo (0 : ℝ) Real.pi) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo (0 : ℝ) Real.pi)
      (continuous_ErCos r hr).continuousOn ?_ ?_
    · rwa [interior_Ioo]
    · intro t ht
      rw [interior_Ioo] at ht
      exact hneg t ht
  have htend : Tendsto (ErCos r) (𝓝[<] Real.pi) (𝓝 (ErCos r Real.pi)) :=
    (continuous_ErCos r hr).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto htend tendsto_const_nhds ?_
  filter_upwards [Ioo_mem_nhdsLT hx.2] with t ht
  exact hanti hx ⟨hx.1.trans ht.1, ht.2⟩ ht.1.le

/-- **Lemma 3.5 from the two claims the paper makes about `R_r`**: `R_r' ≤ 0` on `(0, π)` and
`R_r > 0` on `(0, π)`. -/
theorem cr_eq_norm_I_of_deriv (r : ℕ) (hr : 2 ≤ r)
    (hdiff : DifferentiableOn ℝ (ErCos r) (Set.Ioo (0 : ℝ) Real.pi))
    (hneg : ∀ t ∈ Set.Ioo (0 : ℝ) Real.pi, deriv (ErCos r) t ≤ 0)
    (hpos : ∀ t : ℝ, 0 < t → t < Real.pi → 0 < ErCos r t) :
    cr r = ‖ErComplex r Complex.I‖ :=
  cr_eq_norm_I_of_mono r hr
    (fun x hx0 hx1 => ErCos_pi_le_of_deriv_nonpos r hr hdiff hneg ⟨hx0, hx1⟩)
    (ErCos_pi_nonneg r hr hpos)

end Grothendieck

/-! ### The Beta-integral representation of the cosine series (Vietoris leaf, copied verbatim) -/

namespace VietorisAux

/-! ## Pochhammer polynomial and binomial-series facts -/

theorem ascPochhammer_eval_eq_prod (z : ℂ) (n : ℕ) :
    (ascPochhammer ℂ n).eval z = ∏ i ∈ Finset.range n, (z + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih, Finset.prod_range_succ]

theorem ofReal_risingFact (a : ℝ) (n : ℕ) :
    ((Grothendieck.risingFact a n : ℝ) : ℂ) = ∏ i ∈ Finset.range n, ((a : ℂ) + i) := by
  rw [Grothendieck.risingFact]
  push_cast
  rfl

/-- `Ring.choose (n - 1/2) n = (1/2)_n / n!` -/
theorem choose_eq_risingFact (n : ℕ) :
    Ring.choose ((1/2 : ℂ) + (n : ℂ) - 1) n
      = ((Grothendieck.risingFact (1/2) n : ℝ) : ℂ) / (n.factorial : ℂ) := by
  have h1 : (n.factorial : ℂ) * Ring.choose ((1/2 : ℂ) + (n : ℂ) - 1) n
      = (descPochhammer ℤ n).smeval ((1/2 : ℂ) + (n : ℂ) - 1) := by
    have := Ring.descPochhammer_eq_factorial_smul_choose ((1/2 : ℂ) + (n : ℂ) - 1) n
    rw [nsmul_eq_mul] at this
    exact this.symm
  have h2 : (descPochhammer ℤ n).smeval ((1/2 : ℂ) + (n : ℂ) - 1)
      = ((Grothendieck.risingFact (1/2) n : ℝ) : ℂ) := by
    rw [Polynomial.descPochhammer_smeval_eq_ascPochhammer,
      Polynomial.ascPochhammer_smeval_eq_eval, ascPochhammer_eval_eq_prod, ofReal_risingFact]
    refine Finset.prod_congr rfl ?_
    intro i _
    push_cast
    ring
  have h3 := h1.trans h2
  rw [eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), mul_comm]
  exact h3

/-- The binomial series `1/(1-w)^(1/2) = ∑_k (1/2)_k/k! w^k` for `‖w‖ < 1`. -/
theorem hasSum_binom_series (w : ℂ) (hw : ‖w‖ < 1) :
    HasSum (fun k : ℕ => ((Grothendieck.risingFact (1/2) k : ℝ) : ℂ) / (k.factorial : ℂ) * w ^ k)
      (1 / (1 - w) ^ (1/2 : ℂ)) := by
  have h := Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (1/2 : ℂ)
  have hmem : w ∈ Metric.eball (0 : ℂ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]
    exact hw
  have hs := h.hasSum hmem
  have hpt : ∀ k : ℕ,
      ((FormalMultilinearSeries.ofScalars ℂ fun n => Ring.choose ((1/2 : ℂ) + ↑n - 1) n) k)
        (fun _ => w)
      = ((Grothendieck.risingFact (1/2) k : ℝ) : ℂ) / (k.factorial : ℂ) * w ^ k := by
    intro k
    simp only [FormalMultilinearSeries.ofScalars]
    rw [choose_eq_risingFact]
    simp
  simpa only [hpt, zero_add] using hs

/-! ## Positivity of the real part -/

theorem pow_mul_exp_re (x t : ℝ) (k : ℕ) :
    (((x : ℂ) * Complex.exp (t * Complex.I)) ^ k).re = x ^ k * Real.cos (k * t) := by
  rw [mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul]
  have hk : (↑k : ℂ) * (t * Complex.I) = (((k : ℝ) * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hk, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]

theorem re_one_sub_mul_exp_pos {t : ℝ} (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (ht0 : 0 < t) (ht1 : t < π) :
    0 < (1 - (x : ℂ) * Complex.exp (t * Complex.I)).re := by
  rw [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]
  have hpi : t < 2 * π := by linarith [Real.pi_pos]
  have hcos1 : Real.cos t < 1 := by
    rcases lt_or_eq_of_le (Real.cos_le_one t) with h | h
    · exact h
    · exfalso
      rw [Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hpi] at h
      linarith
  rcases le_total 0 (Real.cos t) with hc | hc
  · nlinarith [mul_le_mul_of_nonneg_right hx1 hc]
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos hx0 hc]

theorem cpow_half_ne_zero {z : ℂ} (hz : z ≠ 0) : z ^ (1/2 : ℂ) ≠ 0 := by
  intro h
  have hvv : z ^ (1/2 : ℂ) * z ^ (1/2 : ℂ) = z := by
    rw [← Complex.cpow_add _ _ hz, show ((1/2 : ℂ) + (1/2 : ℂ)) = 1 by norm_num,
      Complex.cpow_one]
  rw [h, mul_zero] at hvv
  exact hz hvv.symm

/-- For `x ∈ [0,1]` and `t ∈ (0,π)`, the real part of `1/(1-x e^{it})^{1/2}` is nonzero. -/
theorem re_inv_cpow_ne_zero {t : ℝ} (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (ht0 : 0 < t) (ht1 : t < π) :
    (1 / (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ)).re ≠ 0 := by
  set z : ℂ := 1 - (x : ℂ) * Complex.exp (t * Complex.I) with hzdef
  have hzre : 0 < z.re := by
    rw [hzdef]; exact re_one_sub_mul_exp_pos x hx0 hx1 ht0 ht1
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzre; simp at hzre
  set v : ℂ := z ^ (1/2 : ℂ) with hvdef
  have hvv : v * v = z := by
    rw [hvdef, ← Complex.cpow_add _ _ hz,
      show ((1/2 : ℂ) + (1/2 : ℂ)) = 1 by norm_num, Complex.cpow_one]
  have hvne : v ≠ 0 := by
    rw [hvdef]; exact cpow_half_ne_zero hz
  have hvrels : v.re * v.re = v.im * v.im + z.re := by
    have h := congrArg Complex.re hvv
    simp only [Complex.mul_re] at h
    linarith
  have hvr : v.re ≠ 0 := by
    have hpos : 0 < v.re * v.re := by
      rw [hvrels]; nlinarith [sq_nonneg v.im, hzre]
    exact fun h => absurd hpos (by rw [h, mul_zero]; exact lt_irrefl 0)
  have hval : (1 / v).re = v.re / ‖v‖ ^ 2 := by
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  rw [hval]
  exact div_ne_zero hvr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hvne))

/-- For `t ∈ (0,π)` and all `x ∈ [0,1]`, `Re (1/(1-x e^{it})^{1/2}) > 0`. -/
theorem re_inv_cpow_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < π) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < (1 / (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ)).re := by
  set g : ℝ → ℝ :=
    fun x => (1 / (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ)).re with hg
  have hne : ∀ x ∈ Set.Icc (0 : ℝ) 1, g x ≠ 0 := by
    intro x hx
    rw [hg]
    exact re_inv_cpow_ne_zero x hx.1 hx.2 ht0 ht1
  have hbase : Continuous fun x : ℝ => 1 - (x : ℂ) * Complex.exp (t * Complex.I) := by
    fun_prop
  have hslit : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ∈ Complex.slitPlane := by
    intro x hx
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (re_one_sub_mul_exp_pos x hx.1 hx.2 ht0 ht1)
  have hcpow : ContinuousOn
      (fun x : ℝ => (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ))
      (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    exact hbase.continuousWithinAt.cpow continuousWithinAt_const (hslit x hx)
  have hnonzero : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ) ≠ 0 := by
    intro x hx
    refine cpow_half_ne_zero (z := 1 - (x : ℂ) * Complex.exp (t * Complex.I)) ?_
    intro h
    have hzre := re_one_sub_mul_exp_pos x hx.1 hx.2 ht0 ht1
    rw [h] at hzre
    simp at hzre
  have hinv : ContinuousOn
      (fun x : ℝ => 1 / (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ))
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.div hcpow hnonzero
  have hgc : ContinuousOn g (Set.Icc (0 : ℝ) 1) := Complex.continuous_re.comp_continuousOn hinv
  have hg0 : g 0 = 1 := by
    rw [hg]
    norm_num
  intro x hx
  rcases lt_trichotomy (g x) 0 with h | h | h
  · have hcont : ContinuousOn g (Set.Icc (0 : ℝ) x) :=
      hgc.mono fun y hy => ⟨hy.1, hy.2.trans hx.2⟩
    have hmem : (0 : ℝ) ∈ Set.Icc (g x) (g 0) := ⟨h.le, by rw [hg0]; norm_num⟩
    obtain ⟨y, hy, hyv⟩ := intermediate_value_Icc' hx.1 hcont hmem
    exact absurd hyv (hne y ⟨hy.1, hy.2.trans hx.2⟩)
  · exfalso; exact hne x hx h
  · exact h

/-- The Beta-type moment `∫_0^1 x^{k-1/2} (1-x)^{r/2-1/2} dx`. -/
def Jb (r k : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x ^ ((k : ℝ) - 1/2) * (1 - x) ^ ((r : ℝ)/2 - 1/2)

/-- The constant `c = r/2 + 1`. -/
def cc (r : ℕ) : ℝ := (r : ℝ)/2 + 1

theorem Jb_eq_betaIntegral (r k : ℕ) :
    ((Jb r k : ℝ) : ℂ)
      = Complex.betaIntegral (((k : ℝ) + 1/2 : ℝ) : ℂ) ((((r : ℝ) + 1)/2 : ℝ) : ℂ) := by
  have h1 : ((Jb r k : ℝ) : ℂ)
      = ∫ x in (0 : ℝ)..1,
          ((x ^ ((k : ℝ) - 1/2) * (1 - x) ^ ((r : ℝ)/2 - 1/2) : ℝ) : ℂ) := by
    rw [Jb, intervalIntegral.integral_ofReal]
  rw [h1, Complex.betaIntegral]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with x hx
  have hx' : x ∈ Set.Ioc (0:ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
  have hxpos : 0 < x := hx'.1
  have e1 : (((k : ℝ) - 1/2 : ℝ) : ℂ) = (((k : ℝ) + 1/2 : ℝ) : ℂ) - 1 := by push_cast; ring
  have e2 : ((((r : ℝ)/2 - 1/2) : ℝ) : ℂ) = (((((r : ℝ) + 1)/2) : ℝ) : ℂ) - 1 := by push_cast; ring
  have e3 : ((1 - x : ℝ) : ℂ) = 1 - (x : ℂ) := by push_cast; ring
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hxpos.le,
    Complex.ofReal_cpow (show (0:ℝ) ≤ 1 - x by linarith [hx'.2]), e1, e2, e3]

theorem Jb_eq_gamma (r k : ℕ) :
    Jb r k = Real.Gamma ((k : ℝ) + 1/2) * Real.Gamma (((r : ℝ) + 1)/2)
      / Real.Gamma ((k : ℝ) + cc r) := by
  have hu : (0:ℝ) < ((((k : ℝ) + 1/2 : ℝ)) : ℂ).re := by
    have h : (0:ℝ) < (k : ℝ) + 1/2 := by positivity
    simpa using h
  have hv : (0:ℝ) < ((((r : ℝ) + 1)/2 : ℝ) : ℂ).re := by
    have h : (0:ℝ) < ((r : ℝ) + 1)/2 := by positivity
    simpa using h
  have hG : ((Jb r k : ℝ) : ℂ)
      = Complex.Gamma ((((k : ℝ) + 1/2 : ℝ)) : ℂ) * Complex.Gamma (((((r : ℝ) + 1)/2 : ℝ)) : ℂ)
        / Complex.Gamma (((((k : ℝ) + 1/2 : ℝ)) : ℂ) + (((((r : ℝ) + 1)/2 : ℝ)) : ℂ)) := by
    rw [Jb_eq_betaIntegral r k, Complex.betaIntegral_eq_Gamma_mul_div _ _ hu hv]
  have key : ((Real.Gamma ((k : ℝ) + 1/2) * Real.Gamma (((r : ℝ) + 1)/2)
      / Real.Gamma ((k : ℝ) + cc r) : ℝ) : ℂ)
      = Complex.Gamma ((((k : ℝ) + 1/2 : ℝ)) : ℂ) * Complex.Gamma (((((r : ℝ) + 1)/2 : ℝ)) : ℂ)
        / Complex.Gamma (((((k : ℝ) + 1/2 : ℝ)) : ℂ) + (((((r : ℝ) + 1)/2 : ℝ)) : ℂ)) := by
    rw [Complex.ofReal_div, Complex.ofReal_mul, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal,
      ← Complex.Gamma_ofReal]
    congr 2
    simp only [cc]
    push_cast
    ring
  exact Complex.ofReal_inj.mp (hG.trans key.symm)

theorem gamma_add_nat_div_eq_risingFact (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Real.Gamma ((k : ℝ) + a) / Real.Gamma a = Grothendieck.risingFact a k := by
  have hz : ∀ m : ℕ, (a : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have h2 : a = -(m : ℝ) := by
      have hh := congrArg Complex.re h
      simpa using hh
    have : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have h := Complex.Gamma_add_nat_div_Gamma_eq (a : ℂ) hz (n := k)
  have hmain : Complex.Gamma ((a : ℂ) + (k : ℂ)) / Complex.Gamma (a : ℂ)
      = ((Grothendieck.risingFact a k : ℝ) : ℂ) := by
    rw [h, ascPochhammer_eval_eq_prod, ofReal_risingFact]
  have hreal : ((Real.Gamma ((k : ℝ) + a) / Real.Gamma a : ℝ) : ℂ)
      = Complex.Gamma ((a : ℂ) + (k : ℂ)) / Complex.Gamma (a : ℂ) := by
    rw [Complex.ofReal_div, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal]
    have e : (((k : ℝ) + a : ℝ) : ℂ) = ((a : ℂ) + (k : ℂ)) := by push_cast; ring
    rw [e]
  exact Complex.ofReal_inj.mp (hreal.trans hmain)

theorem Jb_pos (r k : ℕ) : 0 < Jb r k := by
  rw [Jb_eq_gamma r k]
  have h1 : 0 < Real.Gamma ((k : ℝ) + 1/2) := Real.Gamma_pos_of_pos (by positivity)
  have h2 : 0 < Real.Gamma (((r : ℝ) + 1)/2) := Real.Gamma_pos_of_pos (by positivity)
  have h3 : 0 < Real.Gamma ((k : ℝ) + cc r) := Real.Gamma_pos_of_pos (by
    simp only [cc]; positivity)
  positivity

/-- Ratio formula: `Jb r k = Jb r 0 * ((1/2)_k / (r/2+1)_k)`. -/
theorem Jb_ratio (r k : ℕ) :
    Jb r k = Jb r 0 * (Grothendieck.risingFact (1/2) k / Grothendieck.risingFact (cc r) k) := by
  have hcpos : 0 < cc r := by simp only [cc]; positivity
  have hA : Real.Gamma ((k : ℝ) + 1/2) / Real.Gamma (1/2) = Grothendieck.risingFact (1/2) k := by
    simpa using gamma_add_nat_div_eq_risingFact (1/2) (by norm_num) k
  have hB : Real.Gamma ((k : ℝ) + cc r) / Real.Gamma (cc r) = Grothendieck.risingFact (cc r) k :=
    gamma_add_nat_div_eq_risingFact (cc r) hcpos k
  have hA0 : Real.Gamma (1/2) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hB0 : Real.Gamma (cc r) ≠ 0 := (Real.Gamma_pos_of_pos hcpos).ne'
  have hAk : Real.Gamma ((k : ℝ) + 1/2) = Grothendieck.risingFact (1/2) k * Real.Gamma (1/2) := by
    have hh := congrArg (· * Real.Gamma (1/2)) hA
    rwa [div_mul_cancel₀ _ hA0] at hh
  have hBk : Real.Gamma ((k : ℝ) + cc r) = Grothendieck.risingFact (cc r) k * Real.Gamma (cc r) := by
    have hh := congrArg (· * Real.Gamma (cc r)) hB
    rwa [div_mul_cancel₀ _ hB0] at hh
  rw [Jb_eq_gamma r k, Jb_eq_gamma r 0, hAk, hBk]
  simp only [Nat.cast_zero, zero_add]
  have hG : Real.Gamma (((r : ℝ) + 1)/2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  field_simp
/-- The real cosine series coming from the binomial series at `w = x·e^{it}`. -/
theorem hasSum_series_re {t : ℝ} (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun k : ℕ => (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) * x ^ k
        * Real.cos (k * t))
      ((1 / (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ)).re) := by
  have hw : ‖(x : ℂ) * Complex.exp (t * Complex.I)‖ < 1 := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hx1
  have hs := (hasSum_binom_series _ hw).map Complex.reCLM Complex.reCLM.continuous
  have hc : ∀ k : ℕ, (((Grothendieck.risingFact (1/2) k : ℝ) : ℂ) / (k.factorial : ℂ))
      = (((Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) : ℝ) : ℂ) := by
    intro k
    rw [Complex.ofReal_div]
    push_cast
    try ring
  have hterm : ∀ k : ℕ,
      ((((Grothendieck.risingFact (1/2) k : ℝ) : ℂ) / (k.factorial : ℂ))
          * ((x : ℂ) * Complex.exp (t * Complex.I)) ^ k).re
      = (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) * x ^ k * Real.cos (k * t) := by
    intro k
    rw [hc k, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      pow_mul_exp_re]
    ring
  simp only [Function.comp_def, Complex.reCLM_apply] at hs ⊢
  rw [funext hterm] at hs
  exact hs

/-- Closed form of the underlying nonnegative series at a real point. -/
theorem hasSum_closed {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun k : ℕ => (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) * x ^ k)
      ((1 - x) ^ (-(1/2) : ℝ)) := by
  have hw : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  have hs := (hasSum_binom_series (x : ℂ) hw).map Complex.reCLM Complex.reCLM.continuous
  have hc : ∀ k : ℕ, (((Grothendieck.risingFact (1/2) k : ℝ) : ℂ) / (k.factorial : ℂ))
      = (((Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) : ℝ) : ℂ) := by
    intro k
    rw [Complex.ofReal_div]
    push_cast
    try ring
  have hterm : ∀ k : ℕ,
      ((((Grothendieck.risingFact (1/2) k : ℝ) : ℂ) / (k.factorial : ℂ)) * (x : ℂ) ^ k).re
      = (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) * x ^ k := by
    intro k
    rw [hc k, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      ← Complex.ofReal_pow, Complex.ofReal_re]
  have hrhs : ((1 / (1 - (x : ℂ)) ^ (1/2 : ℂ))).re = (1 - x) ^ (-(1/2) : ℝ) := by
    have h1x : (0:ℝ) < 1 - x := by linarith
    have hcast : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
    have e : ((1 - x : ℝ) : ℂ) ^ (1/2 : ℂ) = ((Real.sqrt (1 - x) : ℝ) : ℂ) := by
      rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow h1x.le (1/2 : ℝ), ← Real.sqrt_eq_rpow]
    rw [hcast, e, one_div, ← Complex.ofReal_inv, Complex.ofReal_re]
    rw [show ((Real.sqrt (1 - x))⁻¹ : ℝ) = (1 - x) ^ (-(1/2) : ℝ) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h1x.le]]
  simp only [Function.comp_def, Complex.reCLM_apply] at hs ⊢
  rw [funext hterm, hrhs] at hs
  exact hs

/-! ## The weight, the summands and term-by-term integration -/

/-- The weight `x^{k-1/2}(1-x)^{r/2-1/2}`. -/
def Wt (r k : ℕ) (x : ℝ) : ℝ := x ^ ((k : ℝ) - 1/2) * (1 - x) ^ ((r : ℝ)/2 - 1/2)

/-- The term of the cosine series multiplied by the weight. -/
def Fn (r : ℕ) (t : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) * Real.cos (k * t) * Wt r k x

/-- The real part function whose positivity is the crux. -/
def Gt (t : ℝ) (x : ℝ) : ℝ :=
  (1 / (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ)).re

theorem Jb_eq_setIntegral (r k : ℕ) :
    Jb r k = ∫ x in Set.Ioo (0 : ℝ) 1, Wt r k x := by
  have h : Jb r k = ∫ x in Set.Ioo (0 : ℝ) 1,
      x ^ ((k : ℝ) - 1/2) * (1 - x) ^ ((r : ℝ)/2 - 1/2) := by
    rw [Jb, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
  rw [h]
  rfl

theorem Wt_nonneg (r k : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) : 0 ≤ Wt r k x := by
  rw [Wt]
  exact mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.rpow_nonneg (by linarith [hx.2]) _)

theorem Wt_le_invSqrt (r k : ℕ) (hr : 2 ≤ r) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    Wt r k x ≤ x ^ (-(1/2) : ℝ) := by
  have h2r : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hα : 0 ≤ (r : ℝ)/2 - 1/2 := by linarith
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have hA : (1 - x) ^ ((r : ℝ)/2 - 1/2) ≤ 1 :=
    Real.rpow_le_one (by linarith) (by linarith) hα
  have hA0 : 0 ≤ (1 - x) ^ ((r : ℝ)/2 - 1/2) := Real.rpow_nonneg (by linarith) _
  have hB : x ^ ((k:ℝ)) ≤ 1 := Real.rpow_le_one hx0.le hx1.le (Nat.cast_nonneg k)
  have hC : 0 ≤ x ^ (-(1/2) : ℝ) := Real.rpow_nonneg hx0.le _
  have hW : Wt r k x = x ^ (k:ℝ) * x ^ (-(1/2) : ℝ) * (1 - x) ^ ((r : ℝ)/2 - 1/2) := by
    rw [Wt, ← Real.rpow_add hx0,
      show ((k : ℝ) + -(1/2)) = (k : ℝ) - 1/2 by ring]
  rw [hW]
  have hstep : x ^ (k:ℝ) * x ^ (-(1/2) : ℝ) * (1 - x) ^ ((r : ℝ)/2 - 1/2)
      ≤ 1 * x ^ (-(1/2) : ℝ) * 1 := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hB hC
    · exact hA
    · exact hA0
    · exact mul_nonneg zero_le_one hC
  linarith [hstep]

theorem integral_invSqrt :
    ∫ x in Set.Ioo (0:ℝ) 1, x ^ (-(1/2) : ℝ) = 2 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/2)))]
  norm_num

theorem integrable_invSqrt :
    IntegrableOn (fun x : ℝ => x ^ (-(1/2) : ℝ)) (Set.Ioo (0:ℝ) 1) :=
  (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ) < 1)).mpr
    (by norm_num : (-1:ℝ) < -(1/2))

theorem continuousOn_Wt (r k : ℕ) : ContinuousOn (Wt r k) (Set.Ioo (0:ℝ) 1) := by
  have h1 : ContinuousOn (fun x : ℝ => x ^ ((k:ℝ) - 1/2)) (Set.Ioo (0:ℝ) 1) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl hx.1.ne')
  have h2 : ContinuousOn (fun x : ℝ => (1 - x) ^ ((r:ℝ)/2 - 1/2)) (Set.Ioo (0:ℝ) 1) :=
    (continuousOn_const.sub continuousOn_id).rpow_const
      (fun x hx => Or.inl (by linarith [hx.2] : (1:ℝ) - x ≠ 0))
  exact h1.mul h2

theorem coeff_nonneg (k : ℕ) :
    (0:ℝ) ≤ Grothendieck.risingFact (1/2) k / (k.factorial : ℝ) := by
  rw [Grothendieck.risingFact]
  exact div_nonneg (Finset.prod_nonneg fun i _ => by positivity) (Nat.cast_nonneg k.factorial)

theorem integrable_Wt (r k : ℕ) (hr : 2 ≤ r) :
    Integrable (Wt r k) (volume.restrict (Set.Ioo (0:ℝ) 1)) := by
  refine Integrable.mono' integrable_invSqrt ?_ ?_
  · exact (continuousOn_Wt r k).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Wt_nonneg r k hx)]
    exact Wt_le_invSqrt r k hr hx

theorem integral_Wt (r k : ℕ) :
    ∫ x in Set.Ioo (0:ℝ) 1, Wt r k x = Jb r k :=
  (Jb_eq_setIntegral r k).symm

theorem integral_Fn (r : ℕ) (t : ℝ) (k : ℕ) :
    ∫ x in Set.Ioo (0:ℝ) 1, Fn r t k x
      = (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) * Real.cos (k * t) * Jb r k := by
  rw [show (fun x => Fn r t k x) = (fun x => ((Grothendieck.risingFact (1/2) k / (k.factorial : ℝ))
      * Real.cos (k * t)) * Wt r k x) from rfl, MeasureTheory.integral_const_mul,
    integral_Wt r k]

theorem integrable_Fn (r : ℕ) (t : ℝ) (k : ℕ) (hr : 2 ≤ r) :
    Integrable (Fn r t k) (volume.restrict (Set.Ioo (0:ℝ) 1)) := by
  refine (integrable_invSqrt.const_mul |Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)|).mono' ?_ ?_
  · have h1 : ContinuousOn (fun x : ℝ => Grothendieck.risingFact (1/2) k / (k.factorial : ℝ))
        (Set.Ioo (0:ℝ) 1) := continuousOn_const
    have h2 : ContinuousOn (fun x : ℝ => Real.cos (k * t)) (Set.Ioo (0:ℝ) 1) := by fun_prop
    exact ((h1.mul h2).mul (continuousOn_Wt r k)).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hc : (0:ℝ) ≤ Grothendieck.risingFact (1/2) k / (k.factorial : ℝ) := coeff_nonneg k
    have hW : Wt r k x ≤ x ^ (-(1/2) : ℝ) := Wt_le_invSqrt r k hr hx
    have hW0 : 0 ≤ Wt r k x := Wt_nonneg r k hx
    have hb : 0 ≤ x ^ (-(1/2) : ℝ) := Real.rpow_nonneg hx.1.le _
    have hcos : |Real.cos (k * t)| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    calc ‖Fn r t k x‖
        = (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) * |Real.cos (k * t)| * Wt r k x := by
          rw [Real.norm_eq_abs, show Fn r t k x = (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ))
            * Real.cos (k * t) * Wt r k x from rfl, abs_mul, abs_mul, abs_of_nonneg hc,
            abs_of_nonneg hW0]
      _ = (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ))
            * (|Real.cos (k * t)| * Wt r k x) := by ring
      _ ≤ (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) * (1 * x ^ (-(1/2) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hc
          exact mul_le_mul hcos hW hW0 (by norm_num)
      _ = |Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)| * x ^ (-(1/2) : ℝ) := by
          rw [abs_of_nonneg hc]; ring
/-! ## Summability of the integrated norms -/

/-- `a_k = (1/2)_k (1/2)_k / ((r/2+1)_k k!)`. -/
def ak (r k : ℕ) : ℝ :=
  Grothendieck.risingFact (1/2) k * Grothendieck.risingFact (1/2) k
    / (Grothendieck.risingFact (cc r) k * (k.factorial : ℝ))

theorem ak_eq (r k : ℕ) :
    ak r k = Grothendieck.risingFact (1/2) k * Grothendieck.risingFact (1/2) k
      / (Grothendieck.risingFact (cc r) k * (k.factorial : ℝ)) := rfl

theorem risingFact_succ' (a : ℝ) (k : ℕ) :
    Grothendieck.risingFact a (k+1) = Grothendieck.risingFact a k * (a + (k:ℝ)) := by
  rw [Grothendieck.risingFact, Grothendieck.risingFact, Finset.prod_range_succ]

theorem risingFact_pos_one_half (k : ℕ) : 0 < Grothendieck.risingFact (1/2) k := by
  rw [Grothendieck.risingFact]
  exact Finset.prod_pos fun i _ => by positivity

theorem cc_pos (r : ℕ) : 0 < cc r := by simp only [cc]; positivity

theorem risingFact_pos_cc (r k : ℕ) : 0 < Grothendieck.risingFact (cc r) k := by
  rw [Grothendieck.risingFact]
  exact Finset.prod_pos fun i _ => by
    have h : (0:ℝ) < cc r := cc_pos r
    positivity

theorem ak_nonneg (r k : ℕ) : 0 ≤ ak r k := by
  rw [ak_eq]
  exact div_nonneg (mul_nonneg (risingFact_pos_one_half k).le (risingFact_pos_one_half k).le)
    (mul_nonneg (risingFact_pos_cc r k).le (by positivity))

theorem ak_pos (r k : ℕ) : 0 < ak r k := by
  rw [ak_eq]
  exact div_pos (mul_pos (risingFact_pos_one_half k) (risingFact_pos_one_half k))
    (mul_pos (risingFact_pos_cc r k) (by positivity))

theorem ak_ratio (r k : ℕ) :
    ak r (k+1) = ak r k * ((1/2 + (k:ℝ))^2 / ((cc r + (k:ℝ)) * ((k:ℝ)+1))) := by
  have h1 : Grothendieck.risingFact (1/2) (k+1)
      = Grothendieck.risingFact (1/2) k * (1/2 + (k:ℝ)) := risingFact_succ' (1/2) k
  have h2 : Grothendieck.risingFact (cc r) (k+1)
      = Grothendieck.risingFact (cc r) k * (cc r + (k:ℝ)) := risingFact_succ' (cc r) k
  have h3 : (((k+1).factorial : ℕ) : ℝ) = (k.factorial : ℝ) * ((k:ℝ)+1) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hA : (0:ℝ) < Grothendieck.risingFact (1/2) k := risingFact_pos_one_half k
  have hB : (0:ℝ) < Grothendieck.risingFact (cc r) k := risingFact_pos_cc r k
  have hC : (0:ℝ) < (k.factorial : ℝ) := by positivity
  have hD : (0:ℝ) < cc r + (k:ℝ) := by have := cc_pos r; positivity
  have hE : (0:ℝ) < (k:ℝ) + 1 := by positivity
  rw [ak_eq, ak_eq, h1, h2, h3]
  field_simp

theorem ak_step (r k : ℕ) (hr : 2 ≤ r) :
    ak r (k+1) * ((k:ℝ)+2)^2 ≤ ak r k * ((k:ℝ)+1)^2 := by
  have h2r : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hcc : (2:ℝ) ≤ cc r := by simp only [cc]; linarith
  have hA : (0:ℝ) < ak r k := ak_pos r k
  have hD : (0:ℝ) < cc r + (k:ℝ) := by have := cc_pos r; positivity
  have hE : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hF : (0:ℝ) < (k:ℝ) + 2 := by positivity
  have hkey : (1/2 + (k:ℝ))^2 * ((k:ℝ)+2) ≤ ((k:ℝ)+1)^3 := by nlinarith
  have hfrac : (1/2 + (k:ℝ))^2 / ((cc r + (k:ℝ)) * ((k:ℝ)+1)) * ((k:ℝ)+2)^2
      ≤ ((k:ℝ)+1)^2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h1 : (2:ℝ) + (k:ℝ) ≤ cc r + (k:ℝ) := by linarith
    have h2 : (1/2 + (k:ℝ))^2 * ((k:ℝ)+2)^2 ≤ ((k:ℝ)+1)^3 * ((k:ℝ)+2) := by
      have hm := mul_le_mul_of_nonneg_right hkey hF.le
      linarith [hm]
    have h3 : ((k:ℝ)+1)^3 * ((k:ℝ)+2) ≤ ((k:ℝ)+1)^3 * (cc r + (k:ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith : (k:ℝ)+2 ≤ cc r + (k:ℝ)) (by positivity)
    nlinarith [h2, h3]
  rw [ak_ratio]
  calc ak r k * ((1/2 + (k:ℝ))^2 / ((cc r + (k:ℝ)) * ((k:ℝ)+1))) * ((k:ℝ)+2)^2
      = ak r k * ((1/2 + (k:ℝ))^2 / ((cc r + (k:ℝ)) * ((k:ℝ)+1)) * ((k:ℝ)+2)^2) := by ring
    _ ≤ ak r k * ((k:ℝ)+1)^2 := by
        exact mul_le_mul_of_nonneg_left hfrac hA.le

theorem ak_mul_le (r k : ℕ) (hr : 2 ≤ r) : ak r k * ((k:ℝ)+1)^2 ≤ 1 := by
  induction k with
  | zero =>
    rw [ak_eq]
    norm_num [Grothendieck.risingFact]
  | succ k ih =>
    have h1 : ak r (k+1) * (((k:ℝ)+1)+1)^2 ≤ ak r k * ((k:ℝ)+1)^2 := by
      have h := ak_step r k hr
      rwa [show ((k:ℝ)+1)+1 = (k:ℝ)+2 by ring]
    have h1' : ak r (k+1) * ((↑(k+1) : ℝ)+1)^2 ≤ ak r k * ((↑k : ℝ)+1)^2 := by
      push_cast
      exact h1
    have h2 : ak r k * ((↑k : ℝ)+1)^2 ≤ 1 := ih
    linarith

theorem ak_le (r k : ℕ) (hr : 2 ≤ r) : ak r k ≤ 1/((k:ℝ)+1)^2 := by
  have h := ak_mul_le r k hr
  have hpos : (0:ℝ) < ((k:ℝ)+1)^2 := by positivity
  rw [le_div_iff₀ hpos]
  exact h

theorem summable_inv_sq : Summable (fun k : ℕ => 1/((k:ℝ)+1)^2) := by
  have h : Summable (fun n : ℕ => 1/((n:ℝ))^2) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num : 1 < 2)
  have h' : Summable (fun n : ℕ => 1/(((n+1 : ℕ) : ℝ))^2) :=
    (summable_nat_add_iff (f := fun n : ℕ => 1/((n:ℝ))^2) 1).mpr h
  simpa [Nat.cast_add, Nat.cast_one] using h'

theorem integral_norm_Fn (r : ℕ) (t : ℝ) (k : ℕ) :
    ∫ x in Set.Ioo (0:ℝ) 1, ‖Fn r t k x‖
      = |Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)| * |Real.cos (k * t)| * Jb r k := by
  have hae : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0:ℝ) 1)), ‖Fn r t k x‖
      = (|Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)| * |Real.cos (k * t)|) * Wt r k x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hW0 : 0 ≤ Wt r k x := Wt_nonneg r k hx
    rw [Real.norm_eq_abs, show Fn r t k x = (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ))
      * Real.cos (k * t) * Wt r k x from rfl, abs_mul, abs_mul, abs_of_nonneg hW0]
  rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul, integral_Wt r k]

theorem integral_norm_Fn_le (r : ℕ) (t : ℝ) (k : ℕ) (hr : 2 ≤ r) :
    ∫ x in Set.Ioo (0:ℝ) 1, ‖Fn r t k x‖ ≤ Jb r 0 * ak r k := by
  rw [integral_norm_Fn, abs_of_nonneg (coeff_nonneg k)]
  have hcos : |Real.cos (k * t)| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hJ : 0 ≤ Jb r k := (Jb_pos r k).le
  have hc : (0:ℝ) ≤ Grothendieck.risingFact (1/2) k / (k.factorial : ℝ) := coeff_nonneg k
  have step : Grothendieck.risingFact (1/2) k / (k.factorial : ℝ) * |Real.cos (k * t)| * Jb r k
      ≤ Grothendieck.risingFact (1/2) k / (k.factorial : ℝ) * 1 * Jb r k := by
    apply mul_le_mul_of_nonneg_right _ hJ
    exact mul_le_mul_of_nonneg_left hcos hc
  have heq : Grothendieck.risingFact (1/2) k / (k.factorial : ℝ) * 1 * Jb r k = Jb r 0 * ak r k := by
    rw [Jb_ratio r k, ak_eq]
    field_simp
  linarith [step, heq.le, heq.ge]

theorem summable_integral_norm_Fn (r : ℕ) (t : ℝ) (hr : 2 ≤ r) :
    Summable (fun k : ℕ => ∫ x in Set.Ioo (0:ℝ) 1, ‖Fn r t k x‖) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((summable_inv_sq).mul_left (Jb r 0))
  · exact integral_nonneg fun x => norm_nonneg _
  · calc ∫ x in Set.Ioo (0:ℝ) 1, ‖Fn r t k x‖ ≤ Jb r 0 * ak r k := integral_norm_Fn_le r t k hr
      _ ≤ Jb r 0 * (1/((k:ℝ)+1)^2) := by
          exact mul_le_mul_of_nonneg_left (ak_le r k hr) (Jb_pos r 0).le
/-! ## Continuity of `Gt` and the final assembly -/

theorem Gt_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < π) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < Gt t x :=
  re_inv_cpow_pos ht0 ht1

theorem continuousOn_Gt {t : ℝ} (ht0 : 0 < t) (ht1 : t < π) :
    ContinuousOn (Gt t) (Set.Icc (0 : ℝ) 1) := by
  have hbase : Continuous fun x : ℝ => 1 - (x : ℂ) * Complex.exp (t * Complex.I) := by
    fun_prop
  have hslit : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ∈ Complex.slitPlane := by
    intro x hx
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (re_one_sub_mul_exp_pos x hx.1 hx.2 ht0 ht1)
  have hcpow : ContinuousOn
      (fun x : ℝ => (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ))
      (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    exact hbase.continuousWithinAt.cpow continuousWithinAt_const (hslit x hx)
  have hnonzero : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ) ≠ 0 := by
    intro x hx
    refine cpow_half_ne_zero (z := 1 - (x : ℂ) * Complex.exp (t * Complex.I)) ?_
    intro h
    have hzre := re_one_sub_mul_exp_pos x hx.1 hx.2 ht0 ht1
    rw [h] at hzre
    simp at hzre
  have hinv : ContinuousOn
      (fun x : ℝ => 1 / (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ))
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.div hcpow hnonzero
  exact Complex.continuous_re.comp_continuousOn hinv

theorem hasSum_Fn (r : ℕ) (t : ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    HasSum (fun k : ℕ => Fn r t k x) (Gt t x * Wt r 0 x) := by
  have hWk : ∀ k : ℕ, Wt r k x = x ^ k * Wt r 0 x := by
    intro k
    have h : x ^ ((k:ℝ)) * x ^ (-(1/2) : ℝ) = x ^ ((k:ℝ) - 1/2) := by
      rw [← Real.rpow_add hx.1]
      ring_nf
    rw [Wt, Wt, ← Real.rpow_natCast x k, ← h]
    ring
  have h := (hasSum_series_re (t := t) x hx.1.le hx.2).mul_left (Wt r 0 x)
  have hterm : ∀ k : ℕ, Wt r 0 x * ((Grothendieck.risingFact (1/2) k / (k.factorial : ℝ))
      * x ^ k * Real.cos (k * t)) = Fn r t k x := by
    intro k
    rw [Fn, hWk k]
    ring
  rw [funext hterm] at h
  have h2 : HasSum (fun k : ℕ => Fn r t k x) (Gt t x * Wt r 0 x) := by
    rw [show Gt t x = (1 / (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ)).re from rfl,
      mul_comm]
    exact h
  exact h2

theorem integral_tsum_Fn (r : ℕ) (t : ℝ) (hr : 2 ≤ r) :
    HasSum (fun k : ℕ => ∫ x in Set.Ioo (0:ℝ) 1, Fn r t k x)
      (∫ x in Set.Ioo (0:ℝ) 1, ∑' k : ℕ, Fn r t k x) := by
  refine MeasureTheory.hasSum_integral_of_summable_integral_norm (fun k => integrable_Fn r t k hr) ?_
  simpa using summable_integral_norm_Fn r t hr

theorem integral_tsum_Fn_eq (r : ℕ) (t : ℝ) :
    ∫ x in Set.Ioo (0:ℝ) 1, ∑' k : ℕ, Fn r t k x
      = ∫ x in Set.Ioo (0:ℝ) 1, Gt t x * Wt r 0 x := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact (hasSum_Fn r t hx).tsum_eq

theorem integrable_Gt_Wt (r : ℕ) (t : ℝ) (hr : 2 ≤ r) (ht0 : 0 < t) (ht1 : t < π) :
    Integrable (fun x => Gt t x * Wt r 0 x) (volume.restrict (Set.Ioo (0:ℝ) 1)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_Gt ht0 ht1)
  refine Integrable.mono' ((integrable_Wt r 0 hr).const_mul C) ?_ ?_
  · have h1 : ContinuousOn (fun x => Gt t x * Wt r 0 x) (Set.Ioo (0:ℝ) 1) :=
      (continuousOn_Gt ht0 ht1).mono Set.Ioo_subset_Icc_self |>.mul (continuousOn_Wt r 0)
    exact h1.aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hW0 : 0 ≤ Wt r 0 x := Wt_nonneg r 0 hx
    have hb : ‖Gt t x‖ ≤ C := hC x ⟨hx.1.le, hx.2.le⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hW0]
    exact mul_le_mul_of_nonneg_right hb hW0

theorem integral_Gt_Wt_pos (r : ℕ) (t : ℝ) (hr : 2 ≤ r) (ht0 : 0 < t) (ht1 : t < π) :
    0 < ∫ x in Set.Ioo (0:ℝ) 1, Gt t x * Wt r 0 x := by
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (by norm_num : (0:ℝ) ≤ 1)) (continuousOn_Gt ht0 ht1)
  have hmono : ∫ x in Set.Ioo (0:ℝ) 1, Gt t x₀ * Wt r 0 x
      ≤ ∫ x in Set.Ioo (0:ℝ) 1, Gt t x * Wt r 0 x := by
    refine MeasureTheory.integral_mono_ae ((integrable_Wt r 0 hr).const_mul _)
      (integrable_Gt_Wt r t hr ht0 ht1) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hle : Gt t x₀ ≤ Gt t x := hmin ⟨hx.1.le, hx.2.le⟩
    exact mul_le_mul_of_nonneg_right hle (Wt_nonneg r 0 hx)
  have hval : ∫ x in Set.Ioo (0:ℝ) 1, Gt t x₀ * Wt r 0 x = Gt t x₀ * Jb r 0 := by
    rw [MeasureTheory.integral_const_mul, integral_Wt r 0]
  have hm : 0 < Gt t x₀ := Gt_pos ht0 ht1 x₀ hx₀
  have hJ : 0 < Jb r 0 := Jb_pos r 0
  have hpos : 0 < ∫ x in Set.Ioo (0:ℝ) 1, Gt t x₀ * Wt r 0 x := by
    rw [hval]; exact mul_pos hm hJ
  linarith


end VietorisAux

namespace Grothendieck

/-! ### The Beta-integral representation of the boundary cosine series

This is the mechanism of the Vietoris leaf (`VietorisAux.integral_Gt_Wt_pos`), reused to get *both*
the positivity and the monotonicity of `R_r` on `(0, π)`. -/

theorem ErCoeff_eq_Cr_mul_akV (r k : ℕ) : ErCoeff r k = Cr r * VietorisAux.ak r k := by
  unfold ErCoeff VietorisAux.ak VietorisAux.cc
  rw [pow_two, mul_div_assoc]

theorem Jb_mul_tsum_cos (r : ℕ) (hr : 2 ≤ r) (t : ℝ) :
    VietorisAux.Jb r 0 * (∑' k : ℕ, VietorisAux.ak r k * Real.cos ((k : ℝ) * t))
      = ∫ x in Set.Ioo (0 : ℝ) 1, VietorisAux.Gt t x * VietorisAux.Wt r 0 x := by
  have hS := VietorisAux.integral_tsum_Fn r t hr
  rw [VietorisAux.integral_tsum_Fn_eq r t] at hS
  have hterms : ∀ k : ℕ, ∫ x in Set.Ioo (0 : ℝ) 1, VietorisAux.Fn r t k x
      = VietorisAux.Jb r 0 * (VietorisAux.ak r k * Real.cos ((k : ℝ) * t)) := by
    intro k
    rw [VietorisAux.integral_Fn, VietorisAux.Jb_ratio r k, VietorisAux.ak_eq]
    field_simp
  rw [funext hterms] at hS
  rw [← hS.tsum_eq, tsum_mul_left]

/-- **The Beta-integral representation** of the boundary cosine series. -/
theorem ErCos_eq_integral (r : ℕ) (hr : 2 ≤ r) (t : ℝ) :
    ErCos r t = Cr r / VietorisAux.Jb r 0 *
      ∫ x in Set.Ioo (0 : ℝ) 1, VietorisAux.Gt t x * VietorisAux.Wt r 0 x := by
  have h1 : ErCos r t = Cr r * (∑' k : ℕ, VietorisAux.ak r k * Real.cos ((k : ℝ) * t)) := by
    unfold ErCos
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [ErCoeff_eq_Cr_mul_akV]
    ring
  have h2 := Jb_mul_tsum_cos r hr t
  have hJ : VietorisAux.Jb r 0 ≠ 0 := (VietorisAux.Jb_pos r 0).ne'
  rw [h1, ← h2]
  field_simp
  congr 1
  exact tsum_congr fun k => by rw [mul_comm ((k : ℝ)) t]

/-! ### The pointwise monotonicity of `Gt` in `t` -/

/-- `Gt(t,x)² = ((ρ+1)² - x²)/(4ρ²)` where `ρ = |1 - x e^{it}|`. -/
theorem Gt_sq_eq (t x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ht0 : 0 < t) (ht1 : t < Real.pi) :
    VietorisAux.Gt t x ^ 2
      = ((Real.sqrt (1 - 2 * x * Real.cos t + x ^ 2) + 1) ^ 2 - x ^ 2)
          / (4 * (Real.sqrt (1 - 2 * x * Real.cos t + x ^ 2)) ^ 2) := by
  set z : ℂ := 1 - (x : ℂ) * Complex.exp (t * Complex.I) with hzdef
  have hzre : z.re = 1 - x * Real.cos t := by
    rw [hzdef, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul,
      sub_zero]
  have hzim : z.im = -(x * Real.sin t) := by
    rw [hzdef, Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      zero_mul, add_zero]
    ring
  have hzns : Complex.normSq z = 1 - 2 * x * Real.cos t + x ^ 2 := by
    rw [Complex.normSq_apply, hzre, hzim]
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hzpos : 0 < z.re := by
    rw [hzdef]
    exact VietorisAux.re_one_sub_mul_exp_pos x hx0 hx1 ht0 ht1
  have hz : z ≠ 0 := by
    intro h
    rw [h] at hzpos
    simp at hzpos
  have hcpow : z ^ (1/2 : ℂ) * z ^ (1/2 : ℂ) = z := by
    rw [← Complex.cpow_add (1/2 : ℂ) (1/2 : ℂ) hz]
    norm_num
  have hGt : VietorisAux.Gt t x = (z ^ (1/2 : ℂ))⁻¹.re := by
    rw [VietorisAux.Gt, hzdef, one_div]
  have hsre : (z ^ (1/2 : ℂ)).re = Real.sqrt ((‖z‖ + z.re) / 2) := by
    rw [show (1/2 : ℂ) = 2⁻¹ by norm_num]
    exact Complex.cpow_inv_two_re z
  have hcpow2 : (z ^ (1/2 : ℂ)) ^ 2 = z := by
    rw [pow_two]
    exact hcpow
  have hsns : Complex.normSq (z ^ (1/2 : ℂ)) = ‖z‖ := by
    rw [show Complex.normSq (z ^ (1/2 : ℂ)) = ‖z ^ (1/2 : ℂ)‖ ^ 2 from
        Complex.normSq_eq_norm_sq _,
      ← norm_pow, hcpow2]
  have hval : VietorisAux.Gt t x = Real.sqrt ((‖z‖ + z.re) / 2) / ‖z‖ := by
    rw [hGt, Complex.inv_re, hsns, hsre]
  have hρns : ‖z‖ = Real.sqrt (1 - 2 * x * Real.cos t + x ^ 2) := by
    rw [Complex.norm_def, hzns]
  rw [hval, hρns, hzre]
  set ρ : ℝ := Real.sqrt (1 - 2 * x * Real.cos t + x ^ 2) with hρdef
  have hρ2 : ρ ^ 2 = 1 - 2 * x * Real.cos t + x ^ 2 := by
    rw [hρdef, Real.sq_sqrt]
    nlinarith [Real.sin_sq_add_cos_sq t, sq_nonneg (1 - x * Real.cos t), sq_nonneg (x * Real.sin t)]
  have hρpos : 0 < ρ := by
    rw [hρdef, Real.sqrt_pos]
    rcases eq_or_lt_of_le hx0 with h | h
    · rw [← h]; norm_num
    · have hc1 : Real.cos t < 1 := by
        have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0:ℝ)) ht1.le ht0
        simpa using this
      nlinarith [mul_lt_mul_of_pos_left hc1 h, sq_nonneg (1 - x)]
  have hxc : 1 - x * Real.cos t = (ρ ^ 2 + 1 - x ^ 2) / 2 := by
    rw [hρ2]; ring
  have harg : (0:ℝ) ≤ (ρ + (1 - x * Real.cos t)) / 2 := by
    have h1 : x * Real.cos t ≤ 1 := by
      nlinarith [Real.cos_le_one t, hx0, hx1]
    linarith [hρpos.le, h1]
  rw [div_pow, Real.sq_sqrt harg, hxc]
  field_simp
  ring

/-- `Φ(ρ) = ((ρ+1)²-x²)/(4ρ²)` is antitone in `ρ` for `x² ≤ 1`. -/
theorem Phi_anti {x ρ1 ρ2 : ℝ} (hx : x ^ 2 ≤ 1) (h1 : 0 < ρ1) (h12 : ρ1 ≤ ρ2) :
    ((ρ2 + 1) ^ 2 - x ^ 2) / (4 * ρ2 ^ 2) ≤ ((ρ1 + 1) ^ 2 - x ^ 2) / (4 * ρ1 ^ 2) := by
  have h2 : 0 < ρ2 := lt_of_lt_of_le h1 h12
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * ρ1 ^ 2), div_mul_eq_mul_div,
    div_le_iff₀ (by positivity : (0:ℝ) < 4 * ρ2 ^ 2)]
  have key : ((ρ1 + 1) ^ 2 - x ^ 2) * ρ2 ^ 2 - ((ρ2 + 1) ^ 2 - x ^ 2) * ρ1 ^ 2
      = (ρ2 - ρ1) * (2 * ρ1 * ρ2 + (1 - x ^ 2) * (ρ1 + ρ2)) := by ring
  have hnonneg : 0 ≤ (ρ2 - ρ1) * (2 * ρ1 * ρ2 + (1 - x ^ 2) * (ρ1 + ρ2)) := by
    refine mul_nonneg (sub_nonneg.mpr h12) ?_
    have h3 := mul_nonneg (sub_nonneg.mpr hx) (add_nonneg h1.le h2.le)
    nlinarith [mul_nonneg h1.le h2.le]
  nlinarith [key, hnonneg]

/-- **`Gt` is antitone in `t` on `(0, π)`**. -/
theorem Gt_anti {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {t1 t2 : ℝ}
    (ht1 : 0 < t1) (h12 : t1 ≤ t2) (ht2 : t2 < Real.pi) :
    VietorisAux.Gt t2 x ≤ VietorisAux.Gt t1 x := by
  have ht2pos : 0 < t2 := lt_of_lt_of_le ht1 h12
  have ht1' : t1 < Real.pi := lt_of_le_of_lt h12 ht2
  have hρ1 : 0 < Real.sqrt (1 - 2 * x * Real.cos t1 + x ^ 2) := by
    rw [Real.sqrt_pos]
    rcases eq_or_lt_of_le hx0 with h | h
    · rw [← h]; norm_num
    · have hc1 : Real.cos t1 < 1 := by
        have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0:ℝ)) ht1'.le ht1
        simpa using this
      nlinarith [mul_lt_mul_of_pos_left hc1 h, sq_nonneg (1 - x)]
  have hρle : Real.sqrt (1 - 2 * x * Real.cos t1 + x ^ 2)
      ≤ Real.sqrt (1 - 2 * x * Real.cos t2 + x ^ 2) := by
    refine Real.sqrt_le_sqrt ?_
    have hcos : Real.cos t2 ≤ Real.cos t1 :=
      Real.cos_le_cos_of_nonneg_of_le_pi ht1.le ht2.le h12
    nlinarith [hcos, hx0]
  have hsq : VietorisAux.Gt t2 x ^ 2 ≤ VietorisAux.Gt t1 x ^ 2 := by
    rw [Gt_sq_eq t2 x hx0 hx1 ht2pos ht2, Gt_sq_eq t1 x hx0 hx1 ht1 ht1']
    exact Phi_anti (by nlinarith) hρ1 hρle
  have hg1 : 0 ≤ VietorisAux.Gt t1 x :=
    (VietorisAux.Gt_pos ht1 ht1' x ⟨hx0, hx1⟩).le
  have hg2 : 0 ≤ VietorisAux.Gt t2 x :=
    (VietorisAux.Gt_pos ht2pos ht2 x ⟨hx0, hx1⟩).le
  nlinarith [hsq, hg1, hg2, sq_nonneg (VietorisAux.Gt t2 x - VietorisAux.Gt t1 x)]

/-! ### Monotonicity and positivity of `R_r` on `(0, π)` -/

theorem ErCos_antitone {r : ℕ} (hr : 2 ≤ r) {t1 t2 : ℝ}
    (ht1 : 0 < t1) (h12 : t1 ≤ t2) (ht2 : t2 < Real.pi) :
    ErCos r t2 ≤ ErCos r t1 := by
  have ht2pos : 0 < t2 := lt_of_lt_of_le ht1 h12
  have ht1' : t1 < Real.pi := lt_of_le_of_lt h12 ht2
  rw [ErCos_eq_integral r hr t2, ErCos_eq_integral r hr t1]
  have hcoef : 0 ≤ Cr r / VietorisAux.Jb r 0 :=
    div_nonneg (Cr_pos (by linarith : 1 ≤ r)).le (VietorisAux.Jb_pos r 0).le
  refine mul_le_mul_of_nonneg_left ?_ hcoef
  refine MeasureTheory.integral_mono_ae
    (VietorisAux.integrable_Gt_Wt r t2 hr ht2pos ht2)
    (VietorisAux.integrable_Gt_Wt r t1 hr ht1 ht1') ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact mul_le_mul_of_nonneg_right (Gt_anti hx.1.le hx.2.le ht1 h12 ht2)
    (VietorisAux.Wt_nonneg r 0 hx)

theorem ErCos_pos {r : ℕ} (hr : 2 ≤ r) {t : ℝ} (ht0 : 0 < t) (ht1 : t < Real.pi) :
    0 < ErCos r t := by
  rw [ErCos_eq_integral r hr t]
  exact mul_pos (div_pos (Cr_pos (by linarith : 1 ≤ r)) (VietorisAux.Jb_pos r 0))
    (VietorisAux.integral_Gt_Wt_pos r t hr ht0 ht1)

/-- **Lemma 3.5**: `c_r = |E_r(i)|` for `r ≥ 2`. -/
theorem cr_eq_norm_er_I (r : ℕ) (hr : 2 ≤ r) : cr r = ‖ErComplex r Complex.I‖ := by
  refine cr_eq_norm_I_of_mono r hr (fun x hx0 hx1 => ?_) (ErCos_pi_nonneg r hr ?_)
  · have htend : Tendsto (ErCos r) (𝓝[<] Real.pi) (𝓝 (ErCos r Real.pi)) :=
      (continuous_ErCos r hr).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto htend tendsto_const_nhds ?_
    filter_upwards [Ioo_mem_nhdsLT hx1] with t ht
    exact ErCos_antitone hr hx0 ht.1.le ht.2
  · intro t ht0 ht1
    exact ErCos_pos hr ht0 ht1

end Grothendieck

open Grothendieck in
theorem solution (r : ℕ) (hr : 2 ≤ r) :
    DifferentiableOn ℂ (ErComplex r) (Metric.ball (0 : ℂ) 1) ∧
      ∀ z : ℂ, ‖z‖ < 1 →
        HasDerivAt (ErComplex r)
          (∑' k : ℕ, (ErCoeff r k : ℂ) * (((2 * k + 1 : ℕ) : ℂ) * z ^ (2 * k))) z :=
  ⟨Grothendieck.differentiableOn_ErComplex r hr,
   fun z hz => Grothendieck.hasDerivAt_ErComplex r hr hz⟩
