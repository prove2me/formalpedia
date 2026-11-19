-- Prove2me | solution 1 for HermiteLaptop.MaxAgree.five_spoke_degree20_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-18T15:20:55.608901+00:00
-- url     : https://prove2.me/submissions/0ce2ebc5-35a9-4820-bdb5-ab22e040028d

import Definitions.Def_HermiteLaptop_MaxAgree_OneDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic
import Definitions.Def_HermiteLaptop_MaxAgree_Hermite

set_option autoImplicit false

/- Basic.lean -/
section
open MeasureTheory ProbabilityTheory Set
namespace HermiteLaptop.MaxAgree

theorem moment_phi_formula (x : ℝ) :
    phi x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x^2)/2) := by
  simp [phi, gaussianPDFReal]

theorem moment_phi_deriv (x : ℝ) : HasDerivAt phi (-x * phi x) x := by
  have h := (((((hasDerivAt_id x).pow 2).neg.div_const 2).exp).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹)
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at h
  rw [show phi = fun y => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y^2)/2) from
    funext moment_phi_formula]
  apply h.congr_deriv
  change _ * (Real.exp (-(x^2)/2) * (-(2*x)/2)) = -x * (_ * Real.exp (-(x^2)/2))
  ring

theorem moment_phi_nonneg (x : ℝ) : 0 ≤ phi x := gaussianPDFReal_nonneg _ _ _
theorem moment_phi_le_one (x : ℝ) : phi x ≤ 1 := by
  rw [moment_phi_formula]
  have h : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [Real.pi_gt_three]
  exact mul_le_one₀ (inv_le_one_of_one_le₀ h) (Real.exp_nonneg _)
    (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))

theorem moment_Phi_nonneg (x : ℝ) : 0 ≤ Phi x := cdf_nonneg _ _
theorem moment_Phi_le_one (x : ℝ) : Phi x ≤ 1 := cdf_le_one _ _

theorem moment_phi_integrable : Integrable phi := integrable_gaussianPDFReal _ _
theorem moment_phi_integral : (∫ x : ℝ, phi x) = 1 :=
  integral_gaussianPDFReal_eq_one _ one_ne_zero

theorem moment_Phi_integral (x : ℝ) : Phi x = ∫ y in Iic x, phi y := by
  rw [Phi, cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal]
  · rfl
  · exact integral_nonneg_of_ae (ae_of_all _ (gaussianPDFReal_nonneg 0 1))

theorem moment_Phi_deriv (x : ℝ) : HasDerivAt Phi (phi x) x := by
  have hc : Continuous phi := continuous_iff_continuousAt.mpr fun z => (moment_phi_deriv z).continuousAt
  have he : Phi = fun u => Phi 0 + ∫ z in (0 : ℝ)..u, phi z := by
    funext u
    rw [moment_Phi_integral u, moment_Phi_integral 0, ← intervalIntegral.integral_Iic_sub_Iic
      moment_phi_integrable.integrableOn moment_phi_integrable.integrableOn]
    ring
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable ..)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _

theorem moment_phi_neg (x : ℝ) : phi (-x) = phi x := by simp [moment_phi_formula]

theorem moment_Phi_neg (x : ℝ) : Phi (-x) = 1 - Phi x := by
  have h := integral_comp_neg_Iic (-x) phi
  simp only [moment_phi_neg, neg_neg] at h
  have h' := intervalIntegral.integral_Iic_add_Ioi
    (b := x) moment_phi_integrable.integrableOn moment_phi_integrable.integrableOn
  rw [moment_phi_integral, ← h] at h'
  rw [moment_Phi_integral, moment_Phi_integral]
  linarith

theorem moment_Phi_zero : Phi 0 = 1/2 := by
  have h := moment_Phi_neg 0
  rw [neg_zero] at h
  linarith

end HermiteLaptop.MaxAgree
end

/- Recurrence.lean -/
section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace HermiteLaptop.MaxAgree

noncomputable def hermiteMoment (d s j : ℕ) : ℝ :=
  ∫ x : ℝ, x ^ j * phi x ^ d * Phi x ^ s

theorem hermiteMoment_integrable (d s j : ℕ) (hd : 0 < d) :
    Integrable (fun x : ℝ => x ^ j * phi x ^ d * Phi x ^ s) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  have hG := integrable_rpow_mul_exp_neg_mul_sq (b := (1:ℝ)/2) (s := (j:ℝ))
    (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) j])
  have hbase : Integrable (fun x : ℝ => x ^ j * phi x) := by
    convert (hG.const_mul (Real.sqrt (2 * Real.pi))⁻¹) using 1
    ext x
    simp only [moment_phi_formula, Real.rpow_natCast]
    ring_nf
  have c₁ : Continuous phi := continuous_iff_continuousAt.mpr
    (fun x => (moment_phi_deriv x).continuousAt)
  have c₂ : Continuous Phi := continuous_iff_continuousAt.mpr
    (fun x => (moment_Phi_deriv x).continuousAt)
  have hmul := hbase.mul_bdd (c := 1)
    ((c₁.pow d).mul (c₂.pow s)).aestronglyMeasurable
    (ae_of_all _ (fun x => by
      change ‖phi x ^ d * Phi x ^ s‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (moment_phi_nonneg _) _)
        (pow_nonneg (moment_Phi_nonneg _) _))]
      exact mul_le_one₀ (pow_le_one₀ (moment_phi_nonneg _) (moment_phi_le_one _))
        (pow_nonneg (moment_Phi_nonneg _) _) (pow_le_one₀ (moment_Phi_nonneg _) (moment_Phi_le_one _))))
  convert hmul using 1
  ext x
  simp only [pow_succ, Pi.mul_apply, Pi.pow_apply]
  ring

theorem hermiteMoment_recurrence (d s j : ℕ) (hd : 0 < d) :
    (d : ℝ) * hermiteMoment d s (j+1) =
    (j : ℝ) * hermiteMoment d s (j-1) + (s : ℝ) * hermiteMoment (d+1) (s-1) j := by
  let F (d s j : ℕ) (x : ℝ) := x ^ j * phi x ^ d * Phi x ^ s
  have hI (a b c : ℕ) (ha : 0 < a) : Integrable (F a b c) :=
    hermiteMoment_integrable a b c ha
  have h1 := (hI d s (j-1) hd).const_mul (j : ℝ)
  have h2 := (hI d s (j+1) hd).const_mul (d : ℝ)
  have h3 := (hI (d+1) (s-1) j (by omega)).const_mul (s : ℝ)
  have hderiv (x : ℝ) : HasDerivAt (F d s j)
      ((j : ℝ) * F d s (j-1) x - (d : ℝ) * F d s (j+1) x +
        (s : ℝ) * F (d+1) (s-1) j x) x := by
    have h := (((hasDerivAt_pow j x).mul ((moment_phi_deriv x).pow d)).mul
      ((moment_Phi_deriv x).pow s))
    apply h.congr_deriv
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    simp only [F, Pi.mul_apply, Pi.pow_apply, Nat.succ_sub_one, pow_succ, Nat.cast_succ]
    ring
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv
    ((h1.sub h2).add h3) (hI d s j hd)
  have h12 : Integrable (fun x => (j : ℝ) * F d s (j-1) x - (d : ℝ) * F d s (j+1) x) :=
    h1.sub h2
  rw [integral_add h12 h3, integral_sub h1 h2] at hzero
  simp only [integral_const_mul] at hzero
  change (j : ℝ) * hermiteMoment d s (j-1) - (d : ℝ) * hermiteMoment d s (j+1) +
    (s : ℝ) * hermiteMoment (d+1) (s-1) j = 0 at hzero
  linarith

/-- The probability integral transform gives every zeroth moment with one density factor. -/
theorem hermiteMoment_one_zero (s : ℕ) :
    hermiteMoment 1 s 0 = 1 / ((s:ℝ)+1) := by
  have hI : Integrable (fun x : ℝ => phi x * Phi x ^ s) := by
    simpa using hermiteMoment_integrable 1 s 0 (by decide)
  have hd (x : ℝ) : HasDerivAt (fun y => Phi y ^ (s+1))
      (((s : ℝ) + 1) * (phi x * Phi x ^ s)) x := by
    apply ((moment_Phi_deriv x).pow (s+1)).congr_deriv
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    ring
  have hb : Tendsto Phi atBot (𝓝 0) := tendsto_cdf_atBot _
  have ht : Tendsto Phi atTop (𝓝 1) := tendsto_cdf_atTop _
  have h := integral_of_hasDerivAt_of_tendsto hd (hI.const_mul ((s:ℝ)+1))
    (hb.pow (s+1)) (ht.pow (s+1))
  rw [integral_const_mul] at h
  simp only [one_pow, zero_pow (Nat.succ_ne_zero s), sub_zero] at h
  simp only [hermiteMoment, pow_zero, pow_one, one_mul]
  apply (eq_div_iff (by positivity : (s:ℝ)+1 ≠ 0)).mpr
  simpa only [mul_comm] using h

end HermiteLaptop.MaxAgree
end

/- Integrals.lean -/
section
open MeasureTheory

namespace HermiteLaptop.MaxAgree

/-- Separate the polynomial and Gaussian factors in the mission's coefficient integrand. -/
theorem integrandB_moment_factor (a : ℕ) (lam : Multiset ℕ) (x : ℝ) :
    integrandB a lam x = (-1 : ℝ) ^ rCount lam * (Spoly a lam).eval x *
      phi x ^ (rCount lam + 1) * Phi x ^ sCount lam := by
  induction lam using Multiset.induction_on with
  | empty => simp [integrandB, rCount, sCount, Spoly, H, mul_comm]
  | cons b lam ih =>
    cases b with
    | zero =>
      simp [integrandB, rCount, sCount, Spoly, Kfun, H, pow_succ] at ih ⊢
      linear_combination Phi x * ih
    | succ b =>
      simp [integrandB, rCount, sCount, Spoly, Kfun, H, pow_succ] at ih ⊢
      linear_combination (phi x * (Hpoly b).eval x) * ih

/-- Integrate a polynomial with the same Gaussian weights as the monomial moments. -/
theorem integral_polynomial_eq_hermiteMoment (P : Polynomial ℝ) (d s : ℕ) (hd : 0 < d) :
    (∫ x : ℝ, P.eval x * phi x ^ d * Phi x ^ s) =
      ∑ j ∈ P.support, P.coeff j * hermiteMoment d s j := by
  have he (x : ℝ) : P.eval x * phi x ^ d * Phi x ^ s =
      ∑ j ∈ P.support, P.coeff j * (x ^ j * phi x ^ d * Phi x ^ s) := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    simp only [Finset.sum_mul, mul_assoc]
  simp_rw [he]
  rw [integral_finsetSum P.support (fun j _ => (hermiteMoment_integrable d s j hd).const_mul
    (P.coeff j))]
  simp only [integral_const_mul, hermiteMoment]

/-- The mission's coefficient integral is a finite signed combination of Gaussian moments. -/
theorem bal_eq_hermiteMoments (a : ℕ) (lam : Multiset ℕ) :
    Bal a lam = (-1 : ℝ) ^ rCount lam * ∑ j ∈ (Spoly a lam).support,
      (Spoly a lam).coeff j * hermiteMoment (rCount lam + 1) (sCount lam) j := by
  unfold Bal
  simp_rw [integrandB_moment_factor, mul_assoc]
  rw [integral_const_mul]
  congr 1
  simpa only [mul_assoc] using
    integral_polynomial_eq_hermiteMoment (Spoly a lam) (rCount lam + 1) (sCount lam) (by omega)

end HermiteLaptop.MaxAgree
end

/- Dense.lean -/
section
open MeasureTheory Polynomial
namespace HermiteLaptop.MaxAgree

/-- Dense integer polynomials, in ascending order of degree. Missing terms are zero. -/
noncomputable def densePoly : List ℤ → Polynomial ℝ
  | [] => 0
  | c :: v => C (c : ℝ) + X * densePoly v

def denseAdd : List ℤ → List ℤ → List ℤ
  | [], w => w
  | v, [] => v
  | a :: v, b :: w => (a+b) :: denseAdd v w

def denseMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: v, w => denseAdd (w.map (a * ·)) (0 :: denseMul v w)

private theorem densePoly_add (v w : List ℤ) :
    densePoly (denseAdd v w) = densePoly v + densePoly w := by
  induction v generalizing w with
  | nil => simp [denseAdd, densePoly]
  | cons a v ih =>
    cases w with
    | nil => simp [denseAdd, densePoly]
    | cons b w => simp [denseAdd, densePoly, ih]; ring

private theorem densePoly_scale (v : List ℤ) (a : ℤ) :
    densePoly (v.map (a * ·)) = C (a : ℝ) * densePoly v := by
  induction v with
  | nil => simp [densePoly]
  | cons b v ih => simp [densePoly, ih]; ring

theorem densePoly_mul (v w : List ℤ) :
    densePoly (denseMul v w) = densePoly v * densePoly w := by
  induction v with
  | nil => simp [denseMul, densePoly]
  | cons a v ih => simp [denseMul, densePoly_add, densePoly_scale, densePoly, ih]; ring

private def weightedCoefficients : List ℤ → ℕ → List ℤ
  | [], _ => []
  | a :: v, j => ((j : ℤ)*a) :: weightedCoefficients v (j+1)

private theorem densePoly_weight (v : List ℤ) (j : ℕ) :
    densePoly (weightedCoefficients v j) = C (j:ℝ) * densePoly v + X * (densePoly v).derivative := by
  induction v generalizing j with
  | nil => simp [weightedCoefficients, densePoly]
  | cons a v ih => simp [weightedCoefficients, densePoly, ih, derivative_mul]; ring

private def denseDerivative (v : List ℤ) := weightedCoefficients v.tail 1

private theorem densePoly_derivative (v : List ℤ) :
    densePoly (denseDerivative v) = (densePoly v).derivative := by
  cases v with
  | nil => simp [denseDerivative, weightedCoefficients, densePoly]
  | cons a v => simp [denseDerivative, densePoly_weight, densePoly, derivative_mul]

/-- The probabilists' Hermite polynomials from H₀=1 and Hₙ₊₁=XHₙ−Hₙ′. -/
def denseHermite : ℕ → List ℤ
  | 0 => [1]
  | n+1 => let h := denseHermite n
           denseAdd (0 :: h) ((denseDerivative h).map ((-1 : ℤ) * ·))

theorem densePoly_hermite (n : ℕ) : densePoly (denseHermite n) = Hpoly n := by
  induction n with
  | zero => simp [denseHermite, densePoly, Hpoly]
  | succ n ih =>
    rw [denseHermite, densePoly_add, densePoly_scale, densePoly_derivative]
    simp [densePoly, ih, Hpoly, hermite_succ, derivative_map, sub_eq_add_neg]

private def denseTailPoly : List ℕ → List ℤ
  | [] => [1]
  | 0 :: tail => denseTailPoly tail
  | (b+1) :: tail => denseMul (denseHermite b) (denseTailPoly tail)

/-- Polynomial factor in a sorted or unsorted coordinate multi-index. -/
def denseSpoly (a : ℕ) (tail : List ℕ) : List ℤ :=
  denseMul (denseHermite a) (denseTailPoly tail)

theorem densePoly_spoly (a : ℕ) (tail : List ℕ) :
    densePoly (denseSpoly a tail) = Spoly a (tail : Multiset ℕ) := by
  rw [denseSpoly, densePoly_mul, densePoly_hermite, Spoly]
  congr 1
  induction tail with
  | nil => simp [denseTailPoly, densePoly]
  | cons b tail ih =>
    cases b <;> simp [denseTailPoly, densePoly_mul, densePoly_hermite, ih]

/-- Starting at monomial degree j, pair a dense coefficient list with the Gaussian moments. -/
noncomputable def denseMomentDot : List ℤ → ℕ → ℕ → ℕ → ℝ
  | [], _, _, _ => 0
  | c :: v, d, s, j => (c : ℝ)*hermiteMoment d s j + denseMomentDot v d s (j+1)

theorem integral_denseMomentDot (v : List ℤ) (d s j : ℕ) (hd : 0 < d) :
    (∫ x : ℝ, x^j * phi x^d * Phi x^s * (densePoly v).eval x) = denseMomentDot v d s j := by
  let G (v : List ℤ) (j : ℕ) := fun x : ℝ => x^j * phi x^d * Phi x^s * (densePoly v).eval x
  have h (v : List ℤ) (j : ℕ) : Integrable (G v j) ∧
      (∫ x : ℝ, G v j x) = denseMomentDot v d s j := by
    induction v generalizing j with
    | nil =>
      simp [G, densePoly, denseMomentDot]
    | cons c v ih =>
      have eq : G (c :: v) j = fun x : ℝ => (c : ℝ)*(x^j * phi x^d * Phi x^s) + G v (j+1) x := by
        funext x
        simp [G, densePoly, pow_succ]
        ring
      have h1 := (hermiteMoment_integrable d s j hd).const_mul (c : ℝ)
      have h2 := ih (j+1)
      rw [eq]
      refine ⟨h1.add h2.1, ?_⟩
      rw [integral_add h1 h2.1, integral_const_mul, h2.2]
      rfl
  exact (h v j).2

/-- Compute every signed coefficient integral with integer Hermite polynomials and scalar moments. -/
theorem bal_eq_denseMomentDot (a : ℕ) (tail : List ℕ) :
    Bal a (tail : Multiset ℕ) = (-1 : ℝ) ^ rCount (tail : Multiset ℕ) *
      denseMomentDot (denseSpoly a tail) (rCount (tail : Multiset ℕ)+1)
        (sCount (tail : Multiset ℕ)) 0 := by
  rw [← integral_denseMomentDot _ _ _ _ (Nat.succ_pos _), Bal, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [integrandB_moment_factor, densePoly_spoly]
  simp only [Nat.succ_eq_add_one, pow_succ, pow_zero, one_mul]
  ring

end HermiteLaptop.MaxAgree
end

/- TermArithmetic.lean -/
section
namespace HermiteLaptop.MaxAgree

/-- Fixed point interval for a dot product with signed integer coefficients. -/
def denseBand (b : ℕ → ℤ × ℤ) : List ℤ → ℕ → ℤ × ℤ
  | [], _ => (0, 0)
  | c :: cs, j =>
    let rest := denseBand b cs (j+1)
    let (l,u) := b j
    if 0 ≤ c then (c*l + rest.1, c*u + rest.2)
    else (c*u + rest.1, c*l + rest.2)

def bandDot (x : ℕ → ℝ) : List ℤ → ℕ → ℝ
  | [], _ => 0
  | c :: cs, j => (c : ℝ) * x j + bandDot x cs (j+1)

theorem denseBand_sound {x : ℕ → ℝ} {b : ℕ → ℤ × ℤ} (cs : List ℤ) (j : ℕ)
    (h : ∀ i, j ≤ i → i < j+cs.length →
      ((b i).1 : ℝ) ≤ 100000000000000 * x i ∧ 100000000000000 * x i ≤ ((b i).2 : ℝ)) :
    ((denseBand b cs j).1 : ℝ) ≤ 100000000000000 * bandDot x cs j ∧
      100000000000000 * bandDot x cs j ≤ ((denseBand b cs j).2 : ℝ) := by
  induction cs generalizing j with
  | nil => simp [bandDot, denseBand]
  | cons c cs ih =>
    have h0 := h j le_rfl (by simp)
    have ht := ih (j+1) (fun i hi hu => h i (by omega) (by simp only [List.length_cons]; omega))
    by_cases hc : 0 ≤ c
    · simp only [denseBand, hc, if_true, Int.cast_add, Int.cast_mul, bandDot]
      have hc' : 0 ≤ (c:ℝ) := by exact_mod_cast hc
      constructor
      · linarith only [add_le_add (mul_le_mul_of_nonneg_left h0.1 hc') ht.1]
      · linarith only [add_le_add (mul_le_mul_of_nonneg_left h0.2 hc') ht.2]
    · simp only [denseBand, hc, if_false, Int.cast_add, Int.cast_mul, bandDot]
      have hc' : (c:ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hc)
      constructor
      · linarith only [add_le_add (mul_le_mul_of_nonpos_left h0.2 hc') ht.1]
      · linarith only [add_le_add (mul_le_mul_of_nonpos_left h0.1 hc') ht.2]

/-- Distance from zero to a fixed point interval, with zero for an interval crossing zero. -/
def bandDistance (v : ℤ × ℤ) : ℕ := (max v.1 (-v.2)).toNat

theorem bandDistance_le {b : ℤ × ℤ} {x : ℝ}
    (h : (b.1 : ℝ) ≤ x ∧ x ≤ (b.2 : ℝ)) : (bandDistance b : ℝ) ≤ |x| := by
  unfold bandDistance
  have hh : ((max b.1 (-b.2) : ℤ) : ℝ) ≤ |x| := by
    rw [Int.cast_max, Int.cast_neg]
    exact max_le (h.1.trans (le_abs_self _)) ((neg_le_neg h.2).trans (neg_le_abs _))
  rw [← Int.cast_natCast (R := ℝ), Int.toNat_eq_max, Int.cast_max, Int.cast_zero]
  exact max_le hh (abs_nonneg _)

/-- Integer factors in the weight of a multiset. -/
def multiplicityDen (xs : List ℕ) : ℕ :=
  ∏ i ∈ xs.toFinset, (xs.count i).factorial

def factorialDen (a : ℕ) (xs : List ℕ) : ℕ := a.factorial * (xs.map Nat.factorial).prod

theorem factorialDen_eq (a : ℕ) (xs : List ℕ) :
    (factorialDen a xs : ℝ) = factDen a (xs : Multiset ℕ) := by
  simp [factorialDen, factDen, Nat.cast_list_prod, List.map_map, Function.comp_def]

theorem multiplicityDen_eq (xs : List ℕ) :
    Nmult (xs : Multiset ℕ) = (xs.length.factorial : ℝ) / (multiplicityDen xs : ℝ) := by
  simp [Nmult, multiplicityDen]

theorem factorialDen_pos (a : ℕ) (xs : List ℕ) : 0 < factorialDen a xs := by
  unfold factorialDen
  apply Nat.mul_pos (Nat.factorial_pos _)
  exact List.prod_pos (by simpa using fun i (_ : i ∈ xs) => Nat.factorial_pos i)

theorem multiplicityDen_pos (xs : List ℕ) : 0 < multiplicityDen xs := by
  unfold multiplicityDen
  exact Finset.prod_pos fun i _ => Nat.factorial_pos _

def weightedTerm (k a : ℕ) (xs : List ℕ) (z : ℕ) : ℕ :=
  k * xs.length.factorial * z^2 / (100000000 * multiplicityDen xs * factorialDen a xs)

theorem weightedTerm_le (k a : ℕ) (xs : List ℕ) (z : ℕ) {v : ℝ}
    (hz : (z : ℝ) ≤ |100000000000000 * v|) :
    (weightedTerm k a xs z : ℝ) / 10^20 ≤
      (k : ℝ) * Nmult (xs : Multiset ℕ) * v^2 / factDen a (xs : Multiset ℕ) := by
  have h := Nat.div_mul_le_self (k * xs.length.factorial * z^2)
    (100000000 * multiplicityDen xs * factorialDen a xs)
  change weightedTerm k a xs z * _ ≤ _ at h
  have hr := (Nat.cast_le (α := ℝ)).mpr h
  push_cast at hr
  have hm : 0 < (multiplicityDen xs : ℝ) := by exact_mod_cast multiplicityDen_pos xs
  have hf : 0 < (factorialDen a xs : ℝ) := by exact_mod_cast factorialDen_pos a xs
  have hs := mul_self_le_mul_self (Nat.cast_nonneg z) hz
  rw [← sq, ← sq, sq_abs, mul_pow] at hs
  rw [multiplicityDen_eq, ← factorialDen_eq]
  field_simp [hm.ne', hf.ne']
  nlinarith only [hr, mul_le_mul_of_nonneg_left hs
    (mul_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg xs.length.factorial))]

end HermiteLaptop.MaxAgree
end

/- Parameter.lean -/
section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace HermiteLaptop.MaxAgree

/-- Differentiate the squared Gaussian CDF integral with respect to its scale. -/
theorem moment_scaled_quadrant_deriv (t : ℝ) :
    HasDerivAt (fun a : ℝ => ∫ x : ℝ, phi x * (Phi (a*x))^2)
      (∫ x : ℝ, 2*x*phi x*phi (t*x)*Phi (t*x)) t := by
  have hφ : Continuous phi := continuous_iff_continuousAt.mpr fun x =>
    (moment_phi_deriv x).continuousAt
  have hΦ : Continuous Phi := continuous_iff_continuousAt.mpr fun x =>
    (moment_Phi_deriv x).continuousAt
  have hm (a : ℝ) : Continuous (fun x : ℝ => phi x * (Phi (a*x))^2) :=
    hφ.mul ((hΦ.comp (continuous_const.mul continuous_id)).pow 2)
  have hmi : Integrable (fun x : ℝ => phi x * (Phi (t*x))^2) := by
    apply (integrable_gaussianPDFReal 0 1).mono' (hm t).aestronglyMeasurable
    apply ae_of_all
    intro x
    change ‖phi x * (Phi (t*x))^2‖ ≤ phi x
    rw [Real.norm_of_nonneg (mul_nonneg (moment_phi_nonneg _) (sq_nonneg _))]
    apply mul_le_of_le_one_right (moment_phi_nonneg _)
    exact pow_le_one₀ (moment_Phi_nonneg _) (moment_Phi_le_one _)
  have hb : Integrable (fun x : ℝ => 2 * |x| * phi x) := by
    have hg := ((integrable_mul_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)).norm).const_mul
      (2 * (Real.sqrt (2*Real.pi))⁻¹)
    refine hg.congr (ae_of_all _ fun x => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), moment_phi_formula]
    ring_nf
  have hbd (x a : ℝ) : ‖2*x*phi x*phi (a*x)*Phi (a*x)‖ ≤ 2 * |x| * phi x := by
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (moment_phi_nonneg _),
      abs_of_nonneg (moment_Phi_nonneg _), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hx := moment_phi_nonneg x
    have hax := moment_phi_nonneg (a*x)
    apply le_trans (mul_le_of_le_one_right (by positivity)
      (moment_Phi_le_one _))
    exact mul_le_of_le_one_right (by positivity) (moment_phi_le_one _)
  have hd (a x : ℝ) : HasDerivAt (fun b : ℝ => phi x * (Phi (b*x))^2)
      (2*x*phi x*phi (a*x)*Phi (a*x)) a := by
    convert (((moment_Phi_deriv (a*x)).comp a ((hasDerivAt_id a).mul_const x)).pow 2).const_mul
      (phi x) using 1 <;> try rfl
    change 2*x*phi x*phi (a*x)*Phi (a*x) =
      phi x * ((2:ℝ) * Phi (a*x)^1 * (phi (a*x)*(1*x)))
    ring
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (F := fun a x : ℝ => phi x * (Phi (a*x))^2)
    (F' := fun a x : ℝ => 2*x*phi x*phi (a*x)*Phi (a*x)) (bound := fun x : ℝ => 2 * |x| * phi x)
    (Filter.univ_mem) (.of_forall fun a => (hm a).aestronglyMeasurable) hmi ?_
    (ae_of_all _ fun x a _ => hbd x a) hb (ae_of_all _ fun x a _ => hd a x)).2
  exact (((((continuous_const.mul continuous_id).mul hφ).mul
    (hφ.comp (continuous_const.mul continuous_id))).mul
    (hΦ.comp (continuous_const.mul continuous_id)))).aestronglyMeasurable


end HermiteLaptop.MaxAgree
end

/- Inner.lean -/
section
open MeasureTheory ProbabilityTheory Filter Real
namespace HermiteLaptop.MaxAgree

/-- The product of three Gaussian densities reduces to a single Gaussian integral. -/
theorem inner_phi_triple_integral (t : ℝ) :
    (∫ x : ℝ, phi x * phi (t*x) * phi (t*x)) =
      1 / (2 * Real.pi * Real.sqrt (1+2*t^2)) := by
  have hpos : 0 < 1 + 2 * t^2 := by positivity
  have hpi : 0 < 2 * Real.pi := by positivity
  calc
    _ = ∫ x : ℝ, ((Real.sqrt (2*Real.pi))⁻¹)^3 *
        Real.exp (-((1+2*t^2)/2)*x^2) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [moment_phi_formula]
      rw [show -((1+2*t^2)/2)*x^2 = -(x^2)/2 + -((t*x)^2)/2 + -((t*x)^2)/2 by ring]
      rw [Real.exp_add, Real.exp_add]
      ring
    _ = _ := by
      rw [integral_const_mul, integral_gaussian,
        show Real.pi / ((1+2*t^2)/2) = (2*Real.pi)/(1+2*t^2) by rw [div_div_eq_mul_div]; ring,
        Real.sqrt_div hpi.le]
      have hsq := Real.sq_sqrt hpi.le
      have hs : Real.sqrt (2*Real.pi) ≠ 0 := (Real.sqrt_pos.2 hpi).ne'
      have ht : Real.sqrt (1+2*t^2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
      field_simp
      nlinarith only [hsq]

/-- Integration by parts evaluates the derivative integral of the scaled quadrant probability. -/
theorem inner_deriv_integral (t : ℝ) :
    (∫ x : ℝ, 2 * x * phi x * phi (t*x) * Phi (t*x)) =
      t / (Real.pi*(1+t^2)*Real.sqrt (1+2*t^2)) := by
  have hcoord (x : ℝ) : HasDerivAt (fun y : ℝ => t*y) t x := by
    simpa using (hasDerivAt_id x).const_mul t
  have hp (x : ℝ) :
      HasDerivAt (fun y => phi (t*y)) ((-(t*x)*phi (t*x))*t) x :=
    (moment_phi_deriv (t*x)).comp x (hcoord x)
  have hP (x : ℝ) : HasDerivAt (fun y => Phi (t*y)) (phi (t*x)*t) x :=
    (moment_Phi_deriv (t*x)).comp x (hcoord x)
  have hp_bdd : ∀ᵐ x : ℝ, ‖phi (t*x)‖ ≤ 1 :=
    Eventually.of_forall fun x => by simpa [Real.norm_of_nonneg (moment_phi_nonneg _)] using moment_phi_le_one (t*x)
  have hP_bdd : ∀ᵐ x : ℝ, ‖Phi (t*x)‖ ≤ 1 :=
    Eventually.of_forall fun x => by simpa [Real.norm_of_nonneg (moment_Phi_nonneg _)] using moment_Phi_le_one (t*x)
  have hp_m := (show Continuous (fun x : ℝ => phi (t*x)) from continuous_iff_continuousAt.mpr
      fun x => (hp x).continuousAt).aestronglyMeasurable (μ := volume)
  have hP_m := (show Continuous (fun x : ℝ => Phi (t*x)) from continuous_iff_continuousAt.mpr
      fun x => (hP x).continuousAt).aestronglyMeasurable (μ := volume)
  have hpair := moment_phi_integrable.mul_bdd hp_m hp_bdd
  have htriple := hpair.mul_bdd hp_m hp_bdd
  have hxphi : Integrable (fun x : ℝ => x * phi x) := by
    convert (integrable_mul_exp_neg_mul_sq (by norm_num : 0 < (1/2:ℝ))).const_mul
      (Real.sqrt (2*Real.pi))⁻¹ using 1
    ext x
    rw [moment_phi_formula]
    ring_nf
  have hxr := (((hxphi.mul_bdd hp_m hp_bdd).mul_bdd hP_m hP_bdd).const_mul (-(1+t^2)))
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => Phi (t*x)) (u' := fun x => phi (t*x)*t)
    (v := fun x : ℝ => phi x * phi (t*x))
    (v' := fun x => -(1+t^2) * (x * phi x * phi (t*x)))
    (fun x _ => hP x)
    (fun x _ => by convert (moment_phi_deriv x).mul (hp x) using 1 <;> first | rfl | ring)
    (by convert hxr using 1; ext x; dsimp; ring)
    (by convert htriple.const_mul t using 1; ext x; dsimp; ring)
    (by exact hpair.bdd_mul hP_m hP_bdd)
  have hrel : -(1+t^2) * (∫ x : ℝ, x * phi x * phi (t*x) * Phi (t*x)) =
      -(t * (∫ x : ℝ, phi x * phi (t*x) * phi (t*x))) := by
    simp_rw [← integral_const_mul]
    convert hibp using 1 <;> congr 1 <;> (congr 1; ext x; ring)
  rw [inner_phi_triple_integral] at hrel
  have hm : (∫ x : ℝ, 2 * x * phi x * phi (t*x) * Phi (t*x)) =
      2 * (∫ x : ℝ, x * phi x * phi (t*x) * Phi (t*x)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hm]
  have h1 : (1+t^2) ≠ 0 := by positivity
  have h2 : Real.sqrt (1+2*t^2) ≠ 0 := by positivity
  field_simp at hrel ⊢
  linarith

end HermiteLaptop.MaxAgree
end

/- QuadrantPrimitive.lean -/
section
namespace HermiteLaptop.MaxAgree

/-- Antiderivative for the variation of the squared Gaussian CDF under scaling. -/
theorem moment_quadrant_primitive (t : ℝ) :
    HasDerivAt (fun a : ℝ => (1 : ℝ)/4 +
      Real.arcsin (a^2/(1+a^2)) / (2*Real.pi))
      (t / (Real.pi * (1+t^2) * Real.sqrt (1+2*t^2))) t := by
  have h1 : 0 < 1+t^2 := by positivity
  have h2 : 0 < 1+2*t^2 := by positivity
  have ht : t^2 / (1+t^2) < 1 := (div_lt_one h1).2 (by linarith)
  have h0 : 0 ≤ t^2 / (1+t^2) := by positivity
  have hroot : Real.sqrt (1 - (t^2/(1+t^2))^2) = Real.sqrt (1+2*t^2)/(1+t^2) := by
    rw [show 1 - (t^2/(1+t^2))^2 = (1+2*t^2)/(1+t^2)^2 by field_simp; ring,
      Real.sqrt_div h2.le, Real.sqrt_sq h1.le]
  have h := (hasDerivAt_id t).pow 2
  have hq := h.div (h.const_add 1) h1.ne'
  have hd := (((Real.hasDerivAt_arcsin (by linarith : t^2/(1+t^2) ≠ -1) ht.ne).comp t hq).div_const
    (2*Real.pi)).const_add (1/4)
  apply hd.congr_deriv
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, hroot]
  field_simp [h1.ne', (Real.sqrt_pos.2 h2).ne', Real.pi_ne_zero]
  ring

end HermiteLaptop.MaxAgree
end

/- Quadrant.lean -/
section
open MeasureTheory Set

namespace HermiteLaptop.MaxAgree

/-- The square-CDF base integral, valid for every real scale. -/
theorem moment_scaled_quadrant (t : ℝ) :
    (∫ x : ℝ, phi x * (Phi (t*x))^2) =
      1/4 + Real.arcsin (t^2/(1+t^2))/(2*Real.pi) := by
  let F := fun a : ℝ => ∫ x : ℝ, phi x * (Phi (a*x))^2
  let G := fun a : ℝ => 1/4 + Real.arcsin (a^2/(1+a^2))/(2*Real.pi)
  let D := fun a : ℝ => a/(Real.pi*(1+a^2)*Real.sqrt (1+2*a^2))
  have hF (a : ℝ) : HasDerivAt F (D a) a := by
    simpa only [F, D, inner_deriv_integral] using moment_scaled_quadrant_deriv a
  have hG (a : ℝ) : HasDerivAt G (D a) a := moment_quadrant_primitive a
  have hzero : F 0 = G 0 := by
    simp [F, G, moment_Phi_zero, integral_mul_const, moment_phi_integral]
    norm_num
  apply isOpen_univ.eqOn_of_deriv_eq isPreconnected_univ
    (f := F) (g := G)
    (fun a _ => (hF a).differentiableAt.differentiableWithinAt)
    (fun a _ => (hG a).differentiableAt.differentiableWithinAt)
    (fun {a} _ => (hF a).deriv.trans (hG a).deriv.symm) (mem_univ 0) hzero (mem_univ t)

end HermiteLaptop.MaxAgree
end

/- Scaling.lean -/
section
open MeasureTheory
namespace HermiteLaptop.MaxAgree

/-- A power of the Gaussian density is a rescaled Gaussian density. -/
theorem moment_density_power_scale (n s : ℕ) :
    (∫ x : ℝ, phi x ^ (n+1) * Phi x ^ s) =
      ((Real.sqrt (2*Real.pi))⁻¹)^n / Real.sqrt ((n:ℝ)+1) *
        ∫ x : ℝ, phi x * (Phi ((Real.sqrt ((n:ℝ)+1))⁻¹*x))^s := by
  let a := Real.sqrt ((n:ℝ)+1)
  let c := (Real.sqrt (2*Real.pi))⁻¹
  let f (x : ℝ) := phi x * Phi (a⁻¹*x)^s
  have ha : 0 < a := by dsimp [a]; positivity
  have ha2 : a^2 = (n:ℝ)+1 := Real.sq_sqrt (by positivity)
  have hphi (x : ℝ) : phi x^(n+1) = c^n * phi (a*x) := by
    simp only [moment_phi_formula, mul_pow, ← Real.exp_nat_mul, c]
    rw [ha2, Nat.cast_add_one, pow_succ ((Real.sqrt (2*Real.pi))⁻¹),
      show ((n:ℝ)+1) * (-(x^2)/2) = -(((n:ℝ)+1)*x^2)/2 by ring]
    ring
  change _ = c^n / a * ∫ x : ℝ, f x
  calc
    _ = ∫ x : ℝ, c^n * f (a*x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [hphi, f, inv_mul_cancel_left₀ ha.ne']
      ring
    _ = _ := by
      rw [integral_const_mul, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr ha),
        smul_eq_mul]
      ring

end HermiteLaptop.MaxAgree
end

/- Symmetry.lean -/
section
open MeasureTheory

namespace HermiteLaptop.MaxAgree

theorem moment_scaled_power_integrable (t : ℝ) (s : ℕ) :
    Integrable (fun x : ℝ => phi x * Phi (t*x)^s) := by
  have hφ : Continuous phi := continuous_iff_continuousAt.mpr fun x =>
    (moment_phi_deriv x).continuousAt
  have hΦ : Continuous Phi := continuous_iff_continuousAt.mpr fun x =>
    (moment_Phi_deriv x).continuousAt
  refine moment_phi_integrable.mono'
    ((hφ.mul ((hΦ.comp (continuous_const.mul continuous_id)).pow s)).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (moment_phi_nonneg _) (pow_nonneg (moment_Phi_nonneg _) _))]
  exact mul_le_of_le_one_right (moment_phi_nonneg _)
    (pow_le_one₀ (moment_Phi_nonneg _) (moment_Phi_le_one _))

private theorem moment_scaled_reflect (t : ℝ) (s : ℕ) :
    (∫ x : ℝ, phi x * (1-Phi (t*x))^s) = ∫ x : ℝ, phi x * Phi (t*x)^s := by
  have h := integral_neg_eq_self (fun x : ℝ => phi x * Phi (t*x)^s) (μ := volume)
  simpa only [mul_neg, moment_phi_neg, moment_Phi_neg] using h

theorem moment_scaled_one (t : ℝ) :
    (∫ x : ℝ, phi x * Phi (t*x)^1) = 1/2 := by
  have h := moment_scaled_reflect t 1
  have he : (fun x : ℝ => phi x * (1-Phi (t*x))^1) =
      fun x : ℝ => phi x - phi x * Phi (t*x)^1 := by funext x; ring
  rw [he, integral_sub moment_phi_integrable (moment_scaled_power_integrable t 1),
    moment_phi_integral] at h
  linarith

theorem moment_scaled_three (t : ℝ) :
    (∫ x : ℝ, phi x * Phi (t*x)^3) = (3/2) * (∫ x : ℝ, phi x * Phi (t*x)^2) - 1/4 := by
  have h := moment_scaled_reflect t 3
  have he : (fun x : ℝ => phi x * (1-Phi (t*x))^3) =
      fun x : ℝ => phi x - 3 * (phi x * Phi (t*x)^1)
        + 3 * (phi x * Phi (t*x)^2) - phi x * Phi (t*x)^3 := by funext x; ring
  have h1 := (moment_scaled_power_integrable t 1).const_mul (3:ℝ)
  have h2 := (moment_scaled_power_integrable t 2).const_mul (3:ℝ)
  have h3 := moment_scaled_power_integrable t 3
  have ha : Integrable (fun x : ℝ => phi x - 3 * (phi x * Phi (t*x)^1)) :=
    moment_phi_integrable.sub h1
  have hb : Integrable (fun x : ℝ => phi x - 3 * (phi x * Phi (t*x)^1)
      + 3 * (phi x * Phi (t*x)^2)) := ha.add h2
  rw [he, integral_sub hb h3,
    integral_add ha h2, integral_sub moment_phi_integrable h1,
    integral_const_mul, integral_const_mul, moment_phi_integral, moment_scaled_one] at h
  linarith

end HermiteLaptop.MaxAgree
end

/- Bases.lean -/
section
open MeasureTheory

namespace HermiteLaptop.MaxAgree

/-- Total mass of the (n+1)-st power of the standard Gaussian density. -/
noncomputable def momentMass (n : ℕ) : ℝ :=
  (Real.sqrt (2*Real.pi))⁻¹ ^ n / Real.sqrt ((n:ℝ)+1)

private theorem moment_zero_scale (n s : ℕ) :
    hermiteMoment (n+1) s 0 = momentMass n *
      ∫ x : ℝ, phi x * (Phi ((Real.sqrt ((n:ℝ)+1))⁻¹*x))^s := by
  simpa [hermiteMoment, momentMass] using moment_density_power_scale n s

private theorem moment_scale_correlation (n : ℕ) :
    (Real.sqrt ((n:ℝ)+1))⁻¹^2 / (1 + (Real.sqrt ((n:ℝ)+1))⁻¹^2) = 1 / ((n:ℝ)+2) := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  rw [inv_pow, Real.sq_sqrt hn.le]
  field_simp [hn.ne', (show (n:ℝ)+2 ≠ 0 by positivity)]
  ring

theorem hermiteMoment_zero_cdf (n : ℕ) : hermiteMoment (n+1) 0 0 = momentMass n := by
  rw [moment_zero_scale]
  simp [moment_phi_integral]

theorem hermiteMoment_one_cdf (n : ℕ) :
    hermiteMoment (n+1) 1 0 = momentMass n * (1/2) := by
  rw [moment_zero_scale, moment_scaled_one]

theorem hermiteMoment_two_cdf (n : ℕ) :
    hermiteMoment (n+1) 2 0 = momentMass n *
      (1/4 + Real.arcsin (1/((n:ℝ)+2))/(2*Real.pi)) := by
  rw [moment_zero_scale, moment_scaled_quadrant, moment_scale_correlation]

theorem hermiteMoment_three_cdf (n : ℕ) :
    hermiteMoment (n+1) 3 0 = momentMass n *
      ((3/2) * (1/4 + Real.arcsin (1/((n:ℝ)+2))/(2*Real.pi)) - 1/4) := by
  rw [moment_zero_scale, moment_scaled_three, moment_scaled_quadrant, moment_scale_correlation]

/-- The form of the quadrant constant used by the rational arctangent certificate. -/
theorem moment_asin_to_atan (d : ℝ) (hd : 0 < d) :
    Real.arcsin (1/(d+1)) = Real.arctan (1 / Real.sqrt (d*(d+2))) := by
  have hpos : 0 < d+1 := by positivity
  have hprod : 0 < d*(d+2) := by positivity
  have hlt : 1/(d+1) < 1 := (div_lt_one hpos).mpr (by linarith)
  rw [Real.arcsin_eq_arctan ⟨by linarith [one_div_pos.mpr hpos], hlt⟩]
  congr 1
  rw [show 1-(1/(d+1))^2 = (d*(d+2))/(d+1)^2 by field_simp; ring,
    Real.sqrt_div hprod.le, Real.sqrt_sq hpos.le]
  field_simp

end HermiteLaptop.MaxAgree
end

/- Constants.lean -/
section
namespace HermiteLaptop.MaxAgree

open Filter Finset
open scoped Topology

private def cut (q : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ range n, (-1 : ℚ)^i * q^i / (2*(i:ℚ)+1)

private theorem arctan_cuts {x : ℝ} (hx : 0 ≤ x) (hx' : x < 1)
    (q : ℚ) (hq : x^2 = (q:ℝ)) (n : ℕ) :
    x * (cut q (2*n) : ℝ) ≤ Real.arctan x ∧
    Real.arctan x ≤ x * (cut q (2*n+1) : ℝ) := by
  let f (i : ℕ) : ℝ := x^(2*i+1) / ((2*i+1:ℕ):ℝ)
  have h := (Real.hasSum_arctan (x := x) (by simpa [Real.norm_eq_abs, abs_of_nonneg hx] using hx')).tendsto_sum_nat
  have hlim : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ)^i * f i) atTop (𝓝 (Real.arctan x)) := by
    simpa only [f, mul_div_assoc] using h
  have hanti : Antitone f := by
    intro i j hij
    unfold f
    apply div_le_div₀ _ _ _ _
    · positivity
    · exact pow_le_pow_of_le_one hx hx'.le (by omega)
    · positivity
    · exact_mod_cast (show 2*i+1 ≤ 2*j+1 by omega)
  have hc (n : ℕ) : (∑ i ∈ range n, (-1 : ℝ)^i * f i) = x * (cut q n : ℝ) := by
    simp only [cut, Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg,
      Rat.cast_one, Rat.cast_add, Rat.cast_ofNat, Rat.cast_natCast, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [f]
    rw [← hq, pow_succ, pow_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [← hc, ← hc]
  exact ⟨hanti.alternating_series_le_tendsto hlim n, hanti.tendsto_le_alternating_series hlim n⟩

private def Encl (l u : ℚ) (x : ℝ) : Prop := (l:ℝ) ≤ x ∧ x ≤ (u:ℝ)

private theorem encl_widen {l u l' u' : ℚ} {x : ℝ} (h : Encl l u x)
    (hl : l' ≤ l) (hu : u ≤ u') : Encl l' u' x :=
  ⟨(Rat.cast_le.mpr hl).trans h.1, h.2.trans (Rat.cast_le.mpr hu)⟩

private theorem encl_mul {l u l' u' : ℚ} {x y : ℝ} (h : Encl l u x) (h' : Encl l' u' y)
    (hl : 0 ≤ l) (hl' : 0 ≤ l') : Encl (l*l') (u*u') (x*y) := by
  unfold Encl at *
  push_cast
  have ha : 0 ≤ (l:ℝ) := by exact_mod_cast hl
  have hb : 0 ≤ (l':ℝ) := by exact_mod_cast hl'
  exact ⟨mul_le_mul h.1 h'.1 hb (ha.trans h.1),
    mul_le_mul h.2 h'.2 (hb.trans h'.1) ((ha.trans h.1).trans h.2)⟩

private theorem encl_div {l u l' u' : ℚ} {x y : ℝ} (h : Encl l u x) (h' : Encl l' u' y)
    (hl : 0 ≤ l) (hl' : 0 < l') : Encl (l/u') (u/l') (x/y) := by
  unfold Encl at *
  push_cast
  have ha : 0 ≤ (l:ℝ) := by exact_mod_cast hl
  have hb : 0 < (l':ℝ) := by exact_mod_cast hl'
  exact ⟨div_le_div₀ (ha.trans h.1) h.1 (hb.trans_le h'.1) h'.2,
    div_le_div₀ ((ha.trans h.1).trans h.2) h.2 hb h'.1⟩

private theorem encl_exact (q : ℚ) : Encl q q (q:ℝ) := ⟨le_rfl,le_rfl⟩

private theorem encl_add {l u l' u' : ℚ} {x y : ℝ} (h : Encl l u x) (h' : Encl l' u' y) :
    Encl (l+l') (u+u') (x+y) := by
  exact ⟨by simpa using add_le_add h.1 h'.1, by simpa using add_le_add h.2 h'.2⟩

private theorem encl_sub {l u l' u' : ℚ} {x y : ℝ} (h : Encl l u x) (h' : Encl l' u' y) :
    Encl (l-u') (u-l') (x-y) := by
  exact ⟨by simpa using sub_le_sub h.1 h'.2, by simpa using sub_le_sub h.2 h'.1⟩

private theorem encl_sqrt {l u a b : ℚ} {x : ℝ} (h : Encl l u x) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hl : a^2 ≤ l) (hu : u ≤ b^2) : Encl a b (Real.sqrt x) := by
  have ha' : 0 ≤ (a:ℝ) := by exact_mod_cast ha
  have hb' : 0 ≤ (b:ℝ) := by exact_mod_cast hb
  have h0 : (a:ℝ)^2 ≤ x := (show (a:ℝ)^2 ≤ (l:ℝ) by exact_mod_cast hl).trans h.1
  have h1 : x ≤ (b:ℝ)^2 := h.2.trans (by exact_mod_cast hu)
  exact ⟨(Real.le_sqrt ha' ((sq_nonneg _).trans h0)).mpr h0, (Real.sqrt_le_left hb').mpr h1⟩

private theorem atan_encl {x : ℝ} {l u a b q : ℚ} (hx : Encl l u x)
    (hl : 0 ≤ l) (hu : u < 1) (hq : x^2 = (q:ℝ)) (n : ℕ)
    (hcl : 0 ≤ cut q (2*n)) (hcu : 0 ≤ cut q (2*n+1))
    (hlo : a ≤ l * cut q (2*n)) (hhi : u * cut q (2*n+1) ≤ b) :
    Encl a b (Real.arctan x) := by
  have ha : 0 ≤ (l:ℝ) := by exact_mod_cast hl
  have hb : (u:ℝ) < 1 := by exact_mod_cast hu
  obtain ⟨h₁,h₂⟩ := arctan_cuts (ha.trans hx.1) (hx.2.trans_lt hb) q hq n
  exact ⟨(Rat.cast_le.mpr hlo).trans (((encl_mul hx (encl_exact _) hl hcl).1).trans h₁),
    h₂.trans ((encl_mul hx (encl_exact _) hl hcu).2.trans (Rat.cast_le.mpr hhi))⟩

private theorem pi_encl : Encl 3.14159265358979323846 3.14159265358979323847 Real.pi := by
  exact ⟨by exact_mod_cast Real.pi_gt_d20.le, by exact_mod_cast Real.pi_lt_d20.le⟩

private theorem sqrt_two_pi : Encl 2.506628274631000502 2.506628274631000503 (Real.sqrt (2*Real.pi)) := by
  apply encl_sqrt (encl_mul (encl_exact 2) pi_encl (by decide +kernel) (by decide +kernel)) <;> decide +kernel

private theorem sqrt_2_encl : Encl 1.414213562373095048 1.414213562373095049 (Real.sqrt 2) := by
  apply encl_sqrt (encl_exact 2) <;> decide +kernel

private theorem sqrt_3_encl : Encl 1.732050807568877293 1.732050807568877294 (Real.sqrt 3) := by
  apply encl_sqrt (encl_exact 3) <;> decide +kernel

private theorem sqrt_4_encl : Encl 2 2 (Real.sqrt 4) := by
  apply encl_sqrt (encl_exact 4) <;> decide +kernel

private theorem sqrt_5_encl : Encl 2.236067977499789696 2.236067977499789697 (Real.sqrt 5) := by
  apply encl_sqrt (encl_exact 5) <;> decide +kernel

private theorem asin_3_encl : Encl 0.3398369094541219 0.3398369094541220 (Real.arcsin (1/3)) := by
  rw [show (1/3:ℝ) = 1/((2:ℝ)+1) by norm_num, moment_asin_to_atan _ (by norm_num)]
  norm_num only [Nat.cast_ofNat, show (2:ℝ)*(2+2) = 8 by norm_num]
  let x := 1 / Real.sqrt 8
  have hs : x^2 = ((1/8:ℚ):ℝ) := by
    norm_num [x, div_pow, Real.sq_sqrt]
  have hx : Encl 0.353553390593273762 0.353553390593273763 x := by
    have hx0 : 0 < x := by dsimp [x]; positivity
    constructor
    · norm_num at hs ⊢
      nlinarith only [hs, hx0]
    · norm_num at hs ⊢
      nlinarith only [hs, hx0]
  apply atan_encl hx (by decide +kernel) (by decide +kernel) hs 11 <;> decide +kernel

private theorem asin_4_encl : Encl 0.2526802551420786 0.2526802551420787 (Real.arcsin (1/4)) := by
  rw [show (1/4:ℝ) = 1/((3:ℝ)+1) by norm_num, moment_asin_to_atan _ (by norm_num)]
  norm_num only [Nat.cast_ofNat, show (3:ℝ)*(3+2) = 15 by norm_num]
  let x := 1 / Real.sqrt 15
  have hs : x^2 = ((1/15:ℚ):ℝ) := by
    norm_num [x, div_pow, Real.sq_sqrt]
  have hx : Encl 0.258198889747161125 0.258198889747161126 x := by
    have hx0 : 0 < x := by dsimp [x]; positivity
    constructor
    · norm_num at hs ⊢
      nlinarith only [hs, hx0]
    · norm_num at hs ⊢
      nlinarith only [hs, hx0]
  apply atan_encl hx (by decide +kernel) (by decide +kernel) hs 11 <;> decide +kernel

private theorem encl_pow {l u : ℚ} {x : ℝ} (hx : Encl l u x) (hl : 0 ≤ l) (n : ℕ) :
    Encl (l^n) (u^n) (x^n) := by
  have ha : 0 ≤ (l:ℝ) := by exact_mod_cast hl
  exact ⟨by simpa using pow_le_pow_left₀ ha hx.1 n,
    by simpa using pow_le_pow_left₀ (ha.trans hx.1) hx.2 n⟩

private theorem mass_1_encl : Encl 0.2820947917738781 0.2820947917738782 (momentMass 1) := by
  have h₁ := encl_div (encl_exact 1) sqrt_two_pi (by decide +kernel) (by decide +kernel)
  have h₂ := encl_pow h₁ (by decide +kernel) 1
  have h₃ := encl_div h₂ sqrt_2_encl (by decide +kernel) (by decide +kernel)
  have h := encl_widen h₃ (l' := 0.2820947917738781) (u' := 0.2820947917738782) (by decide +kernel) (by decide +kernel)
  convert h using 1
  simp [momentMass, one_div]
  norm_num

private theorem mass_2_encl : Encl 0.0918881492369653 0.0918881492369654 (momentMass 2) := by
  have h₁ := encl_div (encl_exact 1) sqrt_two_pi (by decide +kernel) (by decide +kernel)
  have h₂ := encl_pow h₁ (by decide +kernel) 2
  have h₃ := encl_div h₂ sqrt_3_encl (by decide +kernel) (by decide +kernel)
  have h := encl_widen h₃ (l' := 0.0918881492369653) (u' := 0.0918881492369654) (by decide +kernel) (by decide +kernel)
  convert h using 1
  simp [momentMass, one_div]
  norm_num

private theorem mass_3_encl : Encl 0.0317468179671204 0.0317468179671205 (momentMass 3) := by
  have h₁ := encl_div (encl_exact 1) sqrt_two_pi (by decide +kernel) (by decide +kernel)
  have h₂ := encl_pow h₁ (by decide +kernel) 3
  have h₃ := encl_div h₂ sqrt_4_encl (by decide +kernel) (by decide +kernel)
  have h := encl_widen h₃ (l' := 0.0317468179671204) (u' := 0.0317468179671205) (by decide +kernel) (by decide +kernel)
  convert h using 1
  simp [momentMass, one_div]
  norm_num

private theorem mass_4_encl : Encl 0.0113280527092503 0.0113280527092504 (momentMass 4) := by
  have h₁ := encl_div (encl_exact 1) sqrt_two_pi (by decide +kernel) (by decide +kernel)
  have h₂ := encl_pow h₁ (by decide +kernel) 4
  have h₃ := encl_div h₂ sqrt_5_encl (by decide +kernel) (by decide +kernel)
  have h := encl_widen h₃ (l' := 0.0113280527092503) (u' := 0.0113280527092504) (by decide +kernel) (by decide +kernel)
  convert h using 1
  simp [momentMass, one_div]
  norm_num

private theorem quadrant_2_encl : Encl 0.3040867239846962 0.3040867239846965 (1/4 + Real.arcsin (1/3)/(2*Real.pi)) := by
  have h₁ := encl_mul (encl_exact 2) pi_encl (by decide +kernel) (by decide +kernel)
  have h₂ := encl_div asin_3_encl h₁ (by decide +kernel) (by decide +kernel)
  have h₃ := encl_add (encl_exact (1/4)) h₂
  have h := encl_widen h₃ (l' := 0.3040867239846962) (u' := 0.3040867239846965) (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

private theorem quadrant_3_encl : Encl 0.2902153116275830 0.2902153116275833 (1/4 + Real.arcsin (1/4)/(2*Real.pi)) := by
  have h₁ := encl_mul (encl_exact 2) pi_encl (by decide +kernel) (by decide +kernel)
  have h₂ := encl_div asin_4_encl h₁ (by decide +kernel) (by decide +kernel)
  have h₃ := encl_add (encl_exact (1/4)) h₂
  have h := encl_widen h₃ (l' := 0.2902153116275830) (u' := 0.2902153116275833) (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

theorem hermiteMoment_base_23 :
    (5814822368202 : ℝ)/10^14 ≤ hermiteMoment 2 3 0 ∧
      hermiteMoment 2 3 0 ≤ (5814822368203 : ℝ)/10^14 := by
  have hc := encl_sub (encl_mul (encl_exact (3/2)) quadrant_2_encl (by decide +kernel) (by decide +kernel)) (encl_exact (1/4))
  have h := encl_mul mass_1_encl hc (by decide +kernel) (by decide +kernel)
  have hb := encl_widen h (l' := 5814822368202/10^14) (u' := 5814822368203/10^14) (by decide +kernel) (by decide +kernel)
  rw [hermiteMoment_three_cdf 1]
  norm_num [Encl] at hb ⊢
  exact hb

theorem hermiteMoment_base_32 :
    (2666734786568 : ℝ)/10^14 ≤ hermiteMoment 3 2 0 ∧
      hermiteMoment 3 2 0 ≤ (2666734786569 : ℝ)/10^14 := by
  have h := encl_mul mass_2_encl quadrant_3_encl (by decide +kernel) (by decide +kernel)
  have hb := encl_widen h (l' := 2666734786568/10^14) (u' := 2666734786569/10^14) (by decide +kernel) (by decide +kernel)
  rw [hermiteMoment_two_cdf 2]
  norm_num [Encl] at hb ⊢
  exact hb

theorem hermiteMoment_base_41 :
    (1587340898356 : ℝ)/10^14 ≤ hermiteMoment 4 1 0 ∧
      hermiteMoment 4 1 0 ≤ (1587340898357 : ℝ)/10^14 := by
  have h := encl_mul mass_3_encl (encl_exact (1/2)) (by decide +kernel) (by decide +kernel)
  have hb := encl_widen h (l' := 1587340898356/10^14) (u' := 1587340898357/10^14) (by decide +kernel) (by decide +kernel)
  rw [hermiteMoment_one_cdf 3]
  norm_num [Encl] at hb ⊢
  exact hb

theorem hermiteMoment_base_50 :
    (1132805270925 : ℝ)/10^14 ≤ hermiteMoment 5 0 0 ∧
      hermiteMoment 5 0 0 ≤ (1132805270926 : ℝ)/10^14 := by
  have h := mass_4_encl
  have hb := encl_widen h (l' := 1132805270925/10^14) (u' := 1132805270926/10^14) (by decide +kernel) (by decide +kernel)
  rw [hermiteMoment_zero_cdf 4]
  norm_num [Encl] at hb ⊢
  exact hb

end HermiteLaptop.MaxAgree
end

/- MomentBands.lean -/
section
namespace HermiteLaptop.MaxAgree

/-! Each row fixes the density power d, and each column the monomial degree j.
The integer endpoints use denominator 10¹⁴. The proof checks the initial
values and every outward rounding in the table against the exact recurrence. -/


private def bands5 : Array (Array (ℤ × ℤ)) := #[
  #[(20000000000000, 20000000000000), (23259289472808, 23259289472812), (36000408719408, 36000408719416),
    (64497587275440, 64497587275464), (130467909721692, 130467909721732), (290779111557132, 290779111557264),
    (704532154269096, 704532154269348), (1835597414435832, 1835597414436744), (5101330528077228, 5101330528079196),
    (15022398733313716, 15022398733321512), (46622323638745524, 46622323638764192), (151797585104524076, 151797585104604524),
    (516496334621798848, 516496334622009452), (1830412703154247156, 1830412703155227064), (6736728573037347572, 6736728573040118852),
    (25684012466818820468, 25684012466832637200), (101208498464174582068, 101208498464216393916), (411384575396618954576, 411384575396840774592),
    (1721813307856853526232, 1721813307857566313736), (7408685035615575501240, 7408685035619574749664), (32725919626523506656040, 32725919626537067754516)],
  #[(5814822368202, 5814822368203), (4000102179852, 4000102179854), (4494752082456, 4494752082460),
    (5616670890867, 5616670890871), (8197190613843, 8197190613852), (13048151415159, 13048151415172),
    (22730686273260, 22730686273290), (42401362048389, 42401362048440), (84404854456765, 84404854456890),
    (177587221512618, 177587221512857), (393399442846729, 393399442847351), (912693648899521, 912693648900835),
    (2210420474989561, 2210420474993194), (5569055738490637, 5569055738498994), (14558655664840071, 14558655664864576),
    (39392467153592122, 39392467153652784), (110093981879456772, 110093981879644848), (317208491471407769, 317208491471904291),
    (940669619108579718, 940669619110201752), (2866694310822414408, 2866694310826948383), (8965794679901903407, 8965794679917455249)],
  #[(2666734786568, 2666734786569), (1058227265570, 1058227265572), (1077712474010, 1077712474011),
    (970041660106, 970041660108), (1209873088950, 1209873088953), (1491806492435, 1491806492440),
    (2171271868608, 2171271868616), (3231635000237, 3231635000250), (5321182212708, 5321182212731),
    (9051731860858, 9051731860897), (16505027557621, 16505027557700), (31149026221701, 31149026221842),
    (61929230062341, 61929230062656), (127281718271950, 127281718272543), (272717989438442, 272717989439884),
    (602709595437493, 602709595440352), (1379169495113862, 1379169495121346), (3247182088798104, 3247182088813696),
    (7878591719829658, 7878591719873176), (19622198913597391, 19622198913692403), (50185919229243774, 50185919229524418)],
  #[(1587340898356, 1587340898357), (283201317731, 283201317732), (396835224589, 396835224590),
    (198240922411, 198240922413), (297626418441, 297626418443), (232225080538, 232225080541),
    (372033023051, 372033023054), (382321778934, 382321778940), (651057790339, 651057790345),
    (812221379246, 812221379260), (1464880028262, 1464880028277), (2116193526596, 2116193526633),
    (4028420077720, 4028420077762), (6536988752447, 6536988752562), (13092365252590, 13092365252727),
    (23369321882479, 23369321882889), (49096369697212, 49096369697727), (94946871276661, 94946871278322),
    (208659571213151, 208659571215340), (432257505483910, 432257505491454), (991132963262467, 991132963272865)],
  #[(1132805270925, 1132805270926), (0, 0), (226561054185, 226561054186),
    (0, 0), (135936632511, 135936632512), (0, 0),
    (135936632511, 135936632512), (0, 0), (190311285515, 190311285517),
    (0, 0), (342560313927, 342560313931), (0, 0),
    (753632690639, 753632690649), (0, 0), (1959444995661, 1959444995688),
    (0, 0), (5878334986983, 5878334987064), (0, 0),
    (19986338955742, 19986338956018), (0, 0), (75948088031819, 75948088032869)]
]

/-- Integer bounds for the moment with d density factors, k-d CDF factors,
and monomial degree j, scaled by 10¹⁴. -/
def momentBand (k d j : ℕ) : ℤ × ℤ :=
  let all := if k = 5 then bands5 else #[]
  ((all[d-1]?.getD #[])[j]?.getD (0,0))

private def stepOK (k d j : ℕ) : Prop :=
  (d:ℤ) * (momentBand k d (j+1)).1 ≤
    (j:ℤ) * (momentBand k d (j-1)).1 + ((k-d:ℕ):ℤ) * (momentBand k (d+1) j).1 ∧
  (j:ℤ) * (momentBand k d (j-1)).2 + ((k-d:ℕ):ℤ) * (momentBand k (d+1) j).2 ≤
    (d:ℤ) * (momentBand k d (j+1)).2

private instance (k d j : ℕ) : Decidable (stepOK k d j) := by unfold stepOK; infer_instance


set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem step5 : ∀ d : Fin 5, ∀ j : Fin 20, stepOK 5 (d.val+1) j.val := by
  decide +kernel

private theorem step_checked (k d j : ℕ) (hk : k=5) (hd : 1 ≤ d)
    (hdk : d ≤ k) (hj : j < 20) : stepOK k d j := by
  subst k
  simpa only [Nat.sub_add_cancel hd] using step5 ⟨d-1, by omega⟩ ⟨j,hj⟩

private def BoundAt (k d j : ℕ) : Prop :=
  ((momentBand k d j).1 : ℝ) ≤ 100000000000000 * hermiteMoment d (k-d) j ∧
    100000000000000 * hermiteMoment d (k-d) j ≤ ((momentBand k d j).2 : ℝ)

private theorem bounds_base (k d : ℕ) (hk : k=5) (hd : 1 ≤ d) (hdk : d ≤ k) :
    BoundAt k d 0 := by
  subst k
  interval_cases d
  · change (20000000000000 : ℝ) ≤ 100000000000000 * hermiteMoment 1 4 0 ∧ _
    change _ ∧ 100000000000000 * hermiteMoment 1 4 0 ≤ (20000000000000 : ℝ)
    rw [hermiteMoment_one_zero]
    norm_num
  · change (5814822368202 : ℝ) ≤ 100000000000000 * hermiteMoment 2 3 0 ∧ _
    change _ ∧ 100000000000000 * hermiteMoment 2 3 0 ≤ (5814822368203 : ℝ)
    obtain ⟨hl,hu⟩ := hermiteMoment_base_23
    constructor <;> linarith
  · change (2666734786568 : ℝ) ≤ 100000000000000 * hermiteMoment 3 2 0 ∧ _
    change _ ∧ 100000000000000 * hermiteMoment 3 2 0 ≤ (2666734786569 : ℝ)
    obtain ⟨hl,hu⟩ := hermiteMoment_base_32
    constructor <;> linarith
  · change (1587340898356 : ℝ) ≤ 100000000000000 * hermiteMoment 4 1 0 ∧ _
    change _ ∧ 100000000000000 * hermiteMoment 4 1 0 ≤ (1587340898357 : ℝ)
    obtain ⟨hl,hu⟩ := hermiteMoment_base_41
    constructor <;> linarith
  · change (1132805270925 : ℝ) ≤ 100000000000000 * hermiteMoment 5 0 0 ∧ _
    change _ ∧ 100000000000000 * hermiteMoment 5 0 0 ≤ (1132805270926 : ℝ)
    obtain ⟨hl,hu⟩ := hermiteMoment_base_50
    constructor <;> linarith

/-- The integer table encloses all Gaussian moments required by the degree-20 certificate. -/
theorem momentBand_sound (k d j : ℕ) (hk : k=5) (hd : 1 ≤ d)
    (hdk : d ≤ k) (hj : j ≤ 20) :
    ((momentBand k d j).1 : ℝ) ≤ 100000000000000 * hermiteMoment d (k-d) j ∧
    100000000000000 * hermiteMoment d (k-d) j ≤ ((momentBand k d j).2 : ℝ) := by
  change BoundAt k d j
  induction j using Nat.strong_induction_on generalizing d with
  | h j ih =>
    cases j with
    | zero => exact bounds_base k d hk hd hdk
    | succ j =>
      let S : ℝ := 100000000000000
      have hrec := hermiteMoment_recurrence d (k-d) j hd
      have eqn : (d:ℝ) * (S * hermiteMoment d (k-d) (j+1)) =
          (j:ℝ) * (S * hermiteMoment d (k-d) (j-1)) +
          ((k-d:ℕ):ℝ) * (S * hermiteMoment (d+1) ((k-d)-1) j) := by
        linear_combination S * hrec
      have hjnn : (0:ℝ) ≤ j := Nat.cast_nonneg _
      have hsnn : (0:ℝ) ≤ (k-d:ℕ) := Nat.cast_nonneg _
      have hprev := ih (j-1) (by omega) d hd hdk (by omega)
      have hl₀ := mul_le_mul_of_nonneg_left hprev.1 hjnn
      have hu₀ := mul_le_mul_of_nonneg_left hprev.2 hjnn
      have hnext :
          ((k-d:ℕ):ℝ) * ((momentBand k (d+1) j).1:ℝ) ≤
            ((k-d:ℕ):ℝ) * (S * hermiteMoment (d+1) ((k-d)-1) j) ∧
          ((k-d:ℕ):ℝ) * (S * hermiteMoment (d+1) ((k-d)-1) j) ≤
            ((k-d:ℕ):ℝ) * ((momentBand k (d+1) j).2:ℝ) := by
        by_cases hd' : d+1 ≤ k
        · have hn := ih j (by omega) (d+1) (by omega) hd' (by omega)
          have hs : k-(d+1) = (k-d)-1 := by omega
          unfold BoundAt at hn
          rw [hs] at hn
          exact ⟨mul_le_mul_of_nonneg_left hn.1 hsnn, mul_le_mul_of_nonneg_left hn.2 hsnn⟩
        · have hs : k-d=0 := by omega
          simp [hs]
      obtain ⟨cl,cu⟩ := step_checked k d j hk hd hdk (by omega)
      have cl' : (d:ℝ) * ((momentBand k d (j+1)).1:ℝ) ≤
            (j:ℝ) * ((momentBand k d (j-1)).1:ℝ) +
            ((k-d:ℕ):ℝ) * ((momentBand k (d+1) j).1:ℝ) := by exact_mod_cast cl
      have cu' : (j:ℝ) * ((momentBand k d (j-1)).2:ℝ) +
            ((k-d:ℕ):ℝ) * ((momentBand k (d+1) j).2:ℝ) ≤
            (d:ℝ) * ((momentBand k d (j+1)).2:ℝ) := by exact_mod_cast cu
      have hdpos : (0:ℝ) < d := Nat.cast_pos.mpr hd
      constructor
      · apply (mul_le_mul_iff_right₀ hdpos).mp
        rw [eqn]
        exact cl'.trans (add_le_add hl₀ hnext.1)
      · apply (mul_le_mul_iff_right₀ hdpos).mp
        rw [eqn]
        exact (add_le_add hu₀ hnext.2).trans cu'

end HermiteLaptop.MaxAgree
end

/- Terms.lean -/
section
namespace HermiteLaptop.MaxAgree

/-- Integer lower contribution to a level weight, scaled by 10²⁰. -/
def certTerm (k a : ℕ) (xs : List ℕ) : ℕ :=
  let cs := denseSpoly a xs
  if cs.length ≤ 21 then
    weightedTerm k a xs (bandDistance (denseBand (momentBand k (rCount (xs : Multiset ℕ)+1)) cs 0))
  else 0

private theorem rCount_add_sCount (xs : List ℕ) :
    rCount (xs : Multiset ℕ) + sCount (xs : Multiset ℕ) = xs.length := by
  induction xs with
  | nil => simp [rCount, sCount]
  | cons b xs ih =>
    cases b <;> simp_all [rCount, sCount] <;> omega

private theorem bandDot_eq_moment (cs : List ℤ) (d s j : ℕ) :
    bandDot (hermiteMoment d s) cs j = denseMomentDot cs d s j := by
  induction cs generalizing j with
  | nil => rfl
  | cons c cs ih => simp [bandDot, denseMomentDot, ih]

theorem certTerm_le (k a : ℕ) (xs : List ℕ) (hk : k=5) (hlen : xs.length+1=k) :
    (certTerm k a xs : ℝ) / 10^20 ≤
      (k : ℝ) * Nmult (xs : Multiset ℕ) * Bal a (xs : Multiset ℕ)^2 / factDen a (xs : Multiset ℕ) := by
  let cs := denseSpoly a xs
  let d := rCount (xs : Multiset ℕ) + 1
  let s := sCount (xs : Multiset ℕ)
  have hds : d+s=k := by
    have h := rCount_add_sCount xs
    dsimp [d, s]
    omega
  have hfk : 0 < (factorialDen a xs : ℝ) := by exact_mod_cast factorialDen_pos a xs
  by_cases hcs : cs.length ≤ 21
  · have h := denseBand_sound (x := hermiteMoment d s) (b := momentBand k d) cs 0
      (fun i _ hi => by
        have h := momentBand_sound k d i hk (by dsimp [d]; omega) (by omega) (by omega)
        simpa only [show k-d=s by omega] using h)
    have hz := bandDistance_le h
    rw [bandDot_eq_moment] at hz
    have habs : |Bal a (xs : Multiset ℕ)| = |denseMomentDot cs d s 0| := by
      rw [bal_eq_denseMomentDot, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hfinal : ((bandDistance (denseBand (momentBand k d) cs 0)) : ℝ) ≤ |100000000000000 * Bal a (xs : Multiset ℕ)| := by
      rw [abs_mul, habs]
      rwa [abs_mul] at hz
    simpa [certTerm, hcs, cs, d] using weightedTerm_le k a xs _ hfinal
  · rw [show certTerm k a xs = 0 by exact if_neg hcs]
    simp only [Nat.cast_zero, zero_div]
    rw [multiplicityDen_eq, ← factorialDen_eq]
    positivity

end HermiteLaptop.MaxAgree
end

/- FastTerms.lean -/
section
namespace HermiteLaptop.MaxAgree

/-- Precomputed low-degree Hermite coefficients. Every row is checked against
one step of the defining recurrence below. -/
private def hermiteRows : ℕ → List ℤ
  | 0 => [1]
  | 1 => [0, 1]
  | 2 => [-1, 0, 1]
  | 3 => [0, -3, 0, 1]
  | 4 => [3, 0, -6, 0, 1]
  | 5 => [0, 15, 0, -10, 0, 1]
  | 6 => [-15, 0, 45, 0, -15, 0, 1]
  | 7 => [0, -105, 0, 105, 0, -21, 0, 1]
  | 8 => [105, 0, -420, 0, 210, 0, -28, 0, 1]
  | 9 => [0, 945, 0, -1260, 0, 378, 0, -36, 0, 1]
  | 10 => [-945, 0, 4725, 0, -3150, 0, 630, 0, -45, 0, 1]
  | 11 => [0, -10395, 0, 17325, 0, -6930, 0, 990, 0, -55, 0, 1]
  | 12 => [10395, 0, -62370, 0, 51975, 0, -13860, 0, 1485, 0, -66, 0, 1]
  | 13 => [0, 135135, 0, -270270, 0, 135135, 0, -25740, 0, 2145, 0, -78, 0, 1]
  | 14 => [-135135, 0, 945945, 0, -945945, 0, 315315, 0, -45045, 0, 3003, 0, -91, 0, 1]
  | 15 => [0, -2027025, 0, 4729725, 0, -2837835, 0, 675675, 0, -75075, 0, 4095, 0, -105, 0, 1]
  | 16 => [2027025, 0, -16216200, 0, 18918900, 0, -7567560, 0, 1351350, 0, -120120, 0, 5460, 0, -120, 0, 1]
  | 17 => [0, 34459425, 0, -91891800, 0, 64324260, 0, -18378360, 0, 2552550, 0, -185640, 0, 7140, 0, -136, 0, 1]
  | 18 => [-34459425, 0, 310134825, 0, -413513100, 0, 192972780, 0, -41351310, 0, 4594590, 0, -278460, 0, 9180, 0, -153, 0, 1]
  | 19 => [0, -654729075, 0, 1964187225, 0, -1571349780, 0, 523783260, 0, -87297210, 0, 7936110, 0, -406980, 0, 11628, 0, -171, 0, 1]
  | 20 => [654729075, 0, -6547290750, 0, 9820936125, 0, -5237832600, 0, 1309458150, 0, -174594420, 0, 13226850, 0, -581400, 0, 14535, 0, -190, 0, 1]
  | _ => []

private def fastHermite (n : ℕ) : List ℤ :=
  if n ≤ 20 then hermiteRows n else denseHermite n

private theorem fastHermite_eq (n : ℕ) : fastHermite n = denseHermite n := by
  by_cases hn : n ≤ 20
  · have h0 : hermiteRows 0 = denseHermite 0 := rfl
    have h1 : hermiteRows 1 = denseHermite 1 := by
      rw [denseHermite, ← h0]
      decide +kernel
    have h2 : hermiteRows 2 = denseHermite 2 := by
      rw [denseHermite, ← h1]
      decide +kernel
    have h3 : hermiteRows 3 = denseHermite 3 := by
      rw [denseHermite, ← h2]
      decide +kernel
    have h4 : hermiteRows 4 = denseHermite 4 := by
      rw [denseHermite, ← h3]
      decide +kernel
    have h5 : hermiteRows 5 = denseHermite 5 := by
      rw [denseHermite, ← h4]
      decide +kernel
    have h6 : hermiteRows 6 = denseHermite 6 := by
      rw [denseHermite, ← h5]
      decide +kernel
    have h7 : hermiteRows 7 = denseHermite 7 := by
      rw [denseHermite, ← h6]
      decide +kernel
    have h8 : hermiteRows 8 = denseHermite 8 := by
      rw [denseHermite, ← h7]
      decide +kernel
    have h9 : hermiteRows 9 = denseHermite 9 := by
      rw [denseHermite, ← h8]
      decide +kernel
    have h10 : hermiteRows 10 = denseHermite 10 := by
      rw [denseHermite, ← h9]
      decide +kernel
    have h11 : hermiteRows 11 = denseHermite 11 := by
      rw [denseHermite, ← h10]
      decide +kernel
    have h12 : hermiteRows 12 = denseHermite 12 := by
      rw [denseHermite, ← h11]
      decide +kernel
    have h13 : hermiteRows 13 = denseHermite 13 := by
      rw [denseHermite, ← h12]
      decide +kernel
    have h14 : hermiteRows 14 = denseHermite 14 := by
      rw [denseHermite, ← h13]
      decide +kernel
    have h15 : hermiteRows 15 = denseHermite 15 := by
      rw [denseHermite, ← h14]
      decide +kernel
    have h16 : hermiteRows 16 = denseHermite 16 := by
      rw [denseHermite, ← h15]
      decide +kernel
    have h17 : hermiteRows 17 = denseHermite 17 := by
      rw [denseHermite, ← h16]
      decide +kernel
    have h18 : hermiteRows 18 = denseHermite 18 := by
      rw [denseHermite, ← h17]
      decide +kernel
    have h19 : hermiteRows 19 = denseHermite 19 := by
      rw [denseHermite, ← h18]
      decide +kernel
    have h20 : hermiteRows 20 = denseHermite 20 := by
      rw [denseHermite, ← h19]
      decide +kernel
    rw [fastHermite, if_pos hn]
    interval_cases n <;> assumption
  · exact if_neg hn

private theorem denseMul_one (v : List ℤ) : denseMul v [1] = v := by
  induction v with
  | nil => rfl
  | cons c v ih => simp [denseMul, denseAdd, ih]

private def fastMul (v w : List ℤ) : List ℤ :=
  if w = [1] then v else denseMul v w

private theorem fastMul_eq (v w : List ℤ) : fastMul v w = denseMul v w := by
  by_cases h : w=[1]
  · simp [fastMul, h, denseMul_one]
  · simp [fastMul, h]

private def fastTail : List ℕ → List ℤ
  | [] => [1]
  | 0 :: tail => fastTail tail
  | (b+1) :: tail => fastMul (fastHermite b) (fastTail tail)

private def fastSpoly (a : ℕ) (xs : List ℕ) := fastMul (fastHermite a) (fastTail xs)
private theorem fastSpoly_eq (a : ℕ) (xs : List ℕ) : fastSpoly a xs = denseSpoly a xs := by
  rw [fastSpoly, fastMul_eq, fastHermite_eq, denseSpoly]
  congr 1
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | zero => exact ih
    | succ b =>
      rw [fastTail, fastMul_eq, fastHermite_eq, ih]
      rfl

def fastCertTerm (k a : ℕ) (xs : List ℕ) : ℕ :=
  let cs := fastSpoly a xs
  if cs.length ≤ 21 then
    weightedTerm k a xs (bandDistance (denseBand (momentBand k (rCount (xs : Multiset ℕ)+1)) cs 0))
  else 0

theorem fastCertTerm_eq (k a : ℕ) (xs : List ℕ) : fastCertTerm k a xs = certTerm k a xs := by
  simp only [fastCertTerm, certTerm, fastSpoly_eq]

end HermiteLaptop.MaxAgree
end

/- Truncated.lean -/
section
open MeasureTheory ProbabilityTheory Set

namespace HermiteLaptop.MaxAgree

theorem hermite_poly_density_integrable (P : Polynomial ℝ) :
    Integrable (fun x : ℝ => phi x * P.eval x) := by
  have he (x : ℝ) : phi x * P.eval x =
      ∑ j ∈ P.support, P.coeff j * (x^j * phi x) := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  apply integrable_finsetSum
  intro j _
  have h : Integrable (fun x : ℝ => x^j * phi x) := by
    simpa using hermiteMoment_integrable 1 0 j (by decide)
  exact h.const_mul _

private theorem H_succ_eval (n : ℕ) (x : ℝ) :
    H (n+1) x = x * H n x - (Hpoly n).derivative.eval x := by
  simp [H, Hpoly, Polynomial.hermite_succ, Polynomial.derivative_map]

/-- The truncated normalized Hermite integral, including the exceptional constant term. -/
theorem jInt_eq_Kfun (n : ℕ) (x : ℝ) :
    Jint n x = Kfun n x / Real.sqrt (Nat.factorial n) := by
  cases n with
  | zero => simp [Jint, Kfun, hNorm, H, Hpoly, ← moment_Phi_integral]
  | succ n =>
    have hd (y : ℝ) : HasDerivAt (fun z => -(phi z * H n z)) (phi y * H (n+1) y) y := by
      apply ((moment_phi_deriv y).mul ((Hpoly n).hasDerivAt y)).neg.congr_deriv
      rw [H_succ_eval]
      change -(_ * H n y + _ * _) = _
      ring
    have hi := (hermite_poly_density_integrable (Hpoly (n+1))).integrableOn (s := Iic x)
    have hf := (hermite_poly_density_integrable (Hpoly n)).neg.integrableOn (s := Iic x)
    have hb := tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (fun y _ => hd y) hi hf
    have hh := integral_Iic_of_hasDerivAt_of_tendsto' (fun y _ => hd y) hi hb
    simp only [sub_zero] at hh
    simp only [Jint, hNorm, Kfun, Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
    simp_rw [← mul_div_assoc, integral_div, hh]

end HermiteLaptop.MaxAgree
end

/- Coordinate.lean -/
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HermiteLaptop.MaxAgree

theorem hNorm_integrable_gaussian (a : ℕ) : Integrable (hNorm a) (gaussianReal 0 1) := by
  have hm (j : ℕ) : Integrable (fun x : ℝ => x ^ j) (gaussianReal 0 1) := by
    have hh := MemLp.integrable_norm_pow' (p := j)
      (memLp_id_gaussianReal' (μ := 0) (v := 1) (j : ℝ≥0∞) (by simp))
    apply hh.mono' (by fun_prop)
    filter_upwards with x
    simp
  have hp : Integrable (fun x => (Hpoly a).eval x) (gaussianReal 0 1) := by
    simp_rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    exact integrable_finsetSum _ fun j _ => (hm j).const_mul _
  exact hp.div_const _

private theorem argmax_measurable {k : ℕ} (p : Fin k) : MeasurableSet (argmaxRegion p) := by
  change MeasurableSet {x : Fin k → ℝ | ∀ q : Fin k, x q ≤ x p}
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun _ => measurableSet_le (by fun_prop) (by fun_prop)

private theorem cutoff_integral (a : ℕ) (u : ℝ) :
    (∫ x : ℝ, (Iic u).indicator (hNorm a) x ∂(gaussianReal 0 1)) = Jint a u := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul, Jint]
  rw [← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards with x
  by_cases h : x ∈ Iic u <;> simp [h, phi]

/-- Condition on the winning coordinate. Each other coordinate then has its own
one-dimensional upper cutoff. This also applies in dimension one. -/
theorem hermCoeff_eq_Jint {n : ℕ} (p : Fin (n+1)) (α : Fin (n+1) → ℕ) :
    hermCoeff p α = ∫ u : ℝ, phi u * hNorm (α p) u *
      ∏ j : Fin n, Jint (α (p.succAbove j)) u := by
  classical
  let F := (argmaxRegion p).indicator (hMulti α)
  have hint : Integrable F (gaussPi (n+1)) :=
    (Integrable.fintype_prod (fun j => hNorm_integrable_gaussian (α j))).indicator
      (argmax_measurable p)
  have heq : hermCoeff p α = ∫ x, F x ∂(gaussPi (n+1)) := by
    unfold hermCoeff
    apply integral_congr_ae
    filter_upwards with x
    by_cases h : x ∈ argmaxRegion p <;> simp [F, h]
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) p).symm
  have he : MeasurePreserving e ((gaussianReal 0 1).prod (gaussPi n)) (gaussPi (n+1)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) p).symm
  have hsplit (u : ℝ) (y : Fin n → ℝ) :
      F (e (u,y)) = hNorm (α p) u * ∏ j : Fin n,
        (Iic u).indicator (hNorm (α (p.succAbove j))) (y j) := by
    change (argmaxRegion p).indicator (hMulti α) (p.insertNth u y) = _
    have hx : p.insertNth (α := fun _ => ℝ) u y ∈ argmaxRegion p ↔ ∀ j, y j ≤ u := by
      change (∀ q, (p.insertNth (α := fun _ => ℝ) u y) q ≤ (p.insertNth (α := fun _ => ℝ) u y) p) ↔ _
      rw [p.forall_iff_succAbove]
      simp
    by_cases h : ∀ j, y j ≤ u
    · rw [indicator_of_mem (hx.mpr h), hMulti, Fin.prod_univ_succAbove _ p]
      simp [h, Set.mem_Iic]
    · rw [indicator_of_notMem (fun h' => h (hx.mp h'))]
      obtain ⟨j,hj⟩ := not_forall.mp h
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem (show y j ∉ Iic u from hj) _), mul_zero]
  let : IsProbabilityMeasure (gaussPi n) := by unfold gaussPi; infer_instance
  rw [heq, ← he.integral_comp' F, integral_prod (fun z => F (e z)) (he.integrable_comp_of_integrable hint)]
  simp_rw [hsplit, integral_const_mul]
  unfold gaussPi
  simp_rw [integral_fintype_prod_eq_prod, cutoff_integral]
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [phi, smul_eq_mul, mul_assoc]

/-- The squared coefficient at any argmax cell, in the multiset notation
used by the finite certificate. -/
theorem hermCoeff_sq_eq_bal {n : ℕ} (p : Fin (n+1)) (α : Fin (n+1) → ℕ) :
    hermCoeff p α ^ 2 =
      Bal (α p) (Finset.univ.val.map (fun j : Fin n => α (p.succAbove j))) ^ 2 /
      factDen (α p) (Finset.univ.val.map (fun j : Fin n => α (p.succAbove j))) := by
  let β := fun j : Fin n => α (p.succAbove j)
  let D := Real.sqrt (Nat.factorial (α p)) * ∏ j, Real.sqrt (Nat.factorial (β j))
  have hB : hermCoeff p α = Bal (α p) (Finset.univ.val.map β) / D := by
    rw [hermCoeff_eq_Jint, Bal, ← integral_div]
    apply integral_congr_ae
    filter_upwards with u
    simp only [jInt_eq_Kfun, Finset.prod_div_distrib, hNorm, D, β, integrandB,
      Multiset.map_map, ← Finset.prod_eq_multiset_prod, Function.comp_apply]
    ring
  rw [hB, div_pow]
  congr 1
  simp only [D, mul_pow, ← Finset.prod_pow, Real.sq_sqrt (Nat.cast_nonneg _), factDen,
    Multiset.map_map, ← Finset.prod_eq_multiset_prod, Function.comp_apply, β]

end HermiteLaptop.MaxAgree
end

/- Grouping.lean -/
section
open Finset
namespace HermiteLaptop.MaxAgree

private abbrev tup {j : ℕ} (u : Fin j → ℕ) : Multiset ℕ := Finset.univ.val.map u

private theorem prod_X (l : Multiset ℕ) :
    (l.map (MvPolynomial.X (R := ℕ))).prod = MvPolynomial.monomial l.toFinsupp 1 := by
  classical
  induction l using Multiset.induction_on with
  | empty => simp [MvPolynomial.monomial_zero']
  | cons b l ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add,
      map_add, Multiset.toFinsupp_singleton, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

private theorem coeff_prod_X (l v : Multiset ℕ) :
    MvPolynomial.coeff l.toFinsupp (v.map (MvPolynomial.X (R := ℕ))).prod =
      if v = l then 1 else 0 := by
  rw [prod_X, MvPolynomial.coeff_monomial]
  simp

private theorem tuple_prod_X {j : ℕ} (u : Fin j → ℕ) :
    (∏ i, (MvPolynomial.X (u i) : MvPolynomial ℕ ℕ)) =
      ((tup u).map (MvPolynomial.X (R := ℕ))).prod := by
  simp [tup, Function.comp_def, Finset.prod]

private theorem fiber_card (j : ℕ) (l : Multiset ℕ) (hj : l.card = j) :
    ((Fintype.piFinset fun _ : Fin j => l.toFinset).filter (fun u => tup u = l)).card
      = l.countPerms := by
  classical
  let v : Sym ℕ j := ⟨l,hj⟩
  have hv : v ∈ l.toFinset.sym j := Finset.mem_sym_iff.mpr (by simp [v])
  have h := congrArg (MvPolynomial.coeff l.toFinsupp)
    ((Finset.sum_pow' l.toFinset (MvPolynomial.X (R := ℕ)) j).symm.trans
      (Finset.sum_pow (s := l.toFinset) (MvPolynomial.X (R := ℕ)) j))
  simp only [MvPolynomial.coeff_sum, tuple_prod_X, coeff_prod_X] at h
  rw [Finset.card_filter]
  convert h using 1
  symm
  rw [Finset.sum_eq_single_of_mem v hv]
  · rw [← MvPolynomial.C_eq_coe_nat, MvPolynomial.coeff_C_mul, coeff_prod_X]
    simp [v]
  · intro b _ hb
    have hne : (b : Multiset ℕ) ≠ l := fun he => hb (Subtype.ext he)
    rw [← MvPolynomial.C_eq_coe_nat, MvPolynomial.coeff_C_mul, coeff_prod_X]
    split_ifs with he
    · exact False.elim (hne he)
    · simp

private theorem Nmult_eq_countPerms (l : Multiset ℕ) : Nmult l = (l.countPerms : ℝ) := by
  classical
  unfold Nmult
  apply (div_eq_iff (Finset.prod_ne_zero_iff.mpr fun b _ => by positivity)).mpr
  have hc := Nat.multinomial_spec l.toFinset l.count
  have hsum : (∑ b ∈ l.toFinset, l.count b) = l.card := l.toFinsupp_sum_eq
  rw [hsum, mul_comm] at hc
  exact_mod_cast hc.symm

private theorem antidiagonal_fiber_card (j s : ℕ) {l : Multiset ℕ} (hl : l ∈ multisetsOf j s) :
    (((Finset.Nat.antidiagonalTuple j s).filter (fun u => tup u = l)).card : ℝ) = Nmult l := by
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hl
  have hsum : (tup v).sum = s := Finset.Nat.mem_antidiagonalTuple.mp hv
  have hc : (tup v).card = j := by simp [tup]
  have hsets : ((Finset.Nat.antidiagonalTuple j s).filter (fun u => tup u = tup v)) =
      ((Fintype.piFinset fun _ : Fin j => (tup v).toFinset).filter (fun u => tup u = tup v)) := by
    ext u
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.Nat.mem_antidiagonalTuple]
    constructor
    · rintro ⟨_, he⟩
      refine ⟨fun i => ?_, he⟩
      rw [← he]
      exact Multiset.mem_toFinset.mpr (Multiset.mem_map.mpr ⟨i, by simp, rfl⟩)
    · rintro ⟨_, he⟩
      exact ⟨(congrArg Multiset.sum he).trans hsum, he⟩
  rw [hsets, fiber_card _ _ hc, Nmult_eq_countPerms]

/-- Group tail tuples by their multiset of entries, including its multinomial multiplicity. -/
theorem sum_antidiagonal_multisets (j s : ℕ) (f : Multiset ℕ → ℝ) :
    (∑ u ∈ Finset.Nat.antidiagonalTuple j s, f (Finset.univ.val.map u)) =
    ∑ l ∈ multisetsOf j s, Nmult l * f l := by
  classical
  have hm : ∀ u ∈ Finset.Nat.antidiagonalTuple j s, tup u ∈ multisetsOf j s :=
    fun _ hu => Finset.mem_image_of_mem _ hu
  rw [← Finset.sum_fiberwise_of_maps_to' hm f]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.sum_const, nsmul_eq_mul, antidiagonal_fiber_card _ _ hl]

/-- Single out any coordinate and group the remaining entries by their multiset. -/
theorem sum_distinguished_multisets (j m : ℕ) (p : Fin (j+1)) (f : ℕ → Multiset ℕ → ℝ) :
    (∑ u ∈ Finset.Nat.antidiagonalTuple (j+1) m,
      f (u p) (Finset.univ.val.map (fun i : Fin j => u (p.succAbove i)))) =
    ∑ a ∈ Finset.range (m+1), ∑ l ∈ multisetsOf j (m-a), Nmult l * f a l := by
  classical
  simp_rw [← sum_antidiagonal_multisets]
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun u => ⟨u p, p.removeNth u⟩)
    (fun b => p.insertNth b.1 b.2) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    rw [Finset.Nat.mem_antidiagonalTuple, ← Fin.add_sum_removeNth p u] at hu
    simpa only [Finset.mem_sigma, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple] using
      (show u p < m+1 ∧ (∑ i, p.removeNth u i) = m - u p by omega)
  · rintro ⟨a,v⟩ hv
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple] at hv
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_insertNth]
    change a + (∑ i, v i) = m
    omega
  · intro u _; exact p.insertNth_self_removeNth u
  · rintro ⟨a,v⟩ _; simp
  · intro _ _; rfl

/-- The Hermite level weight summed over labels, grouped by its distinguished degree and tail multiset. -/
theorem coeffC_grouped {n : ℕ} (m : ℕ) :
    coeffC (n+1) m = ((n+1 : ℕ) : ℝ) *
      ∑ a ∈ Finset.range (m+1), ∑ l ∈ multisetsOf n (m-a), Nmult l * Bal a l ^ 2 / factDen a l := by
  have hweight (p : Fin (n+1)) : levelWeight p m =
      ∑ a ∈ Finset.range (m+1), ∑ l ∈ multisetsOf n (m-a), Nmult l * Bal a l ^ 2 / factDen a l := by
    unfold levelWeight
    simp_rw [hermCoeff_sq_eq_bal]
    simpa only [mul_div_assoc] using sum_distinguished_multisets n m p
      (fun a l => Bal a l ^ 2 / factDen a l)
  simp [coeffC, hweight, nsmul_eq_mul]

end HermiteLaptop.MaxAgree
end

/- NumericSum.lean -/
section
open Finset
namespace HermiteLaptop.MaxAgree

private def prepend (b : ℕ) : List ℕ ↪ List ℕ :=
  ⟨List.cons b, fun _ _ h => (List.cons.inj h).2⟩

/-- Enumerate nondecreasing tails of length n and sum s, starting at or above lo.
Different first entries give disjoint collections, so no deduplication is needed. -/
def numericTails : ℕ → ℕ → ℕ → Finset (List ℕ)
  | 0, s, _ => if s = 0 then {[]} else ∅
  | n+1, s, lo =>
    (Finset.Icc lo (s/(n+1))).disjiUnion
      (fun b => (numericTails n (s-b) b).map (prepend b)) (by
        intro i _ j _ hij
        apply Finset.disjoint_left.mpr
        intro l hl hl'
        obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hl
        obtain ⟨v, _, hv⟩ := Finset.mem_map.mp hl'
        exact hij (List.cons.inj hv).1.symm)

theorem numericTails_spec {n s lo : ℕ} {l : List ℕ} (h : l ∈ numericTails n s lo) :
    l.length = n ∧ l.sum = s ∧ l.Pairwise (· ≤ ·) ∧ ∀ b ∈ l, lo ≤ b := by
  induction n generalizing s lo l with
  | zero =>
    simp only [numericTails] at h
    split at h <;> simp_all
  | succ n ih =>
    obtain ⟨b, hb, hl⟩ := Finset.mem_disjiUnion.mp h
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hl
    have hbs := Finset.mem_Icc.mp hb
    have hbs' : b ≤ s := hbs.2.trans (Nat.div_le_self s (n+1))
    obtain ⟨hn, hs, hp, hlow⟩ := ih ht
    change (b :: t).length = _ ∧ (b :: t).sum = _ ∧ (b :: t).Pairwise _ ∧ _
    refine ⟨by simp [hn], by simp [hs, Nat.add_sub_of_le hbs'], List.pairwise_cons.mpr ⟨hlow, hp⟩, ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hbs.1
    · exact hbs.1.trans (hlow c hc)

def tableSum (k m : ℕ) (term : ℕ → List ℕ → ℕ) : ℕ :=
  ∑ a ∈ Finset.range (m+1), ∑ l ∈ numericTails (k-1) (m-a) 0, term a l

private theorem list_in_multisetsOf {n s : ℕ} {l : List ℕ} (hlen : l.length = n)
    (hsum : l.sum = s) : (l : Multiset ℕ) ∈ multisetsOf n s := by
  subst n
  apply Finset.mem_image.mpr
  refine ⟨l.get, Finset.Nat.mem_antidiagonalTuple.mpr ?_, ?_⟩
  · change (Finset.univ.val.map l.get).sum = s
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.sum_coe, hsum]
  · simp

/-- Each admissible sorted tuple represents a different multiset. -/
private theorem tail_sum_le {n s : ℕ} (f : Multiset ℕ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ l ∈ numericTails n s 0, f (l : Multiset ℕ)) ≤ ∑ l ∈ multisetsOf n s, f l := by
  have hinj : Set.InjOn (fun l : List ℕ => (l : Multiset ℕ)) (numericTails n s 0) := by
    intro x hx y hy h
    exact (Multiset.coe_eq_coe.mp h).eq_of_pairwise' (numericTails_spec hx).2.2.1
      (numericTails_spec hy).2.2.1
  rw [← Finset.sum_image hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun l _ _ => hf l)
  exact Finset.image_subset_iff.mpr fun _ hu =>
    list_in_multisetsOf (numericTails_spec hu).1 (numericTails_spec hu).2.1

theorem tableSum_le_coeffC {k m : ℕ} (hk : 0 < k) (term : ℕ → List ℕ → ℕ)
    (h : ∀ a ≤ m, ∀ l ∈ numericTails (k-1) (m-a) 0, (term a l : ℝ) / 10^20 ≤
      (k:ℝ) * Nmult (l:Multiset ℕ) * Bal a (l:Multiset ℕ)^2 / factDen a (l:Multiset ℕ)) :
    (tableSum k m term : ℝ) / 10^20 ≤ coeffC k m := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [coeffC_grouped, Finset.mul_sum, tableSum, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro a ha
  rw [Nat.cast_sum, Finset.sum_div, Finset.mul_sum]
  refine (Finset.sum_le_sum fun l hl => h a (by simpa using ha) l hl).trans ?_
  simp only [Nat.succ_sub_one]
  simp_rw [mul_div_assoc, mul_assoc]
  apply tail_sum_le (fun l => ((n+1:ℕ):ℝ) * (Nmult l * (Bal a l ^ 2 / factDen a l)))
  intro l
  have hden : 0 ≤ factDen a l := by
    unfold factDen
    apply mul_nonneg (by positivity)
    apply Multiset.prod_nonneg
    simp
  have hmult : 0 ≤ Nmult l := by unfold Nmult; positivity
  positivity

end HermiteLaptop.MaxAgree
end

section
namespace HermiteLaptop.MaxAgree

private def splitTable : List ℕ := [200000, 338121, 133340, 36608, 44451, 19403, 21276, 13169, 12703, 9536, 8708, 7209, 6493, 5651, 5104, 4567, 4158, 3784, 3476, 3199, 2962]

private def rowBound (k m : ℕ) : Prop :=
  ((splitTable)[m]?).getD 0 * 100000000000000 ≤
    tableSum k m (certTerm k)

set_option maxRecDepth 100000
set_option maxHeartbeats 200000000

private def fastBlock (k m a : ℕ) : ℕ :=
  ∑ l ∈ numericTails (k-1) (m-a) 0, fastCertTerm k a l

private theorem tableSum_blocks (k m : ℕ) :
    tableSum k m (certTerm k) = ∑ a ∈ Finset.range (m+1), fastBlock k m a := by
  simp only [tableSum, fastBlock, fastCertTerm_eq]

private theorem blockStart (f : ℕ → ℕ) : (∑ j ∈ Finset.range 0, f j) = 0 := rfl

private theorem blockStep {f : ℕ → ℕ} {i u v : ℕ} (h : (∑ j ∈ Finset.range i, f j) = u)
    (b : f i = v) : (∑ j ∈ Finset.range (i+1), f j) = u+v := by
  rw [Finset.sum_range_succ, h, b]

private theorem block_5_0_0 : fastBlock 5 0 0 = 20000000000000000000 := by decide +kernel
private theorem row_5_0 : rowBound 5 0 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 20000000000000000000 := by decide +kernel
    _ = _ := (blockStep (blockStart (fastBlock 5 0)) block_5_0_0).symm

private theorem block_5_1_0 : fastBlock 5 1 0 = 6762431834748463132 := by decide +kernel
private theorem block_5_1_1 : fastBlock 5 1 1 = 27049727338993852528 := by decide +kernel
private theorem row_5_1 : rowBound 5 1 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 33812159173742315660 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStart (fastBlock 5 1)) block_5_1_0) block_5_1_1).symm

private theorem block_5_2_0 : fastBlock 5 2 0 = 3733524071493235168 := by decide +kernel
private theorem block_5_2_1 : fastBlock 5 2 1 = 3200163489851344430 := by decide +kernel
private theorem block_5_2_2 : fastBlock 5 2 2 = 6400326979702688861 := by decide +kernel
private theorem row_5_2 : rowBound 5 2 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 13334014541047268459 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStart (fastBlock 5 2)) block_5_2_0) block_5_2_1) block_5_2_2).symm

private theorem block_5_3_0 : fastBlock 5 3 0 = 897969894507419933 := by decide +kernel
private theorem block_5_3_1 : fastBlock 5 3 1 = 2356233111952982654 := by decide +kernel
private theorem block_5_3_2 : fastBlock 5 3 2 = 174258555929896552 := by decide +kernel
private theorem block_5_3_3 : fastBlock 5 3 3 = 232344741239158032 := by decide +kernel
private theorem row_5_3 : rowBound 5 3 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 3660806303629457171 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 3)) block_5_3_0) block_5_3_1) block_5_3_2) block_5_3_3).symm

private theorem block_5_4_0 : fastBlock 5 4 0 = 767422323355651486 := by decide +kernel
private theorem block_5_4_1 : fastBlock 5 4 1 = 451589663511482515 := by decide +kernel
private theorem block_5_4_2 : fastBlock 5 4 2 = 509413506341911044 := by decide +kernel
private theorem block_5_4_3 : fastBlock 5 4 3 = 1358360136505398691 := by decide +kernel
private theorem block_5_4_4 : fastBlock 5 4 4 = 1358360136502845237 := by decide +kernel
private theorem row_5_4 : rowBound 5 4 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 4445145766217288973 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 4)) block_5_4_0) block_5_4_1) block_5_4_2) block_5_4_3) block_5_4_4).symm

private theorem block_5_5_0 : fastBlock 5 5 0 = 290186132925414145 := by decide +kernel
private theorem block_5_5_1 : fastBlock 5 5 1 = 351536882194923758 := by decide +kernel
private theorem block_5_5_2 : fastBlock 5 5 2 = 563323461380148134 := by decide +kernel
private theorem block_5_5_3 : fastBlock 5 5 3 = 708906290147589968 := by decide +kernel
private theorem block_5_5_4 : fastBlock 5 5 4 = 14671196644364835 := by decide +kernel
private theorem block_5_5_5 : fastBlock 5 5 5 = 11736957314854978 := by decide +kernel
private theorem row_5_5 : rowBound 5 5 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 1940360920607295818 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 5)) block_5_5_0) block_5_5_1) block_5_5_2) block_5_5_3) block_5_5_4) block_5_5_5).symm

private theorem block_5_6_0 : fastBlock 5 6 0 = 236212703404904656 := by decide +kernel
private theorem block_5_6_1 : fastBlock 5 6 1 = 239712386799961686 := by decide +kernel
private theorem block_5_6_2 : fastBlock 5 6 2 = 198166391905752804 := by decide +kernel
private theorem block_5_6_3 : fastBlock 5 6 3 = 255853271377396122 := by decide +kernel
private theorem block_5_6_4 : fastBlock 5 6 4 = 405979068794337321 := by decide +kernel
private theorem block_5_6_5 : fastBlock 5 6 5 = 475058086244352073 := by decide +kernel
private theorem block_5_6_6 : fastBlock 5 6 6 = 316705390825441099 := by decide +kernel
private theorem row_5_6 : rowBound 5 6 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 2127687299352145761 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 6)) block_5_6_0) block_5_6_1) block_5_6_2) block_5_6_3) block_5_6_4) block_5_6_5) block_5_6_6).symm

private theorem block_5_7_0 : fastBlock 5 7 0 = 139471909680316941 := by decide +kernel
private theorem block_5_7_1 : fastBlock 5 7 1 = 76618167746213467 := by decide +kernel
private theorem block_5_7_2 : fastBlock 5 7 2 = 190248503209734702 := by decide +kernel
private theorem block_5_7_3 : fastBlock 5 7 3 = 347546368535382268 := by decide +kernel
private theorem block_5_7_4 : fastBlock 5 7 4 = 264655612943704597 := by decide +kernel
private theorem block_5_7_5 : fastBlock 5 7 5 = 202634024517541776 := by decide +kernel
private theorem block_5_7_6 : fastBlock 5 7 6 = 60962369163040356 := by decide +kernel
private theorem block_5_7_7 : fastBlock 5 7 7 = 34835639518689826 := by decide +kernel
private theorem row_5_7 : rowBound 5 7 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 1316972595314623933 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 7)) block_5_7_0) block_5_7_1) block_5_7_2) block_5_7_3) block_5_7_4) block_5_7_5) block_5_7_6) block_5_7_7).symm

private theorem block_5_8_0 : fastBlock 5 8 0 = 94841671741853384 := by decide +kernel
private theorem block_5_8_1 : fastBlock 5 8 1 = 110992787682956183 := by decide +kernel
private theorem block_5_8_2 : fastBlock 5 8 2 = 130925711304259005 := by decide +kernel
private theorem block_5_8_3 : fastBlock 5 8 3 = 114159786407255406 := by decide +kernel
private theorem block_5_8_4 : fastBlock 5 8 4 = 125479179084713159 := by decide +kernel
private theorem block_5_8_5 : fastBlock 5 8 5 = 226862644994086867 := by decide +kernel
private theorem block_5_8_6 : fastBlock 5 8 6 = 239226910936243283 := by decide +kernel
private theorem block_5_8_7 : fastBlock 5 8 7 = 151901176461402881 := by decide +kernel
private theorem block_5_8_8 : fastBlock 5 8 8 = 75950588225494040 := by decide +kernel
private theorem row_5_8 : rowBound 5 8 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 1270340456838264208 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 8)) block_5_8_0) block_5_8_1) block_5_8_2) block_5_8_3) block_5_8_4) block_5_8_5) block_5_8_6) block_5_8_7) block_5_8_8).symm

private theorem block_5_9_0 : fastBlock 5 9 0 = 76564017876191584 := by decide +kernel
private theorem block_5_9_1 : fastBlock 5 9 1 = 32075136237023145 := by decide +kernel
private theorem block_5_9_2 : fastBlock 5 9 2 = 61939443051018324 := by decide +kernel
private theorem block_5_9_3 : fastBlock 5 9 3 = 134215326729715395 := by decide +kernel
private theorem block_5_9_4 : fastBlock 5 9 4 = 191324714752966923 := by decide +kernel
private theorem block_5_9_5 : fastBlock 5 9 5 = 189780373520888170 := by decide +kernel
private theorem block_5_9_6 : fastBlock 5 9 6 = 100977588178023371 := by decide +kernel
private theorem block_5_9_7 : fastBlock 5 9 7 = 83410057316077158 := by decide +kernel
private theorem block_5_9_8 : fastBlock 5 9 8 = 57732772183187375 := by decide +kernel
private theorem block_5_9_9 : fastBlock 5 9 9 = 25659009852892601 := by decide +kernel
private theorem row_5_9 : rowBound 5 9 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 953678439697984046 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 9)) block_5_9_0) block_5_9_1) block_5_9_2) block_5_9_3) block_5_9_4) block_5_9_5) block_5_9_6) block_5_9_7) block_5_9_8) block_5_9_9).symm

private theorem block_5_10_0 : fastBlock 5 10 0 = 47465516064381194 := by decide +kernel
private theorem block_5_10_1 : fastBlock 5 10 1 = 49174957110438426 := by decide +kernel
private theorem block_5_10_2 : fastBlock 5 10 2 = 77030528459221970 := by decide +kernel
private theorem block_5_10_3 : fastBlock 5 10 3 = 84461755362268934 := by decide +kernel
private theorem block_5_10_4 : fastBlock 5 10 4 = 65017763804249009 := by decide +kernel
private theorem block_5_10_5 : fastBlock 5 10 5 = 82644785321611688 := by decide +kernel
private theorem block_5_10_6 : fastBlock 5 10 6 = 129590956203811671 := by decide +kernel
private theorem block_5_10_7 : fastBlock 5 10 7 = 159253615488595839 := by decide +kernel
private theorem block_5_10_8 : fastBlock 5 10 8 = 112866216208097654 := by decide +kernel
private theorem block_5_10_9 : fastBlock 5 10 9 = 45217439969459366 := by decide +kernel
private theorem block_5_10_10 : fastBlock 5 10 10 = 18086975981877819 := by decide +kernel
private theorem row_5_10 : rowBound 5 10 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 870810509974013570 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 10)) block_5_10_0) block_5_10_1) block_5_10_2) block_5_10_3) block_5_10_4) block_5_10_5) block_5_10_6) block_5_10_7) block_5_10_8) block_5_10_9) block_5_10_10).symm

private theorem block_5_11_0 : fastBlock 5 11 0 = 45287913856992239 := by decide +kernel
private theorem block_5_11_1 : fastBlock 5 11 1 = 20378228127020831 := by decide +kernel
private theorem block_5_11_2 : fastBlock 5 11 2 = 27574354768050230 := by decide +kernel
private theorem block_5_11_3 : fastBlock 5 11 3 = 47407843723910074 := by decide +kernel
private theorem block_5_11_4 : fastBlock 5 11 4 = 92071657293158155 := by decide +kernel
private theorem block_5_11_5 : fastBlock 5 11 5 = 134101875258664185 := by decide +kernel
private theorem block_5_11_6 : fastBlock 5 11 6 = 120733660957088706 := by decide +kernel
private theorem block_5_11_7 : fastBlock 5 11 7 = 82719499953591983 := by decide +kernel
private theorem block_5_11_8 : fastBlock 5 11 8 = 47633935756354275 := by decide +kernel
private theorem block_5_11_9 : fastBlock 5 11 9 = 50358568081855265 := by decide +kernel
private theorem block_5_11_10 : fastBlock 5 11 10 = 38617084230655359 := by decide +kernel
private theorem block_5_11_11 : fastBlock 5 11 11 = 14042576073427874 := by decide +kernel
private theorem row_5_11 : rowBound 5 11 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 720927198080769176 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 11)) block_5_11_0) block_5_11_1) block_5_11_2) block_5_11_3) block_5_11_4) block_5_11_5) block_5_11_6) block_5_11_7) block_5_11_8) block_5_11_9) block_5_11_10) block_5_11_11).symm

private theorem block_5_12_0 : fastBlock 5 12 0 = 28010346758845621 := by decide +kernel
private theorem block_5_12_1 : fastBlock 5 12 1 = 22779674066432149 := by decide +kernel
private theorem block_5_12_2 : fastBlock 5 12 2 = 40950120786098289 := by decide +kernel
private theorem block_5_12_3 : fastBlock 5 12 3 = 56980969152036129 := by decide +kernel
private theorem block_5_12_4 : fastBlock 5 12 4 = 53943679262246321 := by decide +kernel
private theorem block_5_12_5 : fastBlock 5 12 5 = 46868776184505966 := by decide +kernel
private theorem block_5_12_6 : fastBlock 5 12 6 = 52679147455763819 := by decide +kernel
private theorem block_5_12_7 : fastBlock 5 12 7 = 86132124388072906 := by decide +kernel
private theorem block_5_12_8 : fastBlock 5 12 8 = 107061126897882003 := by decide +kernel
private theorem block_5_12_9 : fastBlock 5 12 9 = 90723076100858507 := by decide +kernel
private theorem block_5_12_10 : fastBlock 5 12 10 = 46668828955415104 := by decide +kernel
private theorem block_5_12_11 : fastBlock 5 12 11 = 12400322541893350 := by decide +kernel
private theorem block_5_12_12 : fastBlock 5 12 12 = 4133440841086957 := by decide +kernel
private theorem row_5_12 : rowBound 5 12 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 649331633391137121 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 12)) block_5_12_0) block_5_12_1) block_5_12_2) block_5_12_3) block_5_12_4) block_5_12_5) block_5_12_6) block_5_12_7) block_5_12_8) block_5_12_9) block_5_12_10) block_5_12_11) block_5_12_12).symm

private theorem block_5_13_0 : fastBlock 5 13 0 = 28517287056779746 := by decide +kernel
private theorem block_5_13_1 : fastBlock 5 13 1 = 14033144459847063 := by decide +kernel
private theorem block_5_13_2 : fastBlock 5 13 2 = 17287934854396568 := by decide +kernel
private theorem block_5_13_3 : fastBlock 5 13 3 = 19837571154266694 := by decide +kernel
private theorem block_5_13_4 : fastBlock 5 13 4 = 37717678543360315 := by decide +kernel
private theorem block_5_13_5 : fastBlock 5 13 5 = 70670071303931549 := by decide +kernel
private theorem block_5_13_6 : fastBlock 5 13 6 = 93699245135389045 := by decide +kernel
private theorem block_5_13_7 : fastBlock 5 13 7 = 90003937855860917 := by decide +kernel
private theorem block_5_13_8 : fastBlock 5 13 8 = 59925631901092297 := by decide +kernel
private theorem block_5_13_9 : fastBlock 5 13 9 = 38763141209809212 := by decide +kernel
private theorem block_5_13_10 : fastBlock 5 13 10 = 32127489142596149 := by decide +kernel
private theorem block_5_13_11 : fastBlock 5 13 11 = 33429614695238251 := by decide +kernel
private theorem block_5_13_12 : fastBlock 5 13 12 = 22272839874198386 := by decide +kernel
private theorem block_5_13_13 : fastBlock 5 13 13 = 6853181484078256 := by decide +kernel
private theorem row_5_13 : rowBound 5 13 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 565138768670844448 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 13)) block_5_13_0) block_5_13_1) block_5_13_2) block_5_13_3) block_5_13_4) block_5_13_5) block_5_13_6) block_5_13_7) block_5_13_8) block_5_13_9) block_5_13_10) block_5_13_11) block_5_13_12) block_5_13_13).symm

private theorem block_5_14_0 : fastBlock 5 14 0 = 18435752969327545 := by decide +kernel
private theorem block_5_14_1 : fastBlock 5 14 1 = 11705809740177342 := by decide +kernel
private theorem block_5_14_2 : fastBlock 5 14 2 = 21287066146358509 := by decide +kernel
private theorem block_5_14_3 : fastBlock 5 14 3 = 33909211575015676 := by decide +kernel
private theorem block_5_14_4 : fastBlock 5 14 4 = 41160413408710353 := by decide +kernel
private theorem block_5_14_5 : fastBlock 5 14 5 = 39998850015742125 := by decide +kernel
private theorem block_5_14_6 : fastBlock 5 14 6 = 32202019647335705 := by decide +kernel
private theorem block_5_14_7 : fastBlock 5 14 7 = 38628132533883050 := by decide +kernel
private theorem block_5_14_8 : fastBlock 5 14 8 = 58709723540236580 := by decide +kernel
private theorem block_5_14_9 : fastBlock 5 14 9 = 76964620612560219 := by decide +kernel
private theorem block_5_14_10 : fastBlock 5 14 10 = 71015152611448235 := by decide +kernel
private theorem block_5_14_11 : fastBlock 5 14 11 = 44956135680925487 := by decide +kernel
private theorem block_5_14_12 : fastBlock 5 14 12 = 17640132845285192 := by decide +kernel
private theorem block_5_14_13 : fastBlock 5 14 13 = 3016130445293441 := by decide +kernel
private theorem block_5_14_14 : fastBlock 5 14 14 = 861751549765962 := by decide +kernel
private theorem row_5_14 : rowBound 5 14 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 510490903322065421 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 14)) block_5_14_0) block_5_14_1) block_5_14_2) block_5_14_3) block_5_14_4) block_5_14_5) block_5_14_6) block_5_14_7) block_5_14_8) block_5_14_9) block_5_14_10) block_5_14_11) block_5_14_12) block_5_14_13) block_5_14_14).symm

private theorem block_5_15_0 : fastBlock 5 15 0 = 19003398441793282 := by decide +kernel
private theorem block_5_15_1 : fastBlock 5 15 1 = 9655110247002004 := by decide +kernel
private theorem block_5_15_2 : fastBlock 5 15 2 = 12357090299233757 := by decide +kernel
private theorem block_5_15_3 : fastBlock 5 15 3 = 11694933365191062 := by decide +kernel
private theorem block_5_15_4 : fastBlock 5 15 4 = 16404554164073810 := by decide +kernel
private theorem block_5_15_5 : fastBlock 5 15 5 = 31754734499074987 := by decide +kernel
private theorem block_5_15_6 : fastBlock 5 15 6 = 54200283795954356 := by decide +kernel
private theorem block_5_15_7 : fastBlock 5 15 7 = 71239287202560630 := by decide +kernel
private theorem block_5_15_8 : fastBlock 5 15 8 = 67138055504810531 := by decide +kernel
private theorem block_5_15_9 : fastBlock 5 15 9 = 48301466770309988 := by decide +kernel
private theorem block_5_15_10 : fastBlock 5 15 10 = 29665529376920291 := by decide +kernel
private theorem block_5_15_11 : fastBlock 5 15 11 = 24459226946596485 := by decide +kernel
private theorem block_5_15_12 : fastBlock 5 15 12 = 24429985082723530 := by decide +kernel
private theorem block_5_15_13 : fastBlock 5 15 13 = 21339624924249551 := by decide +kernel
private theorem block_5_15_14 : fastBlock 5 15 14 = 11895959810967333 := by decide +kernel
private theorem block_5_15_15 : fastBlock 5 15 15 = 3172255927290630 := by decide +kernel
private theorem row_5_15 : rowBound 5 15 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 456711496358752227 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 15)) block_5_15_0) block_5_15_1) block_5_15_2) block_5_15_3) block_5_15_4) block_5_15_5) block_5_15_6) block_5_15_7) block_5_15_8) block_5_15_9) block_5_15_10) block_5_15_11) block_5_15_12) block_5_15_13) block_5_15_14) block_5_15_15).symm

private theorem block_5_16_0 : fastBlock 5 16 0 = 13009847137745841 := by decide +kernel
private theorem block_5_16_1 : fastBlock 5 16 1 = 6828587349235252 := by decide +kernel
private theorem block_5_16_2 : fastBlock 5 16 2 = 11538862335609382 := by decide +kernel
private theorem block_5_16_3 : fastBlock 5 16 3 = 18943861636140902 := by decide +kernel
private theorem block_5_16_4 : fastBlock 5 16 4 = 27223553992649056 := by decide +kernel
private theorem block_5_16_5 : fastBlock 5 16 5 = 32487607626513963 := by decide +kernel
private theorem block_5_16_6 : fastBlock 5 16 6 = 29031092813289315 := by decide +kernel
private theorem block_5_16_7 : fastBlock 5 16 7 = 24892783534879626 := by decide +kernel
private theorem block_5_16_8 : fastBlock 5 16 8 = 28124418003363607 := by decide +kernel
private theorem block_5_16_9 : fastBlock 5 16 9 = 43007921075921934 := by decide +kernel
private theorem block_5_16_10 : fastBlock 5 16 10 = 56635935116883898 := by decide +kernel
private theorem block_5_16_11 : fastBlock 5 16 11 = 56430582756300757 := by decide +kernel
private theorem block_5_16_12 : fastBlock 5 16 12 = 40497069851134142 := by decide +kernel
private theorem block_5_16_13 : fastBlock 5 16 13 = 20243650605562443 := by decide +kernel
private theorem block_5_16_14 : fastBlock 5 16 14 = 6240463536429896 := by decide +kernel
private theorem block_5_16_15 : fastBlock 5 16 15 = 591663765719730 := by decide +kernel
private theorem block_5_16_16 : fastBlock 5 16 16 = 147915936230490 := by decide +kernel
private theorem row_5_16 : rowBound 5 16 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 415875817073610234 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 16)) block_5_16_0) block_5_16_1) block_5_16_2) block_5_16_3) block_5_16_4) block_5_16_5) block_5_16_6) block_5_16_7) block_5_16_8) block_5_16_9) block_5_16_10) block_5_16_11) block_5_16_12) block_5_16_13) block_5_16_14) block_5_16_15) block_5_16_16).symm

private theorem block_5_17_0 : fastBlock 5 17 0 = 13310049460982101 := by decide +kernel
private theorem block_5_17_1 : fastBlock 5 17 1 = 6666004410317328 := by decide +kernel
private theorem block_5_17_2 : fastBlock 5 17 2 = 8973949464993210 := by decide +kernel
private theorem block_5_17_3 : fastBlock 5 17 3 = 8548118406306650 := by decide +kernel
private theorem block_5_17_4 : fastBlock 5 17 4 = 9293282137298333 := by decide +kernel
private theorem block_5_17_5 : fastBlock 5 17 5 = 14320087089133636 := by decide +kernel
private theorem block_5_17_6 : fastBlock 5 17 6 = 26471224956875292 := by decide +kernel
private theorem block_5_17_7 : fastBlock 5 17 7 = 43702063489436986 := by decide +kernel
private theorem block_5_17_8 : fastBlock 5 17 8 = 55057066987427000 := by decide +kernel
private theorem block_5_17_9 : fastBlock 5 17 9 = 52975331815713001 := by decide +kernel
private theorem block_5_17_10 : fastBlock 5 17 10 = 38744802061377196 := by decide +kernel
private theorem block_5_17_11 : fastBlock 5 17 11 = 24764363702738747 := by decide +kernel
private theorem block_5_17_12 : fastBlock 5 17 12 = 18495713000961176 := by decide +kernel
private theorem block_5_17_13 : fastBlock 5 17 13 = 18870379593186407 := by decide +kernel
private theorem block_5_17_14 : fastBlock 5 17 14 = 17843533097597217 := by decide +kernel
private theorem block_5_17_15 : fastBlock 5 17 15 = 12867895742855210 := by decide +kernel
private theorem block_5_17_16 : fastBlock 5 17 16 = 6082620263607568 := by decide +kernel
private theorem block_5_17_17 : fastBlock 5 17 17 = 1431204737136242 := by decide +kernel
private theorem row_5_17 : rowBound 5 17 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 378417690417943300 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 17)) block_5_17_0) block_5_17_1) block_5_17_2) block_5_17_3) block_5_17_4) block_5_17_5) block_5_17_6) block_5_17_7) block_5_17_8) block_5_17_9) block_5_17_10) block_5_17_11) block_5_17_12) block_5_17_13) block_5_17_14) block_5_17_15) block_5_17_16) block_5_17_17).symm

private theorem block_5_18_0 : fastBlock 5 18 0 = 9617289061124853 := by decide +kernel
private theorem block_5_18_1 : fastBlock 5 18 1 = 4461930849136624 := by decide +kernel
private theorem block_5_18_2 : fastBlock 5 18 2 = 6800823725745295 := by decide +kernel
private theorem block_5_18_3 : fastBlock 5 18 3 = 10538758219778893 := by decide +kernel
private theorem block_5_18_4 : fastBlock 5 18 4 = 16462389400457575 := by decide +kernel
private theorem block_5_18_5 : fastBlock 5 18 5 = 23084112997830745 := by decide +kernel
private theorem block_5_18_6 : fastBlock 5 18 6 = 25187311075116650 := by decide +kernel
private theorem block_5_18_7 : fastBlock 5 18 7 = 22809778456996278 := by decide +kernel
private theorem block_5_18_8 : fastBlock 5 18 8 = 18997455071012004 := by decide +kernel
private theorem block_5_18_9 : fastBlock 5 18 9 = 21907743302235757 := by decide +kernel
private theorem block_5_18_10 : fastBlock 5 18 10 = 32167819887977787 := by decide +kernel
private theorem block_5_18_11 : fastBlock 5 18 11 = 43254404630496506 := by decide +kernel
private theorem block_5_18_12 : fastBlock 5 18 12 = 45123100851949338 := by decide +kernel
private theorem block_5_18_13 : fastBlock 5 18 13 = 35654700205923132 := by decide +kernel
private theorem block_5_18_14 : fastBlock 5 18 14 = 20800360887359700 := by decide +kernel
private theorem block_5_18_15 : fastBlock 5 18 15 = 8530750399947876 := by decide +kernel
private theorem block_5_18_16 : fastBlock 5 18 16 = 2119193457702865 := by decide +kernel
private theorem block_5_18_17 : fastBlock 5 18 17 = 69320286916511 := by decide +kernel
private theorem block_5_18_18 : fastBlock 5 18 18 = 15404504765471 := by decide +kernel
private theorem row_5_18 : rowBound 5 18 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 347602647272473860 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 18)) block_5_18_0) block_5_18_1) block_5_18_2) block_5_18_3) block_5_18_4) block_5_18_5) block_5_18_6) block_5_18_7) block_5_18_8) block_5_18_9) block_5_18_10) block_5_18_11) block_5_18_12) block_5_18_13) block_5_18_14) block_5_18_15) block_5_18_16) block_5_18_17) block_5_18_18).symm

private theorem block_5_19_0 : fastBlock 5 19 0 = 9723878056268739 := by decide +kernel
private theorem block_5_19_1 : fastBlock 5 19 1 = 4682795411238073 := by decide +kernel
private theorem block_5_19_2 : fastBlock 5 19 2 = 6491624885277757 := by decide +kernel
private theorem block_5_19_3 : fastBlock 5 19 3 = 6548940048065549 := by decide +kernel
private theorem block_5_19_4 : fastBlock 5 19 4 = 6716419383907122 := by decide +kernel
private theorem block_5_19_5 : fastBlock 5 19 5 = 7847064541453333 := by decide +kernel
private theorem block_5_19_6 : fastBlock 5 19 6 = 12469551879218155 := by decide +kernel
private theorem block_5_19_7 : fastBlock 5 19 7 = 22794964454670245 := by decide +kernel
private theorem block_5_19_8 : fastBlock 5 19 8 = 35574395828009709 := by decide +kernel
private theorem block_5_19_9 : fastBlock 5 19 9 = 44213144545168937 := by decide +kernel
private theorem block_5_19_10 : fastBlock 5 19 10 = 42454076568702047 := by decide +kernel
private theorem block_5_19_11 : fastBlock 5 19 11 = 32220044601058635 := by decide +kernel
private theorem block_5_19_12 : fastBlock 5 19 12 = 20761913744812265 := by decide +kernel
private theorem block_5_19_13 : fastBlock 5 19 13 = 14989416419581281 := by decide +kernel
private theorem block_5_19_14 : fastBlock 5 19 14 = 14476280379132477 := by decide +kernel
private theorem block_5_19_15 : fastBlock 5 19 15 = 14792054322974688 := by decide +kernel
private theorem block_5_19_16 : fastBlock 5 19 16 = 12154734476169014 := by decide +kernel
private theorem block_5_19_17 : fastBlock 5 19 17 = 7403741621036420 := by decide +kernel
private theorem block_5_19_18 : fastBlock 5 19 18 = 3031224449226905 := by decide +kernel
private theorem block_5_19_19 : fastBlock 5 19 19 = 638152473923460 := by decide +kernel
private theorem row_5_19 : rowBound 5 19 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 319984418089894811 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 19)) block_5_19_0) block_5_19_1) block_5_19_2) block_5_19_3) block_5_19_4) block_5_19_5) block_5_19_6) block_5_19_7) block_5_19_8) block_5_19_9) block_5_19_10) block_5_19_11) block_5_19_12) block_5_19_13) block_5_19_14) block_5_19_15) block_5_19_16) block_5_19_17) block_5_19_18) block_5_19_19).symm

private theorem block_5_20_0 : fastBlock 5 20 0 = 7350971937681265 := by decide +kernel
private theorem block_5_20_1 : fastBlock 5 20 1 = 3167165199156045 := by decide +kernel
private theorem block_5_20_2 : fastBlock 5 20 2 = 4412477642233953 := by decide +kernel
private theorem block_5_20_3 : fastBlock 5 20 3 = 6124355914995868 := by decide +kernel
private theorem block_5_20_4 : fastBlock 5 20 4 = 9612576007181885 := by decide +kernel
private theorem block_5_20_5 : fastBlock 5 20 5 = 14879781276918849 := by decide +kernel
private theorem block_5_20_6 : fastBlock 5 20 6 = 19117705923808808 := by decide +kernel
private theorem block_5_20_7 : fastBlock 5 20 7 = 20531835932276134 := by decide +kernel
private theorem block_5_20_8 : fastBlock 5 20 8 = 17888040717825238 := by decide +kernel
private theorem block_5_20_9 : fastBlock 5 20 9 = 15336763088674862 := by decide +kernel
private theorem block_5_20_10 : fastBlock 5 20 10 = 17191574591602523 := by decide +kernel
private theorem block_5_20_11 : fastBlock 5 20 11 = 25028873077710667 := by decide +kernel
private theorem block_5_20_12 : fastBlock 5 20 12 = 33676768840974151 := by decide +kernel
private theorem block_5_20_13 : fastBlock 5 20 13 = 36606531095591072 := by decide +kernel
private theorem block_5_20_14 : fastBlock 5 20 14 = 30993577091584855 := by decide +kernel
private theorem block_5_20_15 : fastBlock 5 20 15 = 20238465511558952 := by decide +kernel
private theorem block_5_20_16 : fastBlock 5 20 16 = 9933133862134792 := by decide +kernel
private theorem block_5_20_17 : fastBlock 5 20 17 = 3459719072794031 := by decide +kernel
private theorem block_5_20_18 : fastBlock 5 20 18 = 729475347711785 := by decide +kernel
private theorem block_5_20_19 : fastBlock 5 20 19 = 171140061409 := by decide +kernel
private theorem block_5_20_20 : fastBlock 5 20 20 = 34227683725 := by decide +kernel
private theorem row_5_20 : rowBound 5 20 := by
  unfold rowBound
  rw [tableSum_blocks]
  calc
    _ ≤ 296279997500160869 := by decide +kernel
    _ = _ := (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStep (blockStart (fastBlock 5 20)) block_5_20_0) block_5_20_1) block_5_20_2) block_5_20_3) block_5_20_4) block_5_20_5) block_5_20_6) block_5_20_7) block_5_20_8) block_5_20_9) block_5_20_10) block_5_20_11) block_5_20_12) block_5_20_13) block_5_20_14) block_5_20_15) block_5_20_16) block_5_20_17) block_5_20_18) block_5_20_19) block_5_20_20).symm

private theorem splitRows (m : ℕ) (hm : m ≤ 20) : rowBound 5 m := by
  interval_cases m
  · exact row_5_0
  · exact row_5_1
  · exact row_5_2
  · exact row_5_3
  · exact row_5_4
  · exact row_5_5
  · exact row_5_6
  · exact row_5_7
  · exact row_5_8
  · exact row_5_9
  · exact row_5_10
  · exact row_5_11
  · exact row_5_12
  · exact row_5_13
  · exact row_5_14
  · exact row_5_15
  · exact row_5_16
  · exact row_5_17
  · exact row_5_18
  · exact row_5_19
  · exact row_5_20

end HermiteLaptop.MaxAgree
end

open HermiteLaptop.MaxAgree

theorem solution (m : ℕ) (hm : m ≤ 20) :
    (([200000, 338121, 133340, 36608, 44451, 19403, 21276, 13169, 12703, 9536, 8708, 7209, 6493, 5651, 5104, 4567, 4158, 3784, 3476, 3199, 2962][m]?.getD 0 : ℕ) : ℝ) / 1000000 ≤ HermiteLaptop.MaxAgree.coeffC 5 m := by
  have hsum := tableSum_le_coeffC (k := 5) (m := m) (by decide) (certTerm 5) (fun a _ l hl => by
    have hlen := (numericTails_spec hl).1
    exact certTerm_le 5 a l rfl (by omega))
  apply le_trans _ hsum
  have hn : (splitTable[m]?).getD 0 * 100000000000000 ≤ tableSum 5 m (certTerm 5) :=
    splitRows m hm
  have hr := (Nat.cast_le (α := ℝ)).mpr hn
  push_cast at hr
  change (((splitTable[m]?).getD 0 : ℕ) : ℝ) / 1000000 ≤ _
  linarith
