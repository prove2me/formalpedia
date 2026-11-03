-- Prove2me | solution 1 for Grothendieck.ErCoeff_decay_and_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T16:01:28.374617+00:00
-- url     : https://prove2.me/submissions/7a74a8bb-ecb1-40bc-a08f-93870c0e0cda

import Mathlib
import Definitions.Def_Grothendieck_Series

set_option autoImplicit false

noncomputable section

open MeasureTheory intervalIntegral
open scoped BigOperators Real ENNReal

/-! ## Part I: the coefficient bound (from the published Vietoris leaf) -/

namespace AuxCoeff

/-- The constant `c = r/2 + 1`. -/
def cc (r : ℕ) : ℝ := (r : ℝ)/2 + 1

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

end AuxCoeff

/-! ## Part II: the moment representation (published leaf 5, verbatim) -/

noncomputable section

open MeasureTheory intervalIntegral
open scoped BigOperators ENNReal

namespace Leaf5

/-- The real Beta integral, from the complex one. -/
theorem integral_rpow_mul_rpow_one_sub {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ x in (0 : ℝ)..1, x ^ (p - 1) * (1 - x) ^ (q - 1)
      = Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by
  have key := Complex.betaIntegral_eq_Gamma_mul_div (p : ℂ) (q : ℂ)
    (by simpa using hp) (by simpa using hq)
  have hcongr : (∫ x in (0 : ℝ)..1, ((x ^ (p - 1) * (1 - x) ^ (q - 1) : ℝ) : ℂ))
      = Complex.betaIntegral (p : ℂ) (q : ℂ) := by
    rw [Complex.betaIntegral]
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx0 : (0 : ℝ) ≤ x := by
      simp only [Set.uIcc_of_le zero_le_one, Set.mem_Icc] at hx; exact hx.1
    have hx1 : (0 : ℝ) ≤ 1 - x := by
      simp only [Set.uIcc_of_le zero_le_one, Set.mem_Icc] at hx; linarith [hx.2]
    have e1 : ((p : ℂ) - 1) = ((p - 1 : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((q : ℂ) - 1) = ((q - 1 : ℝ) : ℂ) := by push_cast; ring
    have e3 : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, e3, ← Complex.ofReal_cpow hx0, ← Complex.ofReal_cpow hx1, ← Complex.ofReal_mul]
  have key3 : ((∫ x in (0 : ℝ)..1, x ^ (p - 1) * (1 - x) ^ (q - 1) : ℝ) : ℂ)
      = Complex.Gamma (p : ℂ) * Complex.Gamma (q : ℂ) / Complex.Gamma ((p : ℂ) + (q : ℂ)) := by
    rw [← intervalIntegral.integral_ofReal, hcongr, key]
  rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_div] at key3
  exact Complex.ofReal_inj.mp key3

/-- The same over the open set `Ioo 0 1`. -/
theorem integral_Ioo_rpow_mul_rpow_one_sub {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ x in Set.Ioo (0 : ℝ) 1, x ^ (p - 1) * (1 - x) ^ (q - 1)
      = Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact integral_rpow_mul_rpow_one_sub hp hq

/-- `Γ (a + k) = Γ a * (a)_k` for `a > 0`. -/
theorem Gamma_add_nat_eq {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Real.Gamma (a + k) = Real.Gamma a * Grothendieck.risingFact a k := by
  induction k with
  | zero => simp [Grothendieck.risingFact]
  | succ k ih =>
    have haz : a + (k : ℝ) ≠ 0 := by positivity
    push_cast
    rw [show a + ((k : ℝ) + 1) = (a + (k : ℝ)) + 1 by ring, Real.Gamma_add_one haz, ih]
    simp only [Grothendieck.risingFact, Finset.prod_range_succ]
    ring

/-- The density of the Beta-type measure. -/
def betaWeight (b : ℝ) (x : ℝ) : ℝ :=
  x ^ (-(1 / 2) : ℝ) * (1 - x) ^ (b - 1) / ProbabilityTheory.beta (1 / 2) b

theorem integral_betaWeight_Ioo {b : ℝ} (hb : 0 < b) (k : ℕ) :
    ∫ x in Set.Ioo (0 : ℝ) 1, x ^ k * betaWeight b x
      = Real.Gamma ((k : ℝ) + 1 / 2) * Real.Gamma (b + 1 / 2) /
          (Real.Gamma (1 / 2) * Real.Gamma ((k : ℝ) + b + 1 / 2)) := by
  have hp : (0:ℝ) < (k:ℝ) + 1/2 := by positivity
  have hq : (0:ℝ) < b := hb
  -- pointwise rewriting on `Ioo 0 1`
  have hcongr : ∫ x in Set.Ioo (0:ℝ) 1, x ^ k * betaWeight b x
      = (∫ x in Set.Ioo (0:ℝ) 1, x ^ ((k:ℝ) + 1/2 - 1) * (1 - x) ^ (b - 1))
          / ProbabilityTheory.beta (1/2) b := by
    rw [← MeasureTheory.integral_div]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    have hx0 : 0 < x := hx.1
    have hsplit : x ^ ((k:ℝ) + 1/2 - 1) = x ^ (k:ℝ) * x ^ (-(1/2) : ℝ) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    rw [hsplit, Real.rpow_natCast]
    simp only [betaWeight]
    field_simp
  rw [hcongr]
  rw [integral_Ioo_rpow_mul_rpow_one_sub hp hq]
  simp only [ProbabilityTheory.beta]
  have h1 : Real.Gamma ((k:ℝ) + 1/2) ≠ 0 := (Real.Gamma_pos_of_pos hp).ne'
  have h2 : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
  have h3 : Real.Gamma ((k:ℝ) + 1/2 + b) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have h4 : Real.Gamma (1/2) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h5 : Real.Gamma (1/2 + b) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have h6 : Real.Gamma (b + 1/2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [show (k:ℝ) + 1/2 + b = (k:ℝ) + b + 1/2 by ring]
  rw [show (1:ℝ)/2 + b = b + 1/2 by ring]
  field_simp



/-- `risingFact 1 k = k!`. -/
theorem risingFact_one (k : ℕ) : Grothendieck.risingFact 1 k = (k.factorial : ℝ) := by
  induction k with
  | zero => simp [Grothendieck.risingFact]
  | succ k ih =>
    simp only [Grothendieck.risingFact, Finset.prod_range_succ] at ih ⊢
    rw [ih, Nat.factorial_succ]
    push_cast
    ring

/-- `risingFact a k` is positive for `a > 0`. -/
theorem risingFact_pos {a : ℝ} (ha : 0 < a) (k : ℕ) : 0 < Grothendieck.risingFact a k := by
  unfold Grothendieck.risingFact
  exact Finset.prod_pos fun i _ => by positivity

/-- The measure on `[0,1]` with density `x^(-1/2)(1-x)^(b-1)/B(1/2,b)`. -/
def nu (b : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity fun x => ENNReal.ofReal (betaWeight b x)

theorem measurable_betaWeight (b : ℝ) : Measurable fun x : ℝ => ENNReal.ofReal (betaWeight b x) := by
  unfold betaWeight
  fun_prop

/-- Moments of `nu b`. -/
theorem integral_nu {b : ℝ} (hb : 0 < b) (k : ℕ) :
    ∫ x, x ^ k ∂(nu b)
      = Real.Gamma ((k : ℝ) + 1 / 2) * Real.Gamma (b + 1 / 2) /
          (Real.Gamma (1 / 2) * Real.Gamma ((k : ℝ) + b + 1 / 2)) := by
  rw [nu, integral_withDensity_eq_integral_toReal_smul (measurable_betaWeight b)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have hbpos : 0 < ProbabilityTheory.beta (1 / 2) b := ProbabilityTheory.beta_pos (by norm_num) hb
  trans ∫ x in Set.Ioo (0 : ℝ) 1, x ^ k * betaWeight b x
  · refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : 0 < x := hx.1
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hpos : 0 ≤ betaWeight b x := by
      unfold betaWeight
      positivity
    rw [ENNReal.toReal_ofReal hpos, smul_eq_mul, mul_comm]
  · exact integral_betaWeight_Ioo hb k

theorem measure_univ_nu_toReal {b : ℝ} (hb : 0 < b) : ((nu b) Set.univ).toReal = 1 := by
  have h := integral_nu hb 0
  simp only [Nat.cast_zero, zero_add, pow_zero] at h
  rw [MeasureTheory.integral_const] at h
  rw [smul_eq_mul, mul_one] at h
  have h1 : Real.Gamma (1 / 2) * Real.Gamma (b + 1 / 2) /
      (Real.Gamma (1 / 2) * Real.Gamma (b + 1 / 2)) = 1 := by
    field_simp
  rw [h1, Measure.real] at h
  exact h

theorem isFiniteMeasure_nu {b : ℝ} (hb : 0 < b) : IsFiniteMeasure (nu b) := by
  constructor
  by_contra htop
  rw [not_lt_top_iff] at htop
  have h := measure_univ_nu_toReal hb
  rw [htop] at h
  simp at h

theorem measure_univ_nu {b : ℝ} (hb : 0 < b) : (nu b) Set.univ = 1 := by
  rw [← ENNReal.toReal_eq_one_iff]
  exact measure_univ_nu_toReal hb

theorem isProbabilityMeasure_nu {b : ℝ} (hb : 0 < b) : IsProbabilityMeasure (nu b) :=
  ⟨measure_univ_nu hb⟩

/-- Each single factor `k ↦ (1/2)_k/(b+1/2)_k` is itself a moment sequence on `[0,1]`. -/
theorem integral_nu_risingFact {b : ℝ} (hb : 0 < b) (k : ℕ) :
    ∫ x, x ^ k ∂(nu b) = Grothendieck.risingFact (1 / 2) k /
      Grothendieck.risingFact (b + 1 / 2) k := by
  rw [integral_nu hb k]
  have h1 : Real.Gamma ((k : ℝ) + 1 / 2) =
      Real.Gamma (1 / 2) * Grothendieck.risingFact (1 / 2) k := by
    rw [show (k : ℝ) + 1 / 2 = 1 / 2 + k by ring]
    exact Gamma_add_nat_eq (by norm_num) k
  have h2 : Real.Gamma ((k : ℝ) + b + 1 / 2) =
      Real.Gamma (b + 1 / 2) * Grothendieck.risingFact (b + 1 / 2) k := by
    rw [show (k : ℝ) + b + 1 / 2 = (b + 1 / 2) + k by ring]
    exact Gamma_add_nat_eq (by positivity) k
  rw [h1, h2]
  have hG : Real.Gamma (1 / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hGb : Real.Gamma (b + 1 / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hf : Grothendieck.risingFact (b + 1 / 2) k ≠ 0 := (risingFact_pos (by positivity) k).ne'
  field_simp

theorem nu_compl_Ioo (b : ℝ) : (nu b) (Set.Ioo (0 : ℝ) 1)ᶜ = 0 := by
  refine MeasureTheory.withDensity_absolutelyContinuous _ _ ?_
  rw [Measure.restrict_apply measurableSet_Ioo.compl]
  simp

theorem nu_compl_Icc (b : ℝ) : (nu b) (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  refine MeasureTheory.measure_mono_null ?_ (nu_compl_Ioo b)
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_Ioo] at hx ⊢
  intro h
  exact hx ⟨le_of_lt h.1, le_of_lt h.2⟩

/-- The candidate measure representing the ratio sequence. -/
def mu (r : ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 * p.2) ((nu ((r + 1) / 2)).prod (nu (1 / 2)))

theorem isFiniteMeasure_prod_nu {r : ℝ} (hr : 0 < r) :
    IsFiniteMeasure ((nu ((r + 1) / 2)).prod (nu (1 / 2))) := by
  have : IsFiniteMeasure (nu ((r + 1) / 2)) := isFiniteMeasure_nu (by linarith)
  have : IsFiniteMeasure (nu (1 / 2)) := isFiniteMeasure_nu (by norm_num)
  constructor
  rw [← Set.univ_prod_univ, Measure.prod_prod]
  exact ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _)

theorem isFiniteMeasure_mu {r : ℝ} (hr : 0 < r) : IsFiniteMeasure (mu r) := by
  have := isFiniteMeasure_prod_nu hr
  exact Measure.isFiniteMeasure_map _ (fun p : ℝ × ℝ => p.1 * p.2)

theorem mu_compl_Icc {r : ℝ} (hr : 0 < r) : (mu r) (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  have : IsFiniteMeasure (nu ((r + 1) / 2)) := isFiniteMeasure_nu (by linarith)
  have : IsFiniteMeasure (nu (1 / 2)) := isFiniteMeasure_nu (by norm_num)
  have hsub : (fun p : ℝ × ℝ => p.1 * p.2) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ ⊆
      (Set.Icc (0 : ℝ) 1)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (Set.Icc (0 : ℝ) 1)ᶜ := by
    rintro ⟨x, y⟩ hxy
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_prod,
      Set.mem_univ, and_true, true_and] at hxy ⊢
    by_cases hx : 0 ≤ x ∧ x ≤ 1
    · by_cases hy : 0 ≤ y ∧ y ≤ 1
      · exact absurd ⟨mul_nonneg hx.1 hy.1, by nlinarith [hx.1, hx.2, hy.1, hy.2]⟩ hxy
      · exact Or.inr hy
    · exact Or.inl hx
  rw [mu, Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
  refine MeasureTheory.measure_mono_null hsub ?_
  refine MeasureTheory.measure_union_null ?_ ?_
  · rw [Measure.prod_prod, nu_compl_Icc, zero_mul]
  · rw [Measure.prod_prod, nu_compl_Icc, mul_zero]

theorem integral_mu {r : ℝ} (hr : 0 < r) (k : ℕ) :
    ∫ x, x ^ k ∂(mu r) = (∫ u, u ^ k ∂(nu ((r + 1) / 2))) * (∫ v, v ^ k ∂(nu (1 / 2))) := by
  have : IsFiniteMeasure (nu ((r + 1) / 2)) := isFiniteMeasure_nu (by linarith)
  have : IsFiniteMeasure (nu (1 / 2)) := isFiniteMeasure_nu (by norm_num)
  rw [mu, integral_map (by fun_prop) (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ k)
    (Measure.map (fun p : ℝ × ℝ => p.1 * p.2) ((nu ((r + 1) / 2)).prod (nu (1 / 2)))))]
  simp only [mul_pow]
  exact MeasureTheory.integral_prod_mul (fun u : ℝ => u ^ k) (fun v : ℝ => v ^ k)

theorem integral_mu_eq {r : ℝ} (hr : 0 < r) (k : ℕ) :
    ∫ x, x ^ k ∂(mu r) =
      Real.Gamma ((k : ℝ) + 1 / 2) * Real.Gamma (((r + 1) / 2) + 1 / 2) /
        (Real.Gamma (1 / 2) * Real.Gamma ((k : ℝ) + ((r + 1) / 2) + 1 / 2)) *
      (Real.Gamma ((k : ℝ) + 1 / 2) * Real.Gamma (1 / 2 + 1 / 2) /
        (Real.Gamma (1 / 2) * Real.Gamma ((k : ℝ) + 1 / 2 + 1 / 2))) := by
  rw [integral_mu hr, integral_nu (by linarith), integral_nu (by norm_num)]

theorem gamma_moment_eq (r : ℝ) (hr : 0 < r) (k : ℕ) :
    Real.Gamma ((k : ℝ) + 1 / 2) * Real.Gamma (((r + 1) / 2) + 1 / 2) /
        (Real.Gamma (1 / 2) * Real.Gamma ((k : ℝ) + ((r + 1) / 2) + 1 / 2)) *
      (Real.Gamma ((k : ℝ) + 1 / 2) * Real.Gamma (1 / 2 + 1 / 2) /
        (Real.Gamma (1 / 2) * Real.Gamma ((k : ℝ) + 1 / 2 + 1 / 2)))
      = Grothendieck.risingFact (1 / 2) k * Grothendieck.risingFact (1 / 2) k /
        (Grothendieck.risingFact (r / 2 + 1) k * (k.factorial : ℝ)) := by
  have h1 : Real.Gamma ((k : ℝ) + 1 / 2) =
      Real.Gamma (1 / 2) * Grothendieck.risingFact (1 / 2) k := by
    rw [show (k : ℝ) + 1 / 2 = 1 / 2 + k by ring]
    exact Gamma_add_nat_eq (by norm_num) k
  have h2 : Real.Gamma (((r + 1) / 2) + 1 / 2) = Real.Gamma (r / 2 + 1) := by
    rw [show ((r + 1) / 2) + 1 / 2 = r / 2 + 1 by ring]
  have h3 : Real.Gamma ((k : ℝ) + ((r + 1) / 2) + 1 / 2) =
      Real.Gamma (r / 2 + 1) * Grothendieck.risingFact (r / 2 + 1) k := by
    rw [show (k : ℝ) + ((r + 1) / 2) + 1 / 2 = (r / 2 + 1) + k by ring]
    exact Gamma_add_nat_eq (by positivity) k
  have h4 : Real.Gamma (1 / 2 + 1 / 2) = 1 := by
    rw [show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.Gamma_one]
  have h5 : Real.Gamma ((k : ℝ) + 1 / 2 + 1 / 2) = (k.factorial : ℝ) := by
    rw [show (k : ℝ) + 1 / 2 + 1 / 2 = 1 + k by ring, Gamma_add_nat_eq (by norm_num) k,
      Real.Gamma_one, one_mul, risingFact_one]
  rw [h1, h2, h3, h4, h5]
  have hG : Real.Gamma (1 / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hGr : Real.Gamma (r / 2 + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hf1 : Grothendieck.risingFact (1 / 2) k ≠ 0 := (risingFact_pos (by norm_num) k).ne'
  have hf2 : Grothendieck.risingFact (r / 2 + 1) k ≠ 0 := (risingFact_pos (by positivity) k).ne'
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Leaf 5**: the ratio sequence `k ↦ (1/2)_k (1/2)_k / ((r/2+1)_k k!)` (`r > 0`) is the moment
sequence of a finite nonnegative measure on `[0,1]`.  Explicitly, the measure is the image under
multiplication of the product of two Beta-type measures on `(0,1)`. -/
theorem exists_finite_measure_moments (r : ℝ) (hr : 0 < r) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ k : ℕ, ∫ x, x ^ k ∂μ
        = Grothendieck.risingFact (1 / 2) k * Grothendieck.risingFact (1 / 2) k /
            (Grothendieck.risingFact (r / 2 + 1) k * (k.factorial : ℝ)) :=
  ⟨mu r, isFiniteMeasure_mu hr, mu_compl_Icc hr, fun k => by
    rw [integral_mu_eq hr k, gamma_moment_eq r hr k]⟩

theorem measure_univ_mu {r : ℝ} (hr : 0 < r) : (mu r) Set.univ = 1 := by
  have : IsFiniteMeasure (nu ((r + 1) / 2)) := isFiniteMeasure_nu (by linarith)
  have : IsFiniteMeasure (nu (1 / 2)) := isFiniteMeasure_nu (by norm_num)
  rw [mu, Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod, measure_univ_nu (by linarith),
    measure_univ_nu (by norm_num), mul_one]

theorem isProbabilityMeasure_mu {r : ℝ} (hr : 0 < r) : IsProbabilityMeasure (mu r) :=
  ⟨measure_univ_mu hr⟩

/-- The same statement with a probability measure (the moments force total mass `1`, since the
`k = 0` moment is `1`). -/
theorem exists_probability_measure_moments (r : ℝ) (hr : 0 < r) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ k : ℕ, ∫ x, x ^ k ∂μ
        = Grothendieck.risingFact (1 / 2) k * Grothendieck.risingFact (1 / 2) k /
            (Grothendieck.risingFact (r / 2 + 1) k * (k.factorial : ℝ)) :=
  ⟨mu r, isProbabilityMeasure_mu hr, mu_compl_Icc hr, fun k => by
    rw [integral_mu_eq hr k, gamma_moment_eq r hr k]⟩

/-- The number `C_r` times the `k`-th moment of the measure is the Taylor coefficient `a_{2k+1}`
of `E_r`, equation (3.9) of the paper. -/
theorem ErCoeff_eq_Cr_mul_integral (r k : ℕ) (hr : 1 ≤ r) :
    Grothendieck.ErCoeff r k = Grothendieck.Cr r * ∫ x, x ^ k ∂(mu (r : ℝ)) := by
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  unfold Grothendieck.ErCoeff
  rw [integral_mu_eq hr' k, gamma_moment_eq (r : ℝ) hr' k]
  ring

end Leaf5

namespace Grothendieck

/-- **The Taylor coefficients of `E_r` are moments** (equation (3.9) of the paper), from the
explicit Beta-product measure of `Leaf5`. -/
theorem ErCoeff_moment_representation_proof (r : ℕ) (hr : 1 ≤ r) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ k : ℕ, ErCoeff r k = Cr r * ∫ x, x ^ k ∂μ :=
  ⟨Leaf5.mu (r : ℝ), Leaf5.isProbabilityMeasure_mu (by exact_mod_cast hr),
   Leaf5.mu_compl_Icc (by exact_mod_cast hr),
   fun k => Leaf5.ErCoeff_eq_Cr_mul_integral r k hr⟩

end Grothendieck

open MeasureTheory in
open Grothendieck in
theorem solution_cr (r : ℕ) (hr : 1 ≤ r) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ k : ℕ, ErCoeff r k = Cr r * ∫ x, x ^ k ∂μ :=
  ErCoeff_moment_representation_proof r hr

/-! ## Part III: `cr r = ‖E_r(i)‖` -/

namespace CrLeaf

open Grothendieck MeasureTheory

/-- `ν_r = nu ((r+1)/2)` on `(0,1)`. -/
def nua (r : ℕ) : Measure ℝ := Leaf5.nu (((r : ℝ) + 1) / 2)

/-- `ν = nu (1/2)` on `(0,1)`. -/
def nub : Measure ℝ := Leaf5.nu (1 / 2)

/-- The product measure on `(0,1)²`. -/
def prod (r : ℕ) : Measure (ℝ × ℝ) := (nua r).prod nub

instance (r : ℕ) : IsProbabilityMeasure (nua r) :=
  Leaf5.isProbabilityMeasure_nu (by positivity)

instance : IsProbabilityMeasure nub := Leaf5.isProbabilityMeasure_nu (by norm_num)

instance (r : ℕ) : IsFiniteMeasure (prod r) := by
  rw [prod]; infer_instance

theorem ae_mem_prod (r : ℕ) :
    ∀ᵐ p ∂(prod r), p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ p.2 ∈ Set.Ioo (0 : ℝ) 1 := by
  have h1 : ∀ᵐ p ∂(prod r), p.1 ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [MeasureTheory.ae_iff]
    have hset : {p : ℝ × ℝ | p.1 ∉ Set.Ioo (0 : ℝ) 1}
        = (Set.Ioo (0 : ℝ) 1)ᶜ ×ˢ Set.univ := by
      ext p; simp
    rw [hset, prod, Measure.prod_prod]
    simp only [nua]
    rw [Leaf5.nu_compl_Ioo (((r:ℝ)+1)/2)]
    simp
  have h2 : ∀ᵐ p ∂(prod r), p.2 ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [MeasureTheory.ae_iff]
    have hset : {p : ℝ × ℝ | p.2 ∉ Set.Ioo (0 : ℝ) 1}
        = Set.univ ×ˢ (Set.Ioo (0 : ℝ) 1)ᶜ := by
      ext p; simp
    rw [hset, prod, Measure.prod_prod]
    simp only [nub]
    rw [Leaf5.nu_compl_Ioo (1/2)]
    simp
  exact h1.and h2

theorem integral_nua_pow (r k : ℕ) :
    ∫ x, x ^ k ∂(nua r)
      = Grothendieck.risingFact (1/2) k / Grothendieck.risingFact ((r : ℝ) / 2 + 1) k := by
  rw [nua, Leaf5.integral_nu_risingFact (by positivity : (0:ℝ) < ((r:ℝ)+1)/2)]
  have h : ((r : ℝ) + 1) / 2 + 1 / 2 = (r : ℝ) / 2 + 1 := by ring
  rw [h]

theorem integral_nub_pow (k : ℕ) :
    ∫ x, x ^ k ∂nub = Grothendieck.risingFact (1/2) k / (k.factorial : ℝ) := by
  rw [nub, Leaf5.integral_nu_risingFact (by norm_num : (0:ℝ) < 1/2)]
  have h : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
  rw [h, Leaf5.risingFact_one]

theorem integral_prod_pow (r k : ℕ) :
    ∫ p : ℝ × ℝ, (p.1 * p.2) ^ k ∂(prod r) = AuxCoeff.ak r k := by
  simp only [mul_pow]
  rw [prod, MeasureTheory.integral_prod_mul (fun u : ℝ => u ^ k) (fun v : ℝ => v ^ k)]
  rw [integral_nua_pow, integral_nub_pow]
  simp only [AuxCoeff.ak, AuxCoeff.cc]
  field_simp

/-- Term-by-term integration of `(p₁p₂)^k φ k` against the product measure. -/
theorem hasSum_integral_pow_mul (r : ℕ) (hr : 2 ≤ r) (φ : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hφ : ∀ k, |φ k| ≤ C) :
    HasSum (fun k : ℕ => AuxCoeff.ak r k * φ k)
      (∫ p : ℝ × ℝ, ∑' k : ℕ, (p.1 * p.2) ^ k * φ k ∂(prod r)) := by
  have hInt : ∀ k : ℕ, Integrable (fun p : ℝ × ℝ => (p.1 * p.2) ^ k * φ k) (prod r) := by
    intro k
    refine MeasureTheory.Integrable.of_bound ?_ C ?_
    · exact (by fun_prop : Measurable fun p : ℝ × ℝ => (p.1 * p.2) ^ k * φ k).aestronglyMeasurable
    · filter_upwards [ae_mem_prod r] with p hp
      have h0 : 0 ≤ p.1 * p.2 := mul_nonneg hp.1.1.le hp.2.1.le
      have h1 : p.1 * p.2 ≤ 1 := by nlinarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg h0]
      calc (p.1 * p.2) ^ k * |φ k| ≤ 1 * C :=
            mul_le_mul (pow_le_one₀ h0 h1) (hφ k) (abs_nonneg _) zero_le_one
        _ = C := one_mul C
  have hnorm : ∀ k : ℕ, ∫ p : ℝ × ℝ, ‖(p.1 * p.2) ^ k * φ k‖ ∂(prod r)
      = |φ k| * AuxCoeff.ak r k := by
    intro k
    rw [← integral_prod_pow (r := r) (k := k), ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_mem_prod r] with p hp
    have h0 : 0 ≤ p.1 * p.2 := mul_nonneg hp.1.1.le hp.2.1.le
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg h0, mul_comm]
  have hsummable : Summable
      (fun k : ℕ => ∫ p : ℝ × ℝ, ‖(p.1 * p.2) ^ k * φ k‖ ∂(prod r)) := by
    have hf : Summable (fun k : ℕ => C * (1 / ((k:ℝ)+1)^2)) :=
      AuxCoeff.summable_inv_sq.mul_left C
    refine Summable.of_nonneg_of_le
      (fun k => MeasureTheory.integral_nonneg (fun p => norm_nonneg _)) (fun k => ?_) hf
    rw [hnorm k]
    calc |φ k| * AuxCoeff.ak r k ≤ C * AuxCoeff.ak r k :=
          mul_le_mul_of_nonneg_right (hφ k) (AuxCoeff.ak_nonneg r k)
      _ ≤ C * (1 / ((k:ℝ)+1)^2) := mul_le_mul_of_nonneg_left (AuxCoeff.ak_le r k hr) hC
  have hmain := MeasureTheory.hasSum_integral_of_summable_integral_norm hInt hsummable
  refine hmain.congr_fun (fun k => ?_)
  have hval : ∫ p : ℝ × ℝ, (p.1 * p.2) ^ k * φ k ∂(prod r) = φ k * AuxCoeff.ak r k := by
    rw [show (fun p : ℝ × ℝ => (p.1 * p.2) ^ k * φ k)
        = (fun p : ℝ × ℝ => φ k * (p.1 * p.2) ^ k) from by ext p; ring]
    rw [MeasureTheory.integral_const_mul, integral_prod_pow]
  rw [hval, mul_comm]

theorem hasSum_ak_neg_one (r : ℕ) (hr : 2 ≤ r) :
    HasSum (fun k : ℕ => AuxCoeff.ak r k * (-1 : ℝ) ^ k)
      (∫ p : ℝ × ℝ, ∑' k : ℕ, (p.1 * p.2) ^ k * (-1 : ℝ) ^ k ∂(prod r)) :=
  hasSum_integral_pow_mul r hr (fun k => (-1 : ℝ) ^ k) 1 zero_le_one (fun k => by
    rw [abs_pow]; simp)

theorem tsum_pow_neg_one (r : ℕ) :
    ∀ᵐ p ∂(prod r),
      (∑' k : ℕ, (p.1 * p.2) ^ k * (-1 : ℝ) ^ k) = (1 + p.1 * p.2)⁻¹ := by
  filter_upwards [ae_mem_prod r] with p hp
  have h0 : 0 ≤ p.1 * p.2 := mul_nonneg hp.1.1.le hp.2.1.le
  have h1 : p.1 * p.2 < 1 := by nlinarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have hgeom : HasSum (fun k : ℕ => (-(p.1 * p.2) : ℝ) ^ k) (1 + p.1 * p.2)⁻¹ := by
    have h := hasSum_geometric_of_norm_lt_one (ξ := (-(p.1 * p.2) : ℝ)) (by
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg h0]; exact h1)
    simpa using h
  have hfun : ∀ k : ℕ, (p.1 * p.2) ^ k * (-1 : ℝ) ^ k = (-(p.1 * p.2)) ^ k := by
    intro k; rw [neg_pow]; ring
  simp only [hfun]
  rw [hgeom.tsum_eq]

/-- Pointwise: the series of `(p₁p₂)^k ((w^k).re - (-1)^k)` sums to the positive difference. -/
theorem tsum_pow_re (r : ℕ) (w : ℂ) (hw : ‖w‖ = 1) :
    ∀ᵐ p ∂(prod r),
      (∑' k : ℕ, (p.1 * p.2) ^ k * ((w ^ k).re - (-1 : ℝ) ^ k))
        = ((1 - (p.1 * p.2 : ℂ) * w)⁻¹).re - (1 + p.1 * p.2)⁻¹ := by
  filter_upwards [ae_mem_prod r] with p hp
  set x : ℝ := p.1 * p.2 with hx
  have hx0 : 0 ≤ x := mul_nonneg hp.1.1.le hp.2.1.le
  have hx1 : x < 1 := by nlinarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have hnn : ‖(x : ℂ) * w‖ < 1 := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0, hw, mul_one]
    exact hx1
  have hgeom : HasSum (fun k : ℕ => ((x : ℂ) * w) ^ k) (1 - (x : ℂ) * w)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hnn
  have hsum1 : (∑' k : ℕ, x ^ k * (w ^ k).re) = ((1 - (x : ℂ) * w)⁻¹).re := by
    rw [show ((1 - (x : ℂ) * w)⁻¹).re = (∑' k : ℕ, ((x : ℂ) * w) ^ k).re by rw [hgeom.tsum_eq]]
    rw [Complex.re_tsum hgeom.summable]
    refine tsum_congr fun k => ?_
    rw [show ((x : ℂ) * w) ^ k = ((x ^ k : ℝ) : ℂ) * w ^ k by push_cast; ring,
      Complex.re_ofReal_mul]
  have hsum2 : (∑' k : ℕ, x ^ k * (-1 : ℝ) ^ k) = (1 + x)⁻¹ := by
    have h0 : 0 ≤ x := hx0
    have h1 : x < 1 := hx1
    have hpg : HasSum (fun k : ℕ => (-x : ℝ) ^ k) (1 + x)⁻¹ := by
      have h := hasSum_geometric_of_norm_lt_one (ξ := (-x : ℝ)) (by
        rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg h0]; exact h1)
      simpa using h
    have hfun : ∀ k : ℕ, x ^ k * (-1 : ℝ) ^ k = (-x) ^ k := by
      intro k; rw [neg_pow]; ring
    simp only [hfun]
    rw [hpg.tsum_eq]
  have hsumm1 : Summable (fun k : ℕ => x ^ k * (w ^ k).re) := by
    refine Summable.of_norm_bounded (g := fun k => x ^ k)
      (summable_geometric_of_lt_one hx0 hx1) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx0]
    have hb : |(w ^ k).re| ≤ 1 := by
      have h := Complex.abs_re_le_norm (w ^ k)
      rw [Complex.norm_pow, hw, one_pow] at h
      exact h
    calc x ^ k * |(w ^ k).re| ≤ x ^ k * 1 :=
          mul_le_mul_of_nonneg_left hb (pow_nonneg hx0 k)
      _ = x ^ k := by ring
  have hsumm2 : Summable (fun k : ℕ => x ^ k * (-1 : ℝ) ^ k) := by
    have hfun : (fun k : ℕ => x ^ k * (-1 : ℝ) ^ k) = (fun k : ℕ => (-x) ^ k) := by
      ext k; rw [neg_pow]; ring
    rw [hfun]
    exact summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hx0]; exact hx1)
  have hsplit : ∀ k : ℕ, x ^ k * ((w ^ k).re - (-1 : ℝ) ^ k)
      = x ^ k * (w ^ k).re - x ^ k * (-1 : ℝ) ^ k := fun k => by ring
  simp only [hsplit]
  rw [hsumm1.tsum_sub hsumm2, hsum1, hsum2]
  rw [hx]; push_cast; ring

/-- The crucial pointwise inequality. -/
theorem re_inv_ge (x : ℝ) (w : ℂ) (hx0 : 0 ≤ x) (hx1 : x < 1) (hw : ‖w‖ = 1) :
    (1 + x)⁻¹ ≤ ((1 - (x : ℂ) * w)⁻¹).re := by
  have hw1 : w.re ^ 2 + w.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq w
    rw [Complex.normSq_apply, hw] at h
    nlinarith [h]
  have hc1 : w.re ≤ 1 := by
    have h := Complex.re_le_norm w
    rw [hw] at h; linarith
  have hc2 : -1 ≤ w.re := by
    have h := Complex.re_le_norm (-w)
    rw [norm_neg, hw, Complex.neg_re] at h
    linarith
  rw [Complex.inv_re]
  have hre : (1 - (x : ℂ) * w).re = 1 - x * w.re := by simp
  have him : (1 - (x : ℂ) * w).im = -x * w.im := by simp
  rw [Complex.normSq_apply, hre, him]
  have hns : (1 - x * w.re) * (1 - x * w.re) + (-x * w.im) * (-x * w.im)
      = 1 - 2 * x * w.re + x ^ 2 := by nlinarith [hw1]
  rw [hns]
  have hden : 0 < 1 - 2 * x * w.re + x ^ 2 := by
    nlinarith [mul_nonneg hx0 hx0, sq_nonneg (1 - x * w.re), sq_nonneg (x * w.im)]
  have hpos : 0 < 1 + x := by linarith
  rw [le_div_iff₀ hden, inv_mul_le_iff₀ hpos]
  nlinarith [mul_nonneg hx0 (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - x) (by linarith : (0:ℝ) ≤ 1 + w.re))]

theorem integral_diff_nonneg (r : ℕ) (w : ℂ) (hw : ‖w‖ = 1) :
    0 ≤ ∫ p : ℝ × ℝ, ∑' k : ℕ, (p.1 * p.2) ^ k * ((w ^ k).re - (-1 : ℝ) ^ k) ∂(prod r) := by
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [tsum_pow_re r w hw, ae_mem_prod r] with p hp hpm
  rw [hp, ← Complex.ofReal_mul]
  have hx0 : 0 ≤ p.1 * p.2 := mul_nonneg hpm.1.1.le hpm.2.1.le
  have hx1 : p.1 * p.2 < 1 := by nlinarith [hpm.1.1, hpm.1.2, hpm.2.1, hpm.2.2]
  exact sub_nonneg.mpr (re_inv_ge (p.1 * p.2) w hx0 hx1 hw)

end CrLeaf

namespace Grothendieck

open MeasureTheory

/-- `g_r(w) = ∑_k a_{2k+1} w^k`. -/
def ger (r : ℕ) (w : ℂ) : ℂ := ∑' k : ℕ, (ErCoeff r k : ℂ) * w ^ k

theorem Cr_pos (r : ℕ) (hr : 1 ≤ r) : 0 < Cr r := by
  unfold Cr
  have hr' : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have h1 : (0:ℝ) < Real.Gamma (((r:ℝ)+1)/2) := Real.Gamma_pos_of_pos (by positivity)
  have h2 : (0:ℝ) < Real.Gamma ((r:ℝ)/2) := Real.Gamma_pos_of_pos (by positivity)
  positivity

theorem ErCoeff_eq_Cr_mul_ak (r k : ℕ) : ErCoeff r k = Cr r * AuxCoeff.ak r k := by
  unfold ErCoeff AuxCoeff.ak AuxCoeff.cc
  rw [sq]
  ring

theorem ErCoeff_nonneg' (r : ℕ) (hr : 1 ≤ r) (k : ℕ) : 0 ≤ ErCoeff r k := by
  rw [ErCoeff_eq_Cr_mul_ak]
  exact mul_nonneg (le_of_lt (Cr_pos r hr)) (AuxCoeff.ak_nonneg r k)

theorem norm_ErCoeff_le (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    ‖(ErCoeff r k : ℂ)‖ ≤ Cr r * (1 / ((k:ℝ)+1)^2) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ErCoeff_nonneg' r (by omega) k),
    ErCoeff_eq_Cr_mul_ak]
  exact mul_le_mul_of_nonneg_left (AuxCoeff.ak_le r k hr) (le_of_lt (Cr_pos r (by omega)))

theorem summable_ErCoeff_pow (r : ℕ) (hr : 2 ≤ r) (w : ℂ) (hw : ‖w‖ ≤ 1) :
    Summable (fun k : ℕ => (ErCoeff r k : ℂ) * w ^ k) := by
  refine Summable.of_norm_bounded (g := fun k : ℕ => Cr r * (1 / ((k:ℝ)+1)^2))
    (AuxCoeff.summable_inv_sq.mul_left (Cr r)) (fun k => ?_)
  rw [Complex.norm_mul, Complex.norm_pow]
  calc ‖(ErCoeff r k : ℂ)‖ * ‖w‖ ^ k ≤ (Cr r * (1 / ((k:ℝ)+1)^2)) * 1 ^ k := by
        refine mul_le_mul (norm_ErCoeff_le r hr k) (by simpa using pow_le_one₀ (norm_nonneg w) hw)
          (pow_nonneg (norm_nonneg w) k) ?_
        exact mul_nonneg (le_of_lt (Cr_pos r (by omega))) (by positivity)
    _ = Cr r * (1 / ((k:ℝ)+1)^2) := by ring

theorem ErComplex_eq (r : ℕ) (z : ℂ) : ErComplex r z = z * ger r (z * z) := by
  unfold ErComplex ger
  have hterm : ∀ k : ℕ, (ErCoeff r k : ℂ) * z ^ (2*k+1) = z * ((ErCoeff r k : ℂ) * (z*z)^k) := by
    intro k; rw [mul_pow]; ring
  simp only [hterm]
  rw [tsum_mul_left]

theorem ger_re (r : ℕ) (hr : 2 ≤ r) (w : ℂ) (hw : ‖w‖ ≤ 1) :
    (ger r w).re = Cr r * ∑' k : ℕ, AuxCoeff.ak r k * (w ^ k).re := by
  have hs := summable_ErCoeff_pow r hr w hw
  unfold ger
  rw [Complex.re_tsum hs]
  simp only [Complex.re_ofReal_mul]
  have h2 : ∀ k : ℕ, ErCoeff r k * (w ^ k).re = Cr r * (AuxCoeff.ak r k * (w ^ k).re) := by
    intro k; rw [ErCoeff_eq_Cr_mul_ak]; ring
  simp only [h2]
  rw [tsum_mul_left]

theorem ger_neg_one (r : ℕ) (hr : 2 ≤ r) :
    ger r (-1) = ((Cr r * ∑' k : ℕ, AuxCoeff.ak r k * (-1:ℝ)^k : ℝ) : ℂ) := by
  unfold ger
  have hterm : ∀ k : ℕ, (ErCoeff r k : ℂ) * (-1 : ℂ) ^ k
      = ((ErCoeff r k * (-1 : ℝ) ^ k : ℝ) : ℂ) := by
    intro k; push_cast; ring
  simp only [hterm]
  rw [← Complex.ofReal_tsum]
  congr 1
  have h2 : ∀ k : ℕ, ErCoeff r k * (-1:ℝ)^k = Cr r * (AuxCoeff.ak r k * (-1:ℝ)^k) := by
    intro k; rw [ErCoeff_eq_Cr_mul_ak]; ring
  simp only [h2]
  rw [tsum_mul_left]

/-- `T_r = ∑_k a_k (-1)^k = ∫ (1+uv)^{-1}`. -/
theorem T_eq_integral (r : ℕ) (hr : 2 ≤ r) :
    (∑' k : ℕ, AuxCoeff.ak r k * (-1:ℝ)^k)
      = ∫ p : ℝ × ℝ, (1 + p.1 * p.2)⁻¹ ∂(CrLeaf.prod r) := by
  have h := CrLeaf.hasSum_ak_neg_one r hr
  rw [h.tsum_eq]
  exact MeasureTheory.integral_congr_ae (CrLeaf.tsum_pow_neg_one r)

theorem T_nonneg (r : ℕ) (hr : 2 ≤ r) : 0 ≤ ∑' k : ℕ, AuxCoeff.ak r k * (-1:ℝ)^k := by
  rw [T_eq_integral r hr]
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [CrLeaf.ae_mem_prod r] with p hp
  have h0 : 0 ≤ p.1 * p.2 := mul_nonneg hp.1.1.le hp.2.1.le
  have h1 : p.1 * p.2 < 1 := by nlinarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have : (0:ℝ) < 1 + p.1 * p.2 := by linarith
  positivity

theorem hasSum_ak_diff (r : ℕ) (hr : 2 ≤ r) (w : ℂ) (hw : ‖w‖ = 1) :
    HasSum (fun k : ℕ => AuxCoeff.ak r k * ((w ^ k).re - (-1:ℝ)^k))
      (∫ p : ℝ × ℝ, ∑' k : ℕ, (p.1*p.2)^k * ((w^k).re - (-1:ℝ)^k) ∂(CrLeaf.prod r)) := by
  refine CrLeaf.hasSum_integral_pow_mul r hr _ 2 (by norm_num) (fun k => ?_)
  have h1 : |(w ^ k).re| ≤ 1 := by
    have h := Complex.abs_re_le_norm (w ^ k)
    rw [Complex.norm_pow, hw, one_pow] at h
    exact h
  have h2 : |(-1:ℝ)^k| = 1 := by rw [abs_pow]; simp
  calc |(w^k).re - (-1:ℝ)^k| ≤ |(w^k).re| + |(-1:ℝ)^k| := abs_sub _ _
    _ ≤ 1 + 1 := by linarith
    _ = 2 := by norm_num

theorem ak_re_sum_ge (r : ℕ) (hr : 2 ≤ r) (w : ℂ) (hw : ‖w‖ = 1) :
    (∑' k : ℕ, AuxCoeff.ak r k * (-1:ℝ)^k) ≤ ∑' k : ℕ, AuxCoeff.ak r k * (w^k).re := by
  have hh := hasSum_ak_diff r hr w hw
  have hnn := CrLeaf.integral_diff_nonneg r w hw
  have hsplit : (∑' k : ℕ, AuxCoeff.ak r k * ((w^k).re - (-1:ℝ)^k))
      = (∑' k : ℕ, AuxCoeff.ak r k * (w^k).re) - (∑' k : ℕ, AuxCoeff.ak r k * (-1:ℝ)^k) := by
    have hf : Summable (fun k : ℕ => AuxCoeff.ak r k * (w^k).re) := by
      refine Summable.of_norm_bounded (g := fun k : ℕ => AuxCoeff.ak r k)
        (Summable.of_nonneg_of_le (fun k => AuxCoeff.ak_nonneg r k)
          (fun k => AuxCoeff.ak_le r k hr) AuxCoeff.summable_inv_sq) (fun k => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (AuxCoeff.ak_nonneg r k)]
      have hb : |(w ^ k).re| ≤ 1 := by
        have h := Complex.abs_re_le_norm (w ^ k)
        rw [Complex.norm_pow, hw, one_pow] at h
        exact h
      simpa using mul_le_mul_of_nonneg_left hb (AuxCoeff.ak_nonneg r k)
    have hg : Summable (fun k : ℕ => AuxCoeff.ak r k * (-1:ℝ)^k) := by
      refine Summable.of_norm_bounded (g := fun k : ℕ => AuxCoeff.ak r k)
        (Summable.of_nonneg_of_le (fun k => AuxCoeff.ak_nonneg r k)
          (fun k => AuxCoeff.ak_le r k hr) AuxCoeff.summable_inv_sq) (fun k => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_nonneg (AuxCoeff.ak_nonneg r k), mul_one]
    have hsp : ∀ k : ℕ, AuxCoeff.ak r k * ((w^k).re - (-1:ℝ)^k)
        = AuxCoeff.ak r k * (w^k).re - AuxCoeff.ak r k * (-1:ℝ)^k := fun k => by ring
    simp only [hsp]
    rw [hf.tsum_sub hg]
  have h3 : 0 ≤ (∑' k : ℕ, AuxCoeff.ak r k * ((w^k).re - (-1:ℝ)^k)) := by
    rw [hh.tsum_eq]; exact hnn
  linarith

theorem le_norm_ger (r : ℕ) (hr : 2 ≤ r) (w : ℂ) (hw : ‖w‖ = 1) :
    Cr r * (∑' k : ℕ, AuxCoeff.ak r k * (-1:ℝ)^k) ≤ ‖ger r w‖ := by
  have hS := ak_re_sum_ge r hr w hw
  have hre := ger_re r hr w (le_of_eq hw)
  have h1 : Cr r * (∑' k, AuxCoeff.ak r k * (-1:ℝ)^k) ≤ (ger r w).re := by
    rw [hre]
    exact mul_le_mul_of_nonneg_left hS (le_of_lt (Cr_pos r (by omega)))
  have h2 : (ger r w).re ≤ ‖ger r w‖ := Complex.re_le_norm _
  linarith

theorem norm_ger_neg_one (r : ℕ) (hr : 2 ≤ r) :
    ‖ger r (-1)‖ = Cr r * (∑' k : ℕ, AuxCoeff.ak r k * (-1:ℝ)^k) := by
  rw [ger_neg_one r hr, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (le_of_lt (Cr_pos r (by omega))) (T_nonneg r hr))]

/-- **Lemma 3.5**: `c_r = ‖E_r(i)‖`. -/
theorem cr_eq_norm_er_I (r : ℕ) (hr : 2 ≤ r) : cr r = ‖ErComplex r Complex.I‖ := by
  have hexp : Complex.exp (Complex.I * ((Real.pi/2 : ℝ) : ℂ)) = Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    norm_num
  have hkey : ∀ z : ℂ, ‖z‖ = 1 → ‖ErComplex r Complex.I‖ ≤ ‖ErComplex r z‖ := by
    intro z hz
    have hz2 : ‖z * z‖ = 1 := by rw [Complex.norm_mul, hz, mul_one]
    have h3 : ‖ErComplex r Complex.I‖ = ‖ger r (-1)‖ := by
      rw [ErComplex_eq, Complex.I_mul_I, Complex.norm_mul, Complex.norm_I, one_mul]
    have h1 : ‖ErComplex r z‖ = ‖ger r (z * z)‖ := by
      rw [ErComplex_eq, Complex.norm_mul, hz, one_mul]
    rw [h3, norm_ger_neg_one r hr, h1]
    exact le_norm_ger r hr _ hz2
  have hmem : ‖ErComplex r Complex.I‖ ∈
      {y : ℝ | ∃ t ∈ Set.Icc (0:ℝ) (2*Real.pi), y = ‖ErComplex r (Complex.exp (Complex.I * (t:ℂ)))‖} := by
    refine ⟨Real.pi/2, ⟨le_of_lt (by positivity), by nlinarith [Real.pi_pos]⟩, ?_⟩
    rw [hexp]
  refine le_antisymm (csInf_le ⟨0, ?_⟩ hmem) (le_csInf ⟨_, hmem⟩ ?_)
  · rintro y ⟨t, ht, rfl⟩
    positivity
  · rintro y ⟨t, ht, rfl⟩
    refine hkey _ ?_
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

end Grothendieck

open Grothendieck in
theorem solution (r : ℕ) (hr : 2 ≤ r) :
    (∀ k : ℕ, ErCoeff r k ≤ Cr r / ((k : ℝ) + 1) ^ 2) ∧
      (∀ w : ℂ, ‖w‖ ≤ 1 → Summable (fun k : ℕ => (ErCoeff r k : ℂ) * w ^ k)) := by
  refine ⟨fun k => ?_, fun w hw => Grothendieck.summable_ErCoeff_pow r hr w hw⟩
  have h := Grothendieck.norm_ErCoeff_le r hr k
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Grothendieck.ErCoeff_nonneg' r (by omega) k)] at h
  rw [div_eq_mul_one_div]
  simpa [mul_comm, one_div] using h
