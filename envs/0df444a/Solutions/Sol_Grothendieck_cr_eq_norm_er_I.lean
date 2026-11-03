-- Prove2me | solution 1 for Grothendieck.cr_eq_norm_er_I
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T15:57:28.195862+00:00
-- url     : https://prove2.me/submissions/a6909cad-28ef-401b-be67-ebcecf3184d3

import Mathlib
import Definitions.Def_Grothendieck_Series

set_option autoImplicit false

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

open Filter
open scoped Topology

/-! ## Part 1: the moment measure, summability of the Taylor coefficients

We work with the explicit probability measure `Leaf5.mu r` on `[0,1]` whose `k`-th moment is
`ErCoeff r k / Cr r`.  Nothing below uses `vietoris_pos` or any published lemma beyond the
moment representation copied above. -/

namespace Grothendieck

/-- The moment measure of the Taylor coefficients of `E_r`. -/
def MM (r : ℕ) : Measure ℝ := Leaf5.mu (r : ℝ)

lemma MM_prob {r : ℕ} (hr : 1 ≤ r) : IsProbabilityMeasure (MM r) :=
  Leaf5.isProbabilityMeasure_mu (by exact_mod_cast hr)

lemma MM_support {r : ℕ} (hr : 1 ≤ r) : MM r (Set.Icc (0 : ℝ) 1)ᶜ = 0 :=
  Leaf5.mu_compl_Icc (by exact_mod_cast hr)

/-- The `k`-th moment of `MM r`. -/
def cc (r k : ℕ) : ℝ := ∫ s, s ^ k ∂(MM r)

lemma MM_mom {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : ErCoeff r k = Cr r * cc r k :=
  Leaf5.ErCoeff_eq_Cr_mul_integral r k hr

lemma risingFact_half_pos' (k : ℕ) : 0 < risingFact (1 / 2) k := by
  unfold risingFact
  exact Finset.prod_pos fun i _ => by positivity

lemma risingFact_succ' (a : ℝ) (k : ℕ) :
    risingFact a (k + 1) = risingFact a k * (a + (k : ℝ)) := by
  rw [risingFact, Finset.prod_range_succ, ← risingFact]

lemma risingFact_three_half' (k : ℕ) :
    risingFact (3 / 2) k = risingFact (1 / 2) k * (2 * (k : ℝ) + 1) := by
  induction k with
  | zero => simp [risingFact]
  | succ k ih =>
    rw [risingFact_succ', risingFact_succ', ih]
    push_cast
    ring

lemma risingFact_half_succ (k : ℕ) :
    risingFact (1 / 2) (k + 1) = risingFact (1 / 2) k * (1 / 2 + (k : ℝ)) :=
  risingFact_succ' _ k

/-- The basic ratio sequence `b_k = (1/2)_k / k!`. -/
def bb (k : ℕ) : ℝ := risingFact (1 / 2) k / (k.factorial : ℝ)

lemma bb_nonneg (k : ℕ) : 0 ≤ bb k :=
  div_nonneg (le_of_lt (risingFact_half_pos' k)) (by positivity)

lemma bb_succ (k : ℕ) : bb (k + 1) = bb k * ((1 / 2 + (k : ℝ)) / ((k : ℝ) + 1)) := by
  unfold bb
  rw [risingFact_half_succ, Nat.factorial_succ]
  push_cast
  field_simp

lemma bb_zero : bb 0 = 1 := by
  simp [bb, risingFact]

/-- The comparison sequence `d_k = b_k/(2k+1) = (1/2)_k/((2k+1)·k!)` is summable, by
telescoping against `2(b_k - b_{k+1}) = b_k/(k+1)`. -/
theorem summable_dd :
    Summable fun k : ℕ => risingFact (1 / 2) k / ((2 * (k : ℝ) + 1) * (k.factorial : ℝ)) := by
  have key : ∀ k : ℕ,
      risingFact (1 / 2) k / ((2 * (k : ℝ) + 1) * (k.factorial : ℝ)) ≤ 2 * (bb k - bb (k + 1)) := by
    intro k
    have hb : 0 ≤ bb k := bb_nonneg k
    have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h2 : (k : ℝ) + 1 ≤ 2 * (k : ℝ) + 1 := by
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h3 : 2 * (bb k - bb (k + 1)) = bb k / ((k : ℝ) + 1) := by
      rw [bb_succ]
      field_simp
      ring
    have h4 : bb k / ((2 * (k : ℝ) + 1)) ≤ bb k / ((k : ℝ) + 1) :=
      div_le_div_of_nonneg_left hb h1 h2
    have h5 : risingFact (1 / 2) k / ((2 * (k : ℝ) + 1) * (k.factorial : ℝ)) =
        bb k / ((2 * (k : ℝ) + 1) * (k.factorial : ℝ)) * (k.factorial : ℝ) := by
      unfold bb
      field_simp
    rw [h3]
    unfold bb at h4
    calc risingFact (1 / 2) k / ((2 * (k : ℝ) + 1) * (k.factorial : ℝ))
        = risingFact (1 / 2) k / (k.factorial : ℝ) / (2 * (k : ℝ) + 1) := by
          field_simp
      _ ≤ risingFact (1 / 2) k / (k.factorial : ℝ) / ((k : ℝ) + 1) := h4
  refine summable_of_sum_range_le (f := fun k : ℕ =>
    risingFact (1 / 2) k / ((2 * (k : ℝ) + 1) * (k.factorial : ℝ))) (c := 2) ?_ ?_
  · intro n
    have := risingFact_half_pos' n
    positivity
  · intro n
    calc ∑ k ∈ Finset.range n,
          risingFact (1 / 2) k / ((2 * (k : ℝ) + 1) * (k.factorial : ℝ))
        ≤ ∑ k ∈ Finset.range n, 2 * (bb k - bb (k + 1)) := Finset.sum_le_sum fun k _ => key k
      _ = 2 * (bb 0 - bb n) := by
          have htele : ∑ i ∈ Finset.range n, (bb i - bb (i + 1)) = bb 0 - bb n := by
            have h := Finset.sum_range_sub (fun k => -bb k) n
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, Finset.sum_neg_distrib]
              using h
          rw [← Finset.mul_sum, htele]
      _ ≤ 2 := by
          have h : 0 ≤ bb n := bb_nonneg n
          rw [bb_zero]
          linarith

lemma Cr_pos' {r : ℕ} (hr : 1 ≤ r) : 0 < Cr r := by
  unfold Cr
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h1 : (0 : ℝ) < Real.Gamma (((r : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : (0 : ℝ) < Real.Gamma ((r : ℝ) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h3 : (0 : ℝ) < Real.Gamma (((r : ℝ) + 1) / 2) / Real.Gamma ((r : ℝ) / 2) := div_pos h1 h2
  positivity

lemma ErCoeff_nonneg' {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : 0 ≤ ErCoeff r k := by
  unfold ErCoeff
  have h1 := Cr_pos' hr
  have h2 := risingFact_half_pos' k
  have h3 : 0 < risingFact ((r : ℝ) / 2 + 1) k := by
    unfold risingFact
    exact Finset.prod_pos fun i _ => by positivity
  have h4 : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  positivity

lemma ErCoeff_le_dd {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    ErCoeff r k ≤ Cr r * (risingFact (1 / 2) k / ((2 * (k : ℝ) + 1) * (k.factorial : ℝ))) := by
  unfold ErCoeff
  have hC : 0 < Cr r := Cr_pos' hr
  have hsq : 0 < (risingFact (1 / 2) k) ^ 2 := by
    have := risingFact_half_pos' k; positivity
  have hfk : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hden2 : 0 < risingFact ((r : ℝ) / 2 + 1) k := by
    unfold risingFact
    exact Finset.prod_pos fun i _ => by positivity
  have hden1 : 0 < risingFact (3 / 2) k := by
    unfold risingFact
    exact Finset.prod_pos fun i _ => by positivity
  have hmono : risingFact (3 / 2) k ≤ risingFact ((r : ℝ) / 2 + 1) k := by
    unfold risingFact
    refine Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    push_cast
    linarith
  have h1 : (risingFact (1 / 2) k) ^ 2 / (risingFact ((r : ℝ) / 2 + 1) k * (k.factorial : ℝ))
      ≤ (risingFact (1 / 2) k) ^ 2 / (risingFact (3 / 2) k * (k.factorial : ℝ)) :=
    div_le_div_of_nonneg_left (le_of_lt hsq) (by positivity)
      (mul_le_mul_of_nonneg_right hmono (le_of_lt hfk))
  calc Cr r * (risingFact (1 / 2) k) ^ 2 / (risingFact ((r : ℝ) / 2 + 1) k * (k.factorial : ℝ))
      = Cr r * ((risingFact (1 / 2) k) ^ 2
          / (risingFact ((r : ℝ) / 2 + 1) k * (k.factorial : ℝ))) := by field_simp
    _ ≤ Cr r * ((risingFact (1 / 2) k) ^ 2 / (risingFact (3 / 2) k * (k.factorial : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hC)
    _ = Cr r * (risingFact (1 / 2) k / ((2 * (k : ℝ) + 1) * (k.factorial : ℝ))) := by
        rw [risingFact_three_half']
        have h1' : (0:ℝ) < risingFact (1/2) k := risingFact_half_pos' k
        have h2' : (0:ℝ) < (k.factorial : ℝ) := by positivity
        have h3' : (0:ℝ) < 2*(k:ℝ)+1 := by positivity
        field_simp

/-- The Taylor coefficients of `E_r` form an absolutely summable series. -/
theorem summable_ErCoeff' {r : ℕ} (hr : 1 ≤ r) : Summable fun k : ℕ => ErCoeff r k :=
  Summable.of_nonneg_of_le (fun k => ErCoeff_nonneg' hr k) (fun k => ErCoeff_le_dd hr k)
    (summable_dd.mul_left (Cr r))

end Grothendieck

namespace Grothendieck

lemma MM_ae_mem {r : ℕ} (hr : 1 ≤ r) : ∀ᵐ s ∂(MM r), s ∈ Set.Icc (0 : ℝ) 1 := by
  have h : ((Set.Icc (0 : ℝ) 1)ᶜ)ᶜ ∈ ae (MM r) :=
    MeasureTheory.compl_mem_ae_iff.mpr (MM_support hr)
  filter_upwards [h] with s hs
  simpa using hs

lemma cc_nonneg {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : 0 ≤ cc r k := by
  unfold cc
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [MM_ae_mem hr] with s hs
  exact pow_nonneg hs.1 k

lemma cc_summable {r : ℕ} (hr : 1 ≤ r) : Summable fun k : ℕ => cc r k := by
  have h := (summable_ErCoeff' hr).mul_left ((Cr r)⁻¹)
  refine h.congr (fun k => ?_)
  rw [MM_mom hr k]
  have hCr : Cr r ≠ 0 := (Cr_pos' hr).ne'
  field_simp

lemma cc_tendsto_zero {r : ℕ} (hr : 1 ≤ r) :
    Filter.Tendsto (fun k => cc r k) Filter.atTop (𝓝 0) :=
  (cc_summable hr).tendsto_atTop_zero

lemma integrable_pow_moment {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    Integrable (fun s : ℝ => s ^ k) (MM r) := by
  haveI := MM_prob hr
  refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
  · exact (measurable_id.pow_const k).aestronglyMeasurable
  · filter_upwards [MM_ae_mem hr] with s hs
    simp only [Set.mem_Icc] at hs
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg s) (by rw [abs_le]; exact ⟨by linarith [hs.1], hs.2⟩)

/-- The measure of the point `1` vanishes: the moments tend to `0`. -/
lemma MM_singleton_one {r : ℕ} (hr : 1 ≤ r) : MM r {1} = 0 := by
  haveI := MM_prob hr
  have hsupp := MM_ae_mem hr
  have hle : ∀ k : ℕ, (MM r).real {1} ≤ cc r k := by
    intro k
    calc (MM r).real {1} = ∫ s in ({1} : Set ℝ), (1 : ℝ) ∂(MM r) := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
      _ = ∫ s in ({1} : Set ℝ), s ^ k ∂(MM r) := by
          refine MeasureTheory.setIntegral_congr_fun (measurableSet_singleton (1:ℝ)) ?_
          intro x hx
          simp only [Set.mem_singleton_iff] at hx
          simp [hx]
      _ ≤ ∫ s, s ^ k ∂(MM r) :=
          MeasureTheory.setIntegral_le_integral (integrable_pow_moment hr k)
            (by filter_upwards [hsupp] with s hs using pow_nonneg hs.1 k)
      _ = cc r k := rfl
  have hreal : (MM r).real {1} = 0 := by
    refine le_antisymm ?_ ?_
    · by_contra hcon
      push_neg at hcon
      have hev : ∀ᶠ k in Filter.atTop, cc r k < (MM r).real {1} :=
        (cc_tendsto_zero hr).eventually (Iio_mem_nhds hcon)
      obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
      have hK' := hK K le_rfl
      have hKK := hle K
      linarith
    · rw [measureReal_def]
      positivity
  have hm : (MM r {1}).toReal = 0 := by
    rw [measureReal_def] at hreal
    exact hreal
  have htop : MM r {1} ≠ ⊤ :=
    ne_top_of_le_ne_top (MeasureTheory.measure_ne_top (MM r) Set.univ)
      (MeasureTheory.measure_mono (Set.subset_univ ({1} : Set ℝ)))
  rcases (ENNReal.toReal_eq_zero_iff _).mp hm with h | h
  · exact h
  · exact absurd h htop

lemma MM_ae_lt_one {r : ℕ} (hr : 1 ≤ r) : ∀ᵐ s ∂(MM r), s < 1 := by
  have hne : ∀ᵐ s ∂(MM r), s ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simpa using MM_singleton_one hr
  filter_upwards [MM_ae_mem hr, hne] with s hs hs1
  exact lt_of_le_of_ne hs.2 hs1

lemma measurable_ofReal_pow : Measurable fun s : ℝ => ENNReal.ofReal (s ^ 2) := by
  fun_prop

lemma lintegral_inv_one_sub_ne_top {r : ℕ} (hr : 1 ≤ r) :
    ∫⁻ s, ENNReal.ofReal ((1 - s)⁻¹) ∂(MM r) ≠ ⊤ := by
  have hae : ∀ᵐ s ∂(MM r),
      ENNReal.ofReal ((1 - s)⁻¹) ≤ ∑' k : ℕ, ENNReal.ofReal (s ^ k) := by
    filter_upwards [MM_ae_mem hr, MM_ae_lt_one hr] with s hs hs1
    have hnn : ∀ k : ℕ, (0 : ℝ) ≤ s ^ k := fun k => pow_nonneg hs.1 k
    have hsum : Summable fun k : ℕ => s ^ k := summable_geometric_of_lt_one hs.1 hs1
    rw [← tsum_geometric_of_lt_one hs.1 hs1,
      ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  have hstep : ∫⁻ s, ENNReal.ofReal ((1 - s)⁻¹) ∂(MM r)
      ≤ ∑' k : ℕ, ENNReal.ofReal (cc r k) := by
    calc ∫⁻ s, ENNReal.ofReal ((1 - s)⁻¹) ∂(MM r)
        ≤ ∫⁻ s, ∑' k : ℕ, ENNReal.ofReal (s ^ k) ∂(MM r) :=
          MeasureTheory.lintegral_mono_ae hae
      _ = ∑' k : ℕ, ∫⁻ s, ENNReal.ofReal (s ^ k) ∂(MM r) := by
          refine MeasureTheory.lintegral_tsum (fun k => ?_)
          exact ((measurable_id.pow_const k).ennreal_ofReal).aemeasurable
      _ = ∑' k : ℕ, ENNReal.ofReal (cc r k) := by
          refine tsum_congr (fun k => ?_)
          rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrable_pow_moment hr k)
            (by filter_upwards [MM_ae_mem hr] with s hs using pow_nonneg hs.1 k)]
          rfl
  have htop : ∑' k : ℕ, ENNReal.ofReal (cc r k) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => cc_nonneg hr k) (cc_summable hr)]
    exact ENNReal.ofReal_lt_top.ne
  exact ne_top_of_le_ne_top htop hstep

lemma integrable_inv_one_sub {r : ℕ} (hr : 1 ≤ r) :
    Integrable (fun s : ℝ => (1 - s)⁻¹) (MM r) := by
  refine ⟨((measurable_const.sub measurable_id).inv).aestronglyMeasurable, ?_⟩
  simp only [MeasureTheory.HasFiniteIntegral]
  have hae : ∀ᵐ s ∂(MM r), ‖(1 - s)⁻¹‖ₑ = ENNReal.ofReal ((1 - s)⁻¹) := by
    filter_upwards [MM_ae_lt_one hr] with s hs
    rw [Real.enorm_eq_ofReal_abs,
      abs_of_pos (by positivity : (0:ℝ) < (1 - s)⁻¹)]
  rw [MeasureTheory.lintegral_congr_ae hae]
  exact lt_top_iff_ne_top.mpr (lintegral_inv_one_sub_ne_top hr)

end Grothendieck

/-! ## Part 3: the real part of `(1 - s e^{iu})⁻¹`, the geometric series against the moments -/

namespace Grothendieck

/-- The point `s e^{iu}` of the unit disc, as a complex number. -/
def wfun (u s : ℝ) : ℂ := (s : ℂ) * Complex.exp (u * Complex.I)

lemma norm_wfun (u s : ℝ) (hs : 0 ≤ s) : ‖wfun u s‖ = s := by
  rw [wfun, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs,
    Complex.norm_exp_ofReal_mul_I, mul_one]

lemma one_sub_wfun_re (u s : ℝ) : (1 - wfun u s).re = 1 - s * Real.cos u := by
  simp only [wfun, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

lemma one_sub_wfun_im (u s : ℝ) : (1 - wfun u s).im = -(s * Real.sin u) := by
  simp only [wfun, Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- The real part of `(1 - s e^{iu})⁻¹` is the Poisson-type kernel. -/
theorem re_inv_one_sub (u s : ℝ) :
    ((1 - wfun u s)⁻¹).re = (1 - s * Real.cos u) / (1 - 2 * s * Real.cos u + s ^ 2) := by
  have hsq : (1 - s * Real.cos u) * (1 - s * Real.cos u)
      + (-(s * Real.sin u)) * (-(s * Real.sin u)) = 1 - 2 * s * Real.cos u + s ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  rw [Complex.inv_re, Complex.normSq_apply, one_sub_wfun_re, one_sub_wfun_im, hsq]

/-- For `0 ≤ s < 1` the geometric series of the real parts sums to the Poisson kernel. -/
theorem tsum_pow_cos (s u : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    (∑' k : ℕ, s ^ k * Real.cos (k * u))
      = (1 - s * Real.cos u) / (1 - 2 * s * Real.cos u + s ^ 2) := by
  have hwlt : ‖wfun u s‖ < 1 := by rw [norm_wfun u s hs]; exact hs1
  have hsumm : Summable fun k : ℕ => wfun u s ^ k := summable_geometric_of_norm_lt_one hwlt
  have hgeo : (∑' k : ℕ, wfun u s ^ k) = (1 - wfun u s)⁻¹ :=
    tsum_geometric_of_norm_lt_one hwlt
  have h1 : ∀ k : ℕ, (wfun u s ^ k).re = s ^ k * Real.cos (k * u) := by
    intro k
    have hw : wfun u s ^ k = (s : ℂ) ^ k * Complex.exp (u * Complex.I) ^ k := by
      rw [wfun, mul_pow]
    rw [hw, ← Complex.exp_nat_mul]
    have harg : (↑k : ℂ) * (u * Complex.I) = ((k : ℝ) * u : ℝ) * Complex.I := by
      push_cast
      ring
    have hsk : ((s : ℂ)) ^ k = ((s ^ k : ℝ) : ℂ) := by push_cast; ring
    rw [harg, hsk, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re]
    ring
  have hre : (∑' k : ℕ, s ^ k * Real.cos (k * u)) = ((1 - wfun u s)⁻¹).re := by
    rw [← hgeo, Complex.re_tsum hsumm]
    exact tsum_congr fun k => (h1 k).symm
  rw [hre, re_inv_one_sub]

lemma summable_pow_cos (s u : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    Summable fun k : ℕ => s ^ k * Real.cos (k * u) := by
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one hs hs1) (fun k => ?_)
  have hsk : (0 : ℝ) ≤ s ^ k := pow_nonneg hs k
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hs]
  calc s ^ k * |Real.cos (k * u)| ≤ s ^ k * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hsk
    _ = s ^ k := by ring

lemma ae_geom (r : ℕ) (hr : 1 ≤ r) (u : ℝ) :
    ∀ᵐ s ∂(MM r), (∑' k : ℕ, s ^ k * Real.cos (k * u))
      = (1 - s * Real.cos u) / (1 - 2 * s * Real.cos u + s ^ 2) := by
  filter_upwards [MM_ae_mem hr, MM_ae_lt_one hr] with s hs hs1
  exact tsum_pow_cos s u hs.1 hs1

lemma lintegral_enorm_pow_cos_le (r : ℕ) (hr : 1 ≤ r) (u : ℝ) (k : ℕ) :
    ∫⁻ s, ‖s ^ k * Real.cos (k * u)‖ₑ ∂(MM r) ≤ ENNReal.ofReal (cc r k) := by
  have hle : ∀ᵐ s ∂(MM r), ‖s ^ k * Real.cos (k * u)‖ₑ ≤ ENNReal.ofReal (s ^ k) := by
    filter_upwards [MM_ae_mem hr] with s hs
    have hsk : (0 : ℝ) ≤ s ^ k := pow_nonneg hs.1 k
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_pow, abs_of_nonneg hs.1]
    refine ENNReal.ofReal_le_ofReal ?_
    calc s ^ k * |Real.cos (k * u)| ≤ s ^ k * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hsk
      _ = s ^ k := by ring
  refine le_trans (MeasureTheory.lintegral_mono_ae hle) ?_
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrable_pow_moment hr k)
    (by filter_upwards [MM_ae_mem hr] with s hs using pow_nonneg hs.1 k)]
  rfl

/-- **The integral representation of the cosine transform of the moment sequence.** -/
theorem integral_geom (r : ℕ) (hr : 1 ≤ r) (u : ℝ) :
    (∑' k : ℕ, cc r k * Real.cos (k * u))
      = ∫ s, (1 - s * Real.cos u) / (1 - 2 * s * Real.cos u + s ^ 2) ∂(MM r) := by
  have hmeas : ∀ k : ℕ, AEStronglyMeasurable (fun s : ℝ => s ^ k * Real.cos (k * u)) (MM r) :=
    fun k => ((measurable_id.pow_const k).mul_const _).aestronglyMeasurable
  have hsumm : (∑' k : ℕ, ∫⁻ s, ‖s ^ k * Real.cos (k * u)‖ₑ ∂(MM r)) ≠ ⊤ := by
    have hle : (∑' k : ℕ, ∫⁻ s, ‖s ^ k * Real.cos (k * u)‖ₑ ∂(MM r))
        ≤ ∑' k : ℕ, ENNReal.ofReal (cc r k) :=
      ENNReal.tsum_le_tsum (fun k => lintegral_enorm_pow_cos_le r hr u k)
    refine ne_top_of_le_ne_top ?_ hle
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => cc_nonneg hr k) (cc_summable hr)]
    exact ENNReal.ofReal_lt_top.ne
  have h1 := MeasureTheory.integral_tsum (μ := MM r)
    (f := fun (k : ℕ) (s : ℝ) => s ^ k * Real.cos (k * u)) hmeas hsumm
  rw [← MeasureTheory.integral_congr_ae (ae_geom r hr u), h1]
  refine tsum_congr (fun k => ?_)
  rw [MeasureTheory.integral_mul_const]
  rfl

lemma integrable_geom (r : ℕ) (hr : 1 ≤ r) (u : ℝ) :
    Integrable (fun s : ℝ => (1 - s * Real.cos u) / (1 - 2 * s * Real.cos u + s ^ 2))
      (MM r) := by
  have h1 : Integrable (fun s : ℝ => (1 - wfun u s)⁻¹) (MM r) := by
    refine MeasureTheory.Integrable.mono' (integrable_inv_one_sub hr) ?_ ?_
    · have hm : Measurable fun s : ℝ => (1 - wfun u s)⁻¹ := by
        unfold wfun
        fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [MM_ae_mem hr, MM_ae_lt_one hr] with s hs hs1
      have hge : 1 - s ≤ ‖(1 : ℂ) - wfun u s‖ := by
        have h := norm_sub_norm_le (1 : ℂ) (wfun u s)
        rw [norm_one, norm_wfun u s hs.1] at h
        exact h
      have hpos : (0 : ℝ) < ‖(1 : ℂ) - wfun u s‖ := by linarith [hs1]
      rw [norm_inv, inv_le_inv₀ hpos (by linarith : (0:ℝ) < 1 - s)]
      exact hge
  refine Integrable.congr (h1.re) ?_
  filter_upwards [MM_ae_mem hr, MM_ae_lt_one hr] with s hs hs1
  simpa using re_inv_one_sub u s

lemma integrable_inv_one_add (r : ℕ) (hr : 1 ≤ r) :
    Integrable (fun s : ℝ => (1 + s)⁻¹) (MM r) := by
  haveI := MM_prob hr
  refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
  · exact ((measurable_const.add measurable_id).inv).aestronglyMeasurable
  · filter_upwards [MM_ae_mem hr] with s hs
    have hs0 : (0 : ℝ) ≤ s := hs.1
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < (1 + s)⁻¹)]
    exact inv_le_one_of_one_le₀ (by linarith)

lemma geom_ge (r : ℕ) (hr : 1 ≤ r) (u : ℝ) :
    ∫ s, (1 + s)⁻¹ ∂(MM r)
      ≤ ∫ s, (1 - s * Real.cos u) / (1 - 2 * s * Real.cos u + s ^ 2) ∂(MM r) := by
  refine MeasureTheory.integral_mono_ae (integrable_inv_one_add r hr) (integrable_geom r hr u) ?_
  filter_upwards [MM_ae_mem hr, MM_ae_lt_one hr] with s hs hs1
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hc1 : Real.cos u ≤ 1 := Real.cos_le_one u
  have hc2 : -1 ≤ Real.cos u := Real.neg_one_le_cos u
  have hpos1 : (0 : ℝ) < 1 + s := by linarith
  have hpos2 : (0 : ℝ) < 1 - 2 * s * Real.cos u + s ^ 2 := by
    nlinarith [sq_nonneg (1 - s), mul_nonneg (by linarith : (0:ℝ) ≤ 2 * s)
      (by linarith : (0:ℝ) ≤ 1 - Real.cos u)]
  have key : 0 ≤ s * (1 - s) * (1 + Real.cos u) :=
    mul_nonneg (mul_nonneg hs0 (by linarith)) (by linarith)
  rw [inv_eq_one_div, div_le_div_iff₀ hpos1 hpos2]
  nlinarith [key]

/-- **The key inequality**: the cosine transform of the moment sequence is at least its value at
`u = π`, where `cos (k π) = (-1)^k`. -/
theorem cc_geom_ge (r : ℕ) (hr : 1 ≤ r) (u : ℝ) :
    (∑' k : ℕ, (-1) ^ k * cc r k) ≤ ∑' k : ℕ, cc r k * Real.cos (k * u) := by
  have hpi : (∑' k : ℕ, (-1) ^ k * cc r k) = ∫ s, (1 + s)⁻¹ ∂(MM r) := by
    have h := integral_geom r hr Real.pi
    have hleft : (∑' k : ℕ, cc r k * Real.cos (k * Real.pi))
        = ∑' k : ℕ, (-1) ^ k * cc r k := by
      refine tsum_congr (fun k => ?_)
      rw [Real.cos_nat_mul_pi]
      ring
    rw [← hleft, h]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MM_ae_mem hr] with s hs
    have hs0 : (0 : ℝ) ≤ s := hs.1
    rw [Real.cos_pi]
    have hpos : (0 : ℝ) < 1 + s := by linarith
    rw [show (1 : ℝ) - s * (-1) = 1 + s by ring,
      show (1 : ℝ) - 2 * s * (-1) + s ^ 2 = (1 + s) ^ 2 by ring]
    field_simp
  rw [hpi, integral_geom r hr u]
  exact geom_ge r hr u

end Grothendieck

/-! ## Part 4: the trigonometric series of `E_r` on the unit circle -/

namespace Grothendieck

/-- `e^{it}` for real `t`. -/
def zfun (t : ℝ) : ℂ := Complex.exp ((t : ℝ) * Complex.I)

lemma norm_zfun (t : ℝ) : ‖zfun t‖ = 1 := Complex.norm_exp_ofReal_mul_I t

lemma conj_zfun_eq (t : ℝ) : (starRingEnd ℂ) (zfun t) = zfun (-t) := by
  rw [zfun, zfun, ← Complex.exp_conj]
  congr 1
  push_cast
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

lemma conj_zfun_mul (t : ℝ) : (starRingEnd ℂ) (zfun t) * zfun t = 1 := by
  rw [conj_zfun_eq, zfun, zfun, ← Complex.exp_add]
  have h : ((-t : ℝ) : ℂ) * Complex.I + (t : ℂ) * Complex.I = 0 := by
    push_cast
    ring
  rw [h, Complex.exp_zero]

lemma zfun_pow_eq (t : ℝ) (n : ℕ) :
    zfun t ^ n = Complex.exp ((n : ℂ) * ((t : ℂ) * Complex.I)) := by
  rw [zfun, Complex.exp_nat_mul]

lemma re_zfun_pow_even (t : ℝ) (k : ℕ) : ((zfun t) ^ (2 * k)).re = Real.cos (2 * k * t) := by
  rw [zfun_pow_eq]
  have harg : (((2 * k : ℕ) : ℂ)) * ((t : ℂ) * Complex.I)
      = (((2 * k) * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I_re]

lemma summable_ErComplex {r : ℕ} (hr : 1 ≤ r) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable fun k : ℕ => (ErCoeff r k : ℂ) * z ^ (2 * k + 1) := by
  have h2 : ∀ k : ℕ, ‖((ErCoeff r k : ℝ) : ℂ)‖ = ErCoeff r k := fun k => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ErCoeff_nonneg' hr k)]
  refine Summable.of_norm_bounded (summable_ErCoeff' hr) (fun k => ?_)
  rw [norm_mul, h2, norm_pow]
  have h1 : ‖z‖ ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
  calc ErCoeff r k * ‖z‖ ^ (2 * k + 1) ≤ ErCoeff r k * 1 :=
        mul_le_mul_of_nonneg_left h1 (ErCoeff_nonneg' hr k)
    _ = ErCoeff r k := by ring

lemma summable_ErComplex_even {r : ℕ} (hr : 1 ≤ r) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable fun k : ℕ => (ErCoeff r k : ℂ) * z ^ (2 * k) := by
  have h2 : ∀ k : ℕ, ‖((ErCoeff r k : ℝ) : ℂ)‖ = ErCoeff r k := fun k => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ErCoeff_nonneg' hr k)]
  refine Summable.of_norm_bounded (summable_ErCoeff' hr) (fun k => ?_)
  rw [norm_mul, h2, norm_pow]
  have h1 : ‖z‖ ^ (2 * k) ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
  calc ErCoeff r k * ‖z‖ ^ (2 * k) ≤ ErCoeff r k * 1 :=
        mul_le_mul_of_nonneg_left h1 (ErCoeff_nonneg' hr k)
    _ = ErCoeff r k := by ring

lemma conj_mul_ErComplex {r : ℕ} (hr : 1 ≤ r) (t : ℝ) :
    (starRingEnd ℂ) (zfun t) * ErComplex r (zfun t)
      = ∑' k : ℕ, (ErCoeff r k : ℂ) * (zfun t) ^ (2 * k) := by
  have hsumm := summable_ErComplex hr (z := zfun t) (le_of_eq (norm_zfun t))
  rw [ErComplex, ← Summable.tsum_mul_left ((starRingEnd ℂ) (zfun t)) hsumm]
  refine tsum_congr (fun k => ?_)
  have h : (zfun t) ^ (2 * k + 1) = (zfun t) ^ (2 * k) * zfun t := pow_succ _ _
  rw [h]
  calc (starRingEnd ℂ) (zfun t) * ((ErCoeff r k : ℂ) * ((zfun t) ^ (2 * k) * zfun t))
      = (ErCoeff r k : ℂ) * ((zfun t) ^ (2 * k) * ((starRingEnd ℂ) (zfun t) * zfun t)) := by
        ring
    _ = (ErCoeff r k : ℂ) * ((zfun t) ^ (2 * k) * 1) := by rw [conj_zfun_mul]
    _ = (ErCoeff r k : ℂ) * (zfun t) ^ (2 * k) := by ring

/-- The real part of `conj z · E_r z` on the unit circle is the cosine series. -/
lemma trig_le_norm {r : ℕ} (hr : 1 ≤ r) (t : ℝ) :
    (∑' k : ℕ, ErCoeff r k * Real.cos (2 * k * t)) ≤ ‖ErComplex r (zfun t)‖ := by
  have hz : ‖zfun t‖ ≤ 1 := le_of_eq (norm_zfun t)
  have hsumm2 := summable_ErComplex_even hr (z := zfun t) hz
  have hre : ((starRingEnd ℂ) (zfun t) * ErComplex r (zfun t)).re
      = ∑' k : ℕ, ErCoeff r k * Real.cos (2 * k * t) := by
    rw [conj_mul_ErComplex hr t, Complex.re_tsum hsumm2]
    refine tsum_congr (fun k => ?_)
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, re_zfun_pow_even]
    ring
  calc (∑' k : ℕ, ErCoeff r k * Real.cos (2 * k * t))
      = ((starRingEnd ℂ) (zfun t) * ErComplex r (zfun t)).re := hre.symm
    _ ≤ ‖(starRingEnd ℂ) (zfun t) * ErComplex r (zfun t)‖ := Complex.re_le_norm _
    _ = ‖ErComplex r (zfun t)‖ := by rw [norm_mul, RCLike.norm_conj, norm_zfun, one_mul]

lemma summable_cc_cos {r : ℕ} (hr : 1 ≤ r) (v : ℝ) :
    Summable fun k : ℕ => cc r k * Real.cos (k * v) := by
  refine Summable.of_norm_bounded (cc_summable hr) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cc_nonneg hr k)]
  calc cc r k * |Real.cos (k * v)| ≤ cc r k * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (cc_nonneg hr k)
    _ = cc r k := by ring

lemma summable_cc_alt {r : ℕ} (hr : 1 ≤ r) : Summable fun k : ℕ => (-1) ^ k * cc r k := by
  refine Summable.of_norm_bounded (cc_summable hr) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |((-1 : ℝ)) ^ k| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  rw [h1, abs_of_nonneg (cc_nonneg hr k), one_mul]

lemma tsum_ErCoeff_cos_eq (r : ℕ) (hr : 1 ≤ r) (t : ℝ) :
    (∑' k : ℕ, ErCoeff r k * Real.cos (2 * k * t))
      = Cr r * ∑' k : ℕ, cc r k * Real.cos (k * (2 * t)) := by
  rw [← Summable.tsum_mul_left (Cr r) (summable_cc_cos hr (2 * t))]
  refine tsum_congr (fun k => ?_)
  rw [MM_mom hr k]
  ring

lemma tsum_alt_ErCoeff (r : ℕ) (hr : 1 ≤ r) :
    (∑' k : ℕ, ErCoeff r k * (-1) ^ k) = Cr r * ∑' k : ℕ, (-1) ^ k * cc r k := by
  rw [← Summable.tsum_mul_left (Cr r) (summable_cc_alt hr)]
  refine tsum_congr (fun k => ?_)
  rw [MM_mom hr k]
  ring

/-- **The comparison with `u = π`** in the form used below. -/
theorem trig_ge_alt (r : ℕ) (hr : 1 ≤ r) (t : ℝ) :
    (∑' k : ℕ, ErCoeff r k * (-1) ^ k) ≤ ∑' k : ℕ, ErCoeff r k * Real.cos (2 * k * t) := by
  rw [tsum_ErCoeff_cos_eq r hr t, tsum_alt_ErCoeff r hr]
  exact mul_le_mul_of_nonneg_left (cc_geom_ge r hr (2 * t)) (le_of_lt (Cr_pos' hr))

lemma tsum_alt_eq_integral (r : ℕ) (hr : 1 ≤ r) :
    (∑' k : ℕ, (-1) ^ k * cc r k) = ∫ s, (1 + s)⁻¹ ∂(MM r) := by
  have h := integral_geom r hr Real.pi
  have hleft : (∑' k : ℕ, cc r k * Real.cos (k * Real.pi))
      = ∑' k : ℕ, (-1) ^ k * cc r k := by
    refine tsum_congr (fun k => ?_)
    rw [Real.cos_nat_mul_pi]
    ring
  rw [← hleft, h]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MM_ae_mem hr] with s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  rw [Real.cos_pi]
  have hpos : (0 : ℝ) < 1 + s := by linarith
  rw [show (1 : ℝ) - s * (-1) = 1 + s by ring,
    show (1 : ℝ) - 2 * s * (-1) + s ^ 2 = (1 + s) ^ 2 by ring]
  field_simp

lemma ErCoeff_alt_nonneg (r : ℕ) (hr : 1 ≤ r) :
    0 ≤ ∑' k : ℕ, ErCoeff r k * (-1) ^ k := by
  rw [tsum_alt_ErCoeff r hr, tsum_alt_eq_integral r hr]
  refine mul_nonneg (le_of_lt (Cr_pos' hr)) ?_
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [MM_ae_mem hr] with s hs
  have hpos : (0 : ℝ) < 1 + s := by linarith [hs.1]
  positivity

/-- `‖E_r(i)‖` is the alternating sum of the Taylor coefficients. -/
theorem norm_ErComplex_I {r : ℕ} (hr : 1 ≤ r) :
    ‖ErComplex r Complex.I‖ = ∑' k : ℕ, ErCoeff r k * (-1) ^ k := by
  have hzI : ‖(Complex.I : ℂ)‖ ≤ 1 := by simp
  have hsumm := summable_ErComplex hr (z := Complex.I) hzI
  have hsummR : Summable fun k : ℕ => (((ErCoeff r k * (-1) ^ k : ℝ)) : ℂ) := by
    refine Summable.of_norm_bounded (summable_ErCoeff' hr) (fun k => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have h1 : |((-1 : ℝ)) ^ k| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
    rw [h1, abs_of_nonneg (ErCoeff_nonneg' hr k), mul_one]
  have hpow : ∀ k : ℕ, (Complex.I) ^ (2 * k + 1) = Complex.I * (((-1 : ℝ) ^ k : ℝ) : ℂ) := by
    intro k
    rw [pow_succ, pow_mul, pow_two, Complex.I_mul_I]
    have : ((-1 : ℂ)) ^ k = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    ring
  have hI : ErComplex r Complex.I
      = Complex.I * ((∑' k : ℕ, ErCoeff r k * (-1) ^ k : ℝ) : ℂ) := by
    rw [ErComplex, Complex.ofReal_tsum, ← Summable.tsum_mul_left Complex.I hsummR]
    refine tsum_congr (fun k => ?_)
    rw [hpow]
    push_cast
    ring
  rw [hI, norm_mul, Complex.norm_I, one_mul]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ErCoeff_alt_nonneg r hr)]

theorem cr_eq_norm_er_I_proof (r : ℕ) (hr : 2 ≤ r) : cr r = ‖ErComplex r Complex.I‖ := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hexp : ∀ t : ℝ, zfun t = Complex.exp (Complex.I * t) := by
    intro t
    rw [zfun, mul_comm]
  have hmain : ∀ t : ℝ, ‖ErComplex r Complex.I‖ ≤ ‖ErComplex r (Complex.exp (Complex.I * t))‖ := by
    intro t
    have h1 : ‖ErComplex r Complex.I‖ = ∑' k : ℕ, ErCoeff r k * (-1) ^ k := norm_ErComplex_I hr1
    have h2 : (∑' k : ℕ, ErCoeff r k * Real.cos (2 * k * t))
        ≤ ‖ErComplex r (zfun t)‖ := trig_le_norm hr1 t
    have h3 : (∑' k : ℕ, ErCoeff r k * (-1) ^ k)
        ≤ ∑' k : ℕ, ErCoeff r k * Real.cos (2 * k * t) := trig_ge_alt r hr1 t
    rw [h1, ← hexp t]
    linarith
  have hexpI : Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  refine le_antisymm ?_ ?_
  · refine csInf_le ?_ ?_
    · exact ⟨0, by rintro y ⟨t, -, rfl⟩; positivity⟩
    · exact ⟨Real.pi / 2, ⟨by positivity, by linarith [Real.pi_pos]⟩, by rw [hexpI]⟩
  · refine le_csInf ?_ ?_
    · exact ⟨_, ⟨0, ⟨le_refl 0, by positivity⟩, rfl⟩⟩
    · rintro y ⟨t, -, rfl⟩
      exact hmain t

end Grothendieck

open Grothendieck in
theorem solution (r : ℕ) (hr : 2 ≤ r) : cr r = ‖ErComplex r Complex.I‖ :=
  cr_eq_norm_er_I_proof r hr
