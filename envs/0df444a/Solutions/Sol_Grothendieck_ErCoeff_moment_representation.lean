-- Prove2me | solution 1 for Grothendieck.ErCoeff_moment_representation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T14:49:31.934838+00:00
-- url     : https://prove2.me/submissions/811924bb-3fcc-4594-b6fd-ef7e05ce2ed8

import Mathlib
import Definitions.Def_Grothendieck_Series

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
theorem solution (r : ℕ) (hr : 1 ≤ r) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ k : ℕ, ErCoeff r k = Cr r * ∫ x, x ^ k ∂μ :=
  ErCoeff_moment_representation_proof r hr
