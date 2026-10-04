-- Prove2me | solution 1 for HighDimProb.RandomVectors.grothendieck_inequality
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T05:18:43.329593+00:00
-- url     : https://prove2.me/submissions/263c6642-9509-49ad-b7a7-8949a786e50f

import Mathlib

-- HansonGaussianLaplace (scalar lemma)

open MeasureTheory ProbabilityTheory Real

namespace HansonWrightGaussian

lemma gaussian_sq_laplace (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1 / 4) :
    Integrable (fun x : ℝ => exp (a * x ^ 2)) (gaussianReal 0 1) ∧
      (∫ x : ℝ, exp (a * x ^ 2) ∂gaussianReal 0 1) ≤ exp (2 * a) := by
  have hb : 0 < 1 / 2 - a := by linarith
  have hd : 0 < 1 - 2 * a := by linarith
  have hp : 0 < 2 * Real.pi := by positivity
  have hw : ∀ x : ℝ, gaussianPDFReal 0 1 x * exp (a * x ^ 2) =
      (sqrt (2 * Real.pi))⁻¹ * exp (-(1 / 2 - a) * x ^ 2) := by
    intro x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← exp_add]
    congr 2
    ring
  have hwi : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * exp (a * x ^ 2)) := by
    simp_rw [hw]
    exact (integrable_exp_neg_mul_sq hb).const_mul _
  have hi : Integrable (fun x : ℝ => exp (a * x ^ 2)) (gaussianReal 0 1) := by
    rw [gaussianReal_of_var_ne_zero _ (one_ne_zero : (1 : NNReal) ≠ 0)]
    apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)).mpr
    simpa only [toReal_gaussianPDF, smul_eq_mul] using hwi
  have heq : (∫ x : ℝ, exp (a * x ^ 2) ∂gaussianReal 0 1) =
      (sqrt (2 * Real.pi))⁻¹ * sqrt (Real.pi / (1 / 2 - a)) := by
    rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : NNReal) ≠ 0)]
    simp_rw [smul_eq_mul, hw]
    rw [integral_const_mul, integral_gaussian]
  refine ⟨hi, ?_⟩
  rw [heq]
  set R := (sqrt (2 * Real.pi))⁻¹ * sqrt (Real.pi / (1 / 2 - a))
  have hR : 0 ≤ R := by positivity
  have hsq : R ^ 2 * (1 - 2 * a) = 1 := by
    dsimp [R]
    rw [mul_pow, inv_pow, sq_sqrt hp.le, sq_sqrt (by positivity)]
    field_simp
  have hex : 1 ≤ exp (4 * a) * (1 - 2 * a) := by
    have h := mul_le_mul_of_nonneg_right (add_one_le_exp (4 * a)) hd.le
    nlinarith
  have he2 : exp (2 * a) ^ 2 = exp (4 * a) := by
    rw [sq, ← exp_add]
    congr 1
    ring
  have hsqle : R ^ 2 ≤ exp (2 * a) ^ 2 := by
    apply le_of_mul_le_mul_right (show R ^ 2 * (1 - 2 * a) ≤
      exp (2 * a) ^ 2 * (1 - 2 * a) from ?_) hd
    rw [hsq, he2]
    exact hex
  exact (sq_le_sq₀ hR (exp_pos _).le).mp hsqle


end HansonWrightGaussian

-- GrothendieckSupremum

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace GrothendieckProof

def values {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) : Set ℝ := fun r =>
  ∃ H : Type, ∃ hN : NormedAddCommGroup H,
    letI := hN
    ∃ hI : InnerProductSpace ℝ H,
      letI := hI
      ∃ u : Fin m → H, ∃ v : Fin n → H,
        (∀ i, ‖u i‖ ≤ 1) ∧ (∀ j, ‖v j‖ ≤ 1) ∧
          r = |∑ i, ∑ j, a i j * ⟪u i, v j⟫|

noncomputable def hilbertBound {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  sSup (values a)

lemma value_mem {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : Fin m → H) (v : Fin n → H)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1) :
    |∑ i, ∑ j, a i j * ⟪u i, v j⟫| ∈ values a :=
  ⟨H, inferInstance, inferInstance, u, v, hu, hv, rfl⟩

lemma values_bddAbove {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) :
    BddAbove (values a) := by
  refine ⟨∑ i, ∑ j, |a i j|, ?_⟩
  rintro r ⟨H, hN, hI, u, v, hu, hv, rfl⟩
  letI := hN
  letI := hI
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul]
  apply mul_le_of_le_one_right (abs_nonneg _)
  calc |⟪u i, v j⟫| ≤ ‖u i‖ * ‖v j‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * 1 := mul_le_mul (hu i) (hv j) (norm_nonneg _) (by norm_num)
    _ = 1 := by ring

lemma values_nonempty {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) :
    (values a).Nonempty := by
  refine ⟨0, ?_⟩
  have h := value_mem a (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
    (by simp) (by simp)
  simpa using h

lemma bilinear_le_bound {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : Fin m → H) (v : Fin n → H)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1) :
    |∑ i, ∑ j, a i j * ⟪u i, v j⟫| ≤ hilbertBound a :=
  le_csSup (values_bddAbove a) (value_mem a u v hu hv)

lemma bound_nonneg {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ hilbertBound a := by
  have h := bilinear_le_bound a (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
    (by simp) (by simp)
  simpa using h

lemma quarter_left {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : Fin m → H) (v : Fin n → H)
    (hu : ∀ i, ‖u i‖ ≤ 1 / 4) (hv : ∀ j, ‖v j‖ ≤ 1) :
    |∑ i, ∑ j, a i j * ⟪u i, v j⟫| ≤ hilbertBound a / 4 := by
  have h := bilinear_le_bound a (fun i => (4 : ℝ) • u i) v
    (fun i => by simpa [norm_smul] using (show 4 * ‖u i‖ ≤ 1 by linarith [hu i])) hv
  have he : (∑ i, ∑ j, a i j * ⟪(4 : ℝ) • u i, v j⟫) =
      4 * ∑ i, ∑ j, a i j * ⟪u i, v j⟫ := by
    simp_rw [real_inner_smul_left]
    simp_rw [← mul_assoc, mul_comm (a _ _) 4, mul_assoc]
    simp_rw [← Finset.mul_sum]
  rw [he, abs_mul] at h
  norm_num at h
  linarith

lemma quarter_right {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : Fin m → H) (v : Fin n → H)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1 / 4) :
    |∑ i, ∑ j, a i j * ⟪u i, v j⟫| ≤ hilbertBound a / 4 := by
  have h := bilinear_le_bound a u (fun j => (4 : ℝ) • v j) hu
    (fun j => by simpa [norm_smul] using (show 4 * ‖v j‖ ≤ 1 by linarith [hv j]))
  have he : (∑ i, ∑ j, a i j * ⟪u i, (4 : ℝ) • v j⟫) =
      4 * ∑ i, ∑ j, a i j * ⟪u i, v j⟫ := by
    simp_rw [real_inner_smul_right]
    simp_rw [← mul_assoc, mul_comm (a _ _) 4, mul_assoc]
    simp_rw [← Finset.mul_sum]
  rw [he, abs_mul] at h
  norm_num at h
  linarith

lemma linear_cube {ι : Type*} [Fintype ι] (c x : ι → ℝ) (B : ℝ)
    (hs : ∀ s : ι → ℝ, (∀ i, s i = 1 ∨ s i = -1) → |∑ i, c i * s i| ≤ B)
    (hx : ∀ i, |x i| ≤ 1) : |∑ i, c i * x i| ≤ B := by
  classical
  let s : ι → ℝ := fun i => if 0 ≤ c i then 1 else -1
  have hsign : ∀ i, s i = 1 ∨ s i = -1 := by
    intro i
    dsimp [s]
    split_ifs <;> simp
  have he : (∑ i, c i * s i) = ∑ i, |c i| := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [s]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  have hb := hs s hsign
  rw [he, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))] at hb
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply le_trans _ hb
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hx i)

lemma bilinear_cube {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ)
    (hs : ∀ x : Fin m → ℝ, ∀ y : Fin n → ℝ,
      (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
      |∑ i, ∑ j, a i j * x i * y j| ≤ 1)
    (x : Fin m → ℝ) (y : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ j, |y j| ≤ 1) :
    |∑ i, ∑ j, a i j * x i * y j| ≤ 1 := by
  have hfirst (s : Fin n → ℝ) (hss : ∀ j, s j = 1 ∨ s j = -1) :
      |∑ i, ∑ j, a i j * x i * s j| ≤ 1 := by
    have he (r : Fin m → ℝ) :
        (∑ i, (∑ j, a i j * s j) * r i) = ∑ i, ∑ j, a i j * r i * s j := by
      simp_rw [Finset.sum_mul]
      congr 1
      funext i
      apply Finset.sum_congr rfl
      intro j _
      ring
    have h := linear_cube (fun i => ∑ j, a i j * s j) x 1
      (fun r hr => by rw [he]; exact hs r s hr hss) hx
    rwa [he] at h
  have he (s : Fin n → ℝ) :
      (∑ j, (∑ i, a i j * x i) * s j) = ∑ i, ∑ j, a i j * x i * s j := by
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  have h := linear_cube (fun j => ∑ i, a i j * x i) y 1
    (fun s hss => by rw [he]; exact hfirst s hss) hy
  rwa [he] at h

end GrothendieckProof

-- GrothendieckGaussian

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory Real

namespace GrothendieckProof

noncomputable def clip (x : ℝ) : ℝ := max (-12) (min 12 x)

@[fun_prop] lemma continuous_clip : Continuous clip := by unfold clip; fun_prop

lemma abs_clip_le (x : ℝ) : |clip x| ≤ 12 := by
  unfold clip
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma abs_clip_le_self (x : ℝ) : |clip x| ≤ |x| := by
  unfold clip
  by_cases h1 : x ≤ -12
  · rw [min_eq_right (by linarith : x ≤ 12), max_eq_left h1,
      abs_of_nonpos (by norm_num), abs_of_nonpos (by linarith : x ≤ 0)]
    linarith
  · by_cases h2 : 12 ≤ x
    · rw [min_eq_left h2, max_eq_right (by norm_num : (-12 : ℝ) ≤ 12),
        abs_of_nonneg (by norm_num), abs_of_nonneg (by linarith : 0 ≤ x)]
      exact h2
    · rw [min_eq_right (le_of_not_ge h2), max_eq_right (le_of_not_ge h1)]

lemma abs_residual_le (x : ℝ) : |x - clip x| ≤ |x| := by
  unfold clip
  by_cases h1 : x ≤ -12
  · rw [min_eq_right (by linarith : x ≤ 12), max_eq_left h1,
      abs_of_nonpos (by linarith : x - -12 ≤ 0),
      abs_of_nonpos (by linarith : x ≤ 0)]
    linarith
  · by_cases h2 : 12 ≤ x
    · rw [min_eq_left h2, max_eq_right (by norm_num : (-12 : ℝ) ≤ 12),
        abs_of_nonneg (by linarith : 0 ≤ x - 12),
        abs_of_nonneg (by linarith : 0 ≤ x)]
      linarith
    · rw [min_eq_right (le_of_not_ge h2), max_eq_right (le_of_not_ge h1)]
      simp

lemma residual_sq_le_exp (x : ℝ) :
    (x - clip x) ^ 2 ≤ exp (x ^ 2 / 4) / 32 := by
  by_cases hx : |x| ≤ 12
  · have hx' := abs_le.mp hx
    have he : clip x = x := by
      unfold clip
      rw [min_eq_right hx'.2, max_eq_right hx'.1]
    rw [he, sub_self, zero_pow (by decide)]
    positivity
  · have hx2 : (144 : ℝ) ≤ x ^ 2 := by
      have h := le_of_lt (lt_of_not_ge hx)
      have hh := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 12) (abs_nonneg x)).mpr h
      norm_num [sq_abs] at hh
      exact hh
    have hx4 : (144 : ℝ) ^ 2 ≤ (x ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hx2 2
    have hx6 := mul_le_mul_of_nonneg_right hx4 (sq_nonneg x)
    have he := Real.pow_div_factorial_le_exp (x ^ 2 / 4) (by positivity) 3
    norm_num at he
    have hlarge : 32 * x ^ 2 ≤ exp (x ^ 2 / 4) := by
      nlinarith only [he, hx6, sq_nonneg x]
    have hr : (x - clip x) ^ 2 ≤ x ^ 2 := by
      exact sq_le_sq.mpr (abs_residual_le x)
    linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_inner_memLp (u : E) :
    MemLp (fun g : E => ⟪u, g⟫) 2 (stdGaussian E) := by
  exact (IsGaussian.hasGaussianLaw_id.map (innerSL ℝ u)).memLp_two

lemma gaussian_inner_product (u v : E) :
    (∫ g : E, ⟪u, g⟫ * ⟪v, g⟫ ∂stdGaussian E) = ⟪u, v⟫ := by
  have h := covarianceBilin_apply (μ := stdGaussian E) IsGaussian.memLp_two_id u v
  simp only [id_eq, integral_id_stdGaussian, sub_zero] at h
  rw [covarianceBilin_stdGaussian, innerSL_apply_apply] at h
  exact h.symm

lemma gaussian_inner_law (u : E) :
    (stdGaussian E).map (fun g : E => ⟪u, g⟫) =
      (gaussianReal 0 1).map (fun x : ℝ => ‖u‖ * x) := by
  change (stdGaussian E).map (innerSL ℝ u) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm, gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one]
  congr 1
  apply NNReal.eq
  simp [Real.toNNReal_of_nonneg (sq_nonneg ‖u‖)]

lemma gaussian_inner_sq_laplace (u : E) (hu : ‖u‖ ≤ 1) :
    Integrable (fun g : E => exp (⟪u, g⟫ ^ 2 / 4)) (stdGaussian E) ∧
      (∫ g : E, exp (⟪u, g⟫ ^ 2 / 4) ∂stdGaussian E) ≤ 2 := by
  have hsq : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hh := HansonWrightGaussian.gaussian_sq_laplace (‖u‖ ^ 2 / 4)
    (by positivity) (by linarith)
  have he (x : ℝ) : exp ((‖u‖ * x) ^ 2 / 4) = exp ((‖u‖ ^ 2 / 4) * x ^ 2) := by
    congr 1
    ring
  have hmap := gaussian_inner_law u
  have hi : Integrable (fun x : ℝ => exp (x ^ 2 / 4))
      ((stdGaussian E).map (fun g : E => ⟪u, g⟫)) := by
    rw [hmap, integrable_map_measure (by fun_prop) (by fun_prop)]
    simpa only [Function.comp_def, he] using hh.1
  have hi' := (integrable_map_measure
    (g := fun x : ℝ => exp (x ^ 2 / 4))
    (by fun_prop) (show AEMeasurable (fun g : E => ⟪u, g⟫) (stdGaussian E) by fun_prop)).mp hi
  refine ⟨hi', ?_⟩
  have hh' : (∫ g : E, exp (⟪u, g⟫ ^ 2 / 4) ∂stdGaussian E) ≤
      exp (2 * (‖u‖ ^ 2 / 4)) := by
    rw [← integral_map (f := fun x : ℝ => exp (x ^ 2 / 4))
      (by fun_prop) (by fun_prop), hmap,
      integral_map (by fun_prop) (by fun_prop)]
    simpa only [he] using hh.2
  apply hh'.trans
  calc exp (2 * (‖u‖ ^ 2 / 4)) ≤ exp (1 / 2) := exp_le_exp.mpr (by linarith)
    _ ≤ 2 := by
      have h := exp_bound_div_one_sub_of_interval (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      norm_num at h ⊢
      exact h

lemma clip_gaussian_memLp (u : E) :
    MemLp (fun g : E => clip ⟪u, g⟫) 2 (stdGaussian E) := by
  apply (gaussian_inner_memLp u).mono (by fun_prop)
  exact Filter.Eventually.of_forall (fun g => by
    simpa only [Real.norm_eq_abs] using abs_clip_le_self ⟪u, g⟫)

lemma residual_gaussian_memLp (u : E) :
    MemLp (fun g : E => ⟪u, g⟫ - clip ⟪u, g⟫) 2 (stdGaussian E) :=
  (gaussian_inner_memLp u).sub (clip_gaussian_memLp u)

lemma residual_gaussian_sq (u : E) (hu : ‖u‖ ≤ 1) :
    (∫ g : E, (⟪u, g⟫ - clip ⟪u, g⟫) ^ 2 ∂stdGaussian E) ≤ 1 / 16 := by
  have hh := gaussian_inner_sq_laplace u hu
  calc (∫ g : E, (⟪u, g⟫ - clip ⟪u, g⟫) ^ 2 ∂stdGaussian E)
      ≤ ∫ g : E, exp (⟪u, g⟫ ^ 2 / 4) / 32 ∂stdGaussian E :=
        integral_mono (residual_gaussian_memLp u).integrable_sq (hh.1.div_const _)
          (fun g => residual_sq_le_exp _)
    _ = (∫ g : E, exp (⟪u, g⟫ ^ 2 / 4) ∂stdGaussian E) / 32 := integral_div _ _
    _ ≤ 1 / 16 := by linarith [hh.2]

end GrothendieckProof

-- GrothendieckL2

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory Real

namespace GrothendieckProof

lemma inner_toLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hf hg
  simp [hf, hg, RCLike.inner_apply, mul_comm]

lemma norm_sq_toLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp]
  simp only [pow_two]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def gaussianLp (u : E) : Lp ℝ 2 (stdGaussian E) :=
  (gaussian_inner_memLp u).toLp (fun g : E => ⟪u, g⟫)

noncomputable def clippedLp (u : E) : Lp ℝ 2 (stdGaussian E) :=
  (clip_gaussian_memLp u).toLp (fun g : E => clip ⟪u, g⟫)

noncomputable def residualLp (u : E) : Lp ℝ 2 (stdGaussian E) :=
  (residual_gaussian_memLp u).toLp (fun g : E => ⟪u, g⟫ - clip ⟪u, g⟫)

lemma gaussianLp_eq (u : E) : gaussianLp u = clippedLp u + residualLp u := by
  have h : residualLp u = gaussianLp u - clippedLp u := by
    unfold residualLp gaussianLp clippedLp
    exact MemLp.toLp_sub _ _
  rw [h]
  abel

lemma gaussianLp_inner (u v : E) : ⟪gaussianLp u, gaussianLp v⟫ = ⟪u, v⟫ := by
  unfold gaussianLp
  rw [inner_toLp, gaussian_inner_product]

lemma gaussianLp_norm (u : E) : ‖gaussianLp u‖ = ‖u‖ := by
  have h : ‖gaussianLp u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, gaussianLp_inner, real_inner_self_eq_norm_sq]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

lemma clippedLp_norm (u : E) (hu : ‖u‖ ≤ 1) : ‖clippedLp u‖ ≤ 1 := by
  have h : ‖clippedLp u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    unfold clippedLp
    rw [norm_sq_toLp]
    have hpoint (g : E) : (clip ⟪u, g⟫) ^ 2 ≤ ⟪u, g⟫ ^ 2 :=
      sq_le_sq.mpr (abs_clip_le_self _)
    calc (∫ g : E, (clip ⟪u, g⟫) ^ 2 ∂stdGaussian E)
        ≤ ∫ g : E, ⟪u, g⟫ ^ 2 ∂stdGaussian E :=
          integral_mono (clip_gaussian_memLp u).integrable_sq
            (gaussian_inner_memLp u).integrable_sq hpoint
      _ = ‖u‖ ^ 2 := by
        simp_rw [pow_two]
        rw [gaussian_inner_product, real_inner_self_eq_norm_sq]
        ring
  have hsq : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
  nlinarith [norm_nonneg (clippedLp u)]

lemma residualLp_norm (u : E) (hu : ‖u‖ ≤ 1) : ‖residualLp u‖ ≤ 1 / 4 := by
  have h : ‖residualLp u‖ ^ 2 ≤ 1 / 16 := by
    unfold residualLp
    rw [norm_sq_toLp]
    exact residual_gaussian_sq u hu
  nlinarith [norm_nonneg (residualLp u)]

lemma bilinear_twelve {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ)
    (hs : ∀ x : Fin m → ℝ, ∀ y : Fin n → ℝ,
      (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
      |∑ i, ∑ j, a i j * x i * y j| ≤ 1)
    (x : Fin m → ℝ) (y : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 12) (hy : ∀ j, |y j| ≤ 12) :
    |∑ i, ∑ j, a i j * x i * y j| ≤ 144 := by
  have h := bilinear_cube a hs (fun i => x i / 12) (fun j => y j / 12)
    (fun i => by rw [abs_div]; norm_num; linarith [hx i])
    (fun j => by rw [abs_div]; norm_num; linarith [hy j])
  have he : (∑ i, ∑ j, a i j * (x i / 12) * (y j / 12)) =
      (∑ i, ∑ j, a i j * x i * y j) / 144 := by
    simp_rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, abs_div] at h
  norm_num at h
  linarith

end GrothendieckProof

-- GrothendieckContraction

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory Real

namespace GrothendieckProof

variable {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ)
  (hs : ∀ x : Fin m → ℝ, ∀ y : Fin n → ℝ,
    (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
    |∑ i, ∑ j, a i j * x i * y j| ≤ 1)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

include hs

lemma clipped_bilinear (u : Fin m → E) (v : Fin n → E) :
    |∑ i, ∑ j, a i j * ⟪clippedLp (u i), clippedLp (v j)⟫| ≤ 144 := by
  have hi (i : Fin m) (j : Fin n) :
      Integrable (fun g : E => a i j * clip ⟪u i, g⟫ * clip ⟪v j, g⟫) (stdGaussian E) := by
    have h := ((clip_gaussian_memLp (u i)).integrable_mul
      (clip_gaussian_memLp (v j))).const_mul (a i j)
    simpa only [Pi.mul_apply, mul_assoc] using h
  have his (i : Fin m) :
      Integrable (fun g : E => ∑ j, a i j * clip ⟪u i, g⟫ * clip ⟪v j, g⟫)
        (stdGaussian E) := integrable_finsetSum _ (fun j _ => hi i j)
  have hit : Integrable
      (fun g : E => ∑ i, ∑ j, a i j * clip ⟪u i, g⟫ * clip ⟪v j, g⟫)
      (stdGaussian E) := integrable_finsetSum _ (fun i _ => his i)
  have he : (∑ i, ∑ j, a i j * ⟪clippedLp (u i), clippedLp (v j)⟫) =
      ∫ g : E, ∑ i, ∑ j, a i j * clip ⟪u i, g⟫ * clip ⟪v j, g⟫ ∂stdGaussian E := by
    rw [integral_finsetSum Finset.univ (fun i _ => his i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
    apply Finset.sum_congr rfl
    intro j _
    unfold clippedLp
    rw [inner_toLp]
    simpa only [mul_assoc] using (integral_const_mul (a i j)
      (fun g : E => clip ⟪u i, g⟫ * clip ⟪v j, g⟫)).symm
  rw [he]
  apply abs_integral_le_integral_abs.trans
  calc (∫ g : E, |∑ i, ∑ j, a i j * clip ⟪u i, g⟫ * clip ⟪v j, g⟫| ∂stdGaussian E)
      ≤ ∫ _g : E, (144 : ℝ) ∂stdGaussian E :=
        integral_mono hit.abs (integrable_const _)
          (fun g => bilinear_twelve a hs (fun i => clip ⟪u i, g⟫)
            (fun j => clip ⟪v j, g⟫) (fun _ => abs_clip_le _) (fun _ => abs_clip_le _))
    _ = 144 := by simp

lemma finite_contraction (u : Fin m → E) (v : Fin n → E)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1) :
    |∑ i, ∑ j, a i j * ⟪u i, v j⟫| ≤ 144 + hilbertBound a / 2 := by
  have hc := clipped_bilinear a hs u v
  have hr := quarter_left a (fun i => residualLp (u i)) (fun j => gaussianLp (v j))
    (fun i => residualLp_norm _ (hu i))
    (fun j => by rw [gaussianLp_norm]; exact hv j)
  have hl := quarter_right a (fun i => clippedLp (u i)) (fun j => residualLp (v j))
    (fun i => clippedLp_norm _ (hu i)) (fun j => residualLp_norm _ (hv j))
  have he : (∑ i, ∑ j, a i j * ⟪u i, v j⟫) =
      (∑ i, ∑ j, a i j * ⟪clippedLp (u i), clippedLp (v j)⟫) +
      (∑ i, ∑ j, a i j * ⟪residualLp (u i), gaussianLp (v j)⟫) +
      (∑ i, ∑ j, a i j * ⟪clippedLp (u i), residualLp (v j)⟫) := by
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← gaussianLp_inner, gaussianLp_eq (u i), inner_add_left]
    nth_rw 1 [gaussianLp_eq (v j)]
    rw [inner_add_right]
    ring
  rw [he]
  have ht := abs_add_le
    ((∑ i, ∑ j, a i j * ⟪clippedLp (u i), clippedLp (v j)⟫) +
      (∑ i, ∑ j, a i j * ⟪residualLp (u i), gaussianLp (v j)⟫))
    (∑ i, ∑ j, a i j * ⟪clippedLp (u i), residualLp (v j)⟫)
  have ht' := abs_add_le
    (∑ i, ∑ j, a i j * ⟪clippedLp (u i), clippedLp (v j)⟫)
    (∑ i, ∑ j, a i j * ⟪residualLp (u i), gaussianLp (v j)⟫)
  linarith

end GrothendieckProof

-- GrothendieckComplete

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory Real

namespace GrothendieckProof

lemma arbitrary_contraction {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ)
    (hs : ∀ x : Fin m → ℝ, ∀ y : Fin n → ℝ,
      (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
      |∑ i, ∑ j, a i j * x i * y j| ≤ 1)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : Fin m → H) (v : Fin n → H)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1) :
    |∑ i, ∑ j, a i j * ⟪u i, v j⟫| ≤ 144 + hilbertBound a / 2 := by
  classical
  let S : Submodule ℝ H := Submodule.span ℝ (Set.range u ∪ Set.range v)
  letI : FiniteDimensional ℝ S :=
    FiniteDimensional.span_of_finite ℝ ((Set.finite_range u).union (Set.finite_range v))
  letI : MeasurableSpace S := borel S
  letI : BorelSpace S := ⟨rfl⟩
  let uS : Fin m → S := fun i => ⟨u i,
    Submodule.subset_span (Set.mem_union_left _ (Set.mem_range_self i))⟩
  let vS : Fin n → S := fun j => ⟨v j,
    Submodule.subset_span (Set.mem_union_right _ (Set.mem_range_self j))⟩
  exact finite_contraction a hs uS vS hu hv

lemma hilbertBound_le {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ)
    (hs : ∀ x : Fin m → ℝ, ∀ y : Fin n → ℝ,
      (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
      |∑ i, ∑ j, a i j * x i * y j| ≤ 1) : hilbertBound a ≤ 288 := by
  have h : hilbertBound a ≤ 144 + hilbertBound a / 2 := by
    apply csSup_le (values_nonempty a)
    rintro r ⟨H, hN, hI, u, v, hu, hv, rfl⟩
    letI := hN
    letI := hI
    exact arbitrary_contraction a hs u v hu hv
  linarith

theorem grothendieck_complete :
    ∃ K : ℝ, 0 < K ∧ K ≤ 288 ∧
      ∀ {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ),
        (∀ x : Fin m → ℝ, ∀ y : Fin n → ℝ, (∀ i, x i = 1 ∨ x i = -1) →
          (∀ j, y j = 1 ∨ y j = -1) → |∑ i, ∑ j, a i j * x i * y j| ≤ 1) →
        ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
          (u : Fin m → H) (v : Fin n → H),
          (∀ i, ‖u i‖ = 1) → (∀ j, ‖v j‖ = 1) →
          |∑ i, ∑ j, a i j * inner ℝ (u i) (v j)| ≤ K := by
  refine ⟨288, by norm_num, le_rfl, ?_⟩
  intro m n a hs H _ _ _ u v hu hv
  exact (bilinear_le_bound a u v (fun i => (hu i).le) (fun j => (hv j).le)).trans
    (hilbertBound_le a hs)


end GrothendieckProof

theorem solution :
    ∃ K : ℝ, 0 < K ∧ K ≤ 288 ∧
      ∀ {m n : ℕ} (a : Matrix (Fin m) (Fin n) ℝ),
        (∀ x : Fin m → ℝ, ∀ y : Fin n → ℝ, (∀ i, x i = 1 ∨ x i = -1) →
          (∀ j, y j = 1 ∨ y j = -1) → |∑ i, ∑ j, a i j * x i * y j| ≤ 1) →
        ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
          (u : Fin m → H) (v : Fin n → H),
          (∀ i, ‖u i‖ = 1) → (∀ j, ‖v j‖ = 1) →
          |∑ i, ∑ j, a i j * inner ℝ (u i) (v j)| ≤ K :=
  GrothendieckProof.grothendieck_complete

#print axioms solution
