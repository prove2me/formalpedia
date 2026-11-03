-- Prove2me | solution 1 for Grothendieck.matrix_grothendieck_identity_of_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T14:28:30.967964+00:00
-- url     : https://prove2.me/submissions/dea2cdac-43e1-4999-b145-501ef34f249c

import Mathlib
import Definitions.Def_Grothendieck_Series
import Definitions.Def_Grothendieck_Gaussian
import Definitions.Def_Grothendieck_Reduced

/-!
# Reduction of Lemma 2.1 (matrix_grothendieck_identity) to a two-column integral

The expectation `grothendieckExpectation r n u v` of Lemma 2.1 is an integral over the
`r × n` standard Gaussian matrix `Z` of `⟪Zu/‖Zu‖, Zv/‖Zv‖⟫`.  This file proves that it
equals an integral over the explicit law of the two columns `(Zu, Zv)`: the `r` rows of
that pair are independent and each row is a two-dimensional Gaussian with covariance
`!![1, t; t, 1]`, `t = ⟪u, v⟫`.  In particular the expectation depends only on `⟪u, v⟫`.

This is the measure-theoretic step that every computation of `Er r (⟪u,v⟫)` presupposes.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Real RealInnerProductSpace

namespace Grothendieck

/-! ### Small facts about Euclidean space coercions -/

lemma equiv_apply_eq_ofLp {m : Type*} [Fintype m] (x : EuclideanSpace ℝ m) (i : m) :
    (EuclideanSpace.equiv m ℝ) x i = x.ofLp i := by
  rw [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_apply]

lemma ofLp_equiv_symm {m : Type*} [Fintype m] (y : m → ℝ) (i : m) :
    ((EuclideanSpace.equiv m ℝ).symm y).ofLp i = y i := by
  simp [EuclideanSpace.equiv]

/-! ### The `2 × 2` correlation matrix -/

/-- The covariance matrix `!![1, t; t, 1]` of two standard Gaussians with correlation `t`. -/

lemma isHermitian_corrMat (t : ℝ) : (corrMat t).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp

lemma corrMat_posSemidef {t : ℝ} (ht : |t| ≤ 1) : (corrMat t).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_corrMat t) fun x => ?_
  simp only [star_trivial, Matrix.mulVec, dotProduct, Fin.sum_univ_two, corrMat_apply_zero_zero,
    corrMat_apply_zero_one, corrMat_apply_one_zero, corrMat_apply_one_one]
  have h1 : (0:ℝ) ≤ 1 - t^2 := by
    have := abs_le.mp ht
    nlinarith
  nlinarith [sq_nonneg (x 0 + t * x 1), sq_nonneg (x 1), h1, mul_nonneg h1 (sq_nonneg (x 1))]

/-- The one-dimensional Gaussian integral of a complex exponential. -/
lemma integral_gaussian_exp (c : ℝ) :
    ∫ t : ℝ, Complex.exp (↑(t * c) * Complex.I) ∂(gaussianReal 0 1)
      = Complex.exp (-↑(c ^ 2) / 2) := by
  simp only [← Real.inner_apply]
  rw [← charFun_apply, charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one, one_mul]
  congr 1
  rw [Complex.ofReal_pow]
  ring

/-! ### The two coordinate projections of one Gaussian row -/

/-- The map sending one Gaussian row `x ∈ ℝ^n` to the pair `(⟪u,x⟫, ⟪v,x⟫) ∈ ℝ²`. -/
lemma continuous_projFun {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) : Continuous (projFun u v) := by
  unfold projFun
  fun_prop

lemma measurable_projFun {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) : Measurable (projFun u v) :=
  (continuous_projFun u v).measurable

lemma inner_projFun {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) (x : Fin n → ℝ)
    (z : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (projFun u v x) z = ∑ k, x k * (z.ofLp 0 * u.ofLp k + z.ofLp 1 * v.ofLp k) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, projFun, Fin.sum_univ_two, Finset.mul_sum,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, Fin.mk_one]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-! ### The law of one row -/

/-- **The law of one projected Gaussian row**: if `u` and `v` are unit vectors, the image of
the standard Gaussian measure on `ℝ^n` under `x ↦ (⟪u,x⟫, ⟪v,x⟫)` is the two-dimensional
Gaussian with covariance `!![1, t; t, 1]`, `t = ⟪u,v⟫`. -/
theorem map_projFun_eq {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Measure.map (projFun u v) (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      = multivariateGaussian 0 (corrMat (inner ℝ u v)) := by
  have habs : |inner ℝ u v| ≤ 1 := by
    have h := norm_inner_le_norm (𝕜 := ℝ) u v
    rw [hu, hv, mul_one] at h
    simpa using h
  have hS : (corrMat (inner ℝ u v)).PosSemidef := corrMat_posSemidef habs
  apply Measure.ext_of_charFun
  ext z
  rw [charFun_multivariateGaussian hS]
  simp only [inner_zero_right, Complex.ofReal_zero, mul_zero, zero_mul, sub_zero]
  rw [charFun_apply]
  have hcont : Continuous fun y : EuclideanSpace ℝ (Fin 2) =>
      Complex.exp (↑⟪y, z⟫ * Complex.I) := by fun_prop
  rw [integral_map (measurable_projFun u v).aemeasurable hcont.aestronglyMeasurable]
  have h2 : ∀ x : Fin n → ℝ,
      Complex.exp (↑(∑ k, x k * (z.ofLp 0 * u.ofLp k + z.ofLp 1 * v.ofLp k)) * Complex.I)
        = ∏ k, Complex.exp (↑(x k * (z.ofLp 0 * u.ofLp k + z.ofLp 1 * v.ofLp k)) * Complex.I) := by
    intro x
    rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  simp only [inner_projFun, h2]
  rw [integral_fintype_prod_eq_prod
    (f := fun (k : Fin n) (t : ℝ) =>
      Complex.exp (↑(t * (z.ofLp 0 * u.ofLp k + z.ofLp 1 * v.ofLp k)) * Complex.I))]
  have h3 : ∀ c : Fin n → ℝ,
      (∏ k, ∫ t : ℝ, Complex.exp (↑(t * c k) * Complex.I) ∂(gaussianReal 0 1))
        = Complex.exp (-↑(∑ k, (c k) ^ 2) / 2) := by
    intro c
    simp_rw [integral_gaussian_exp]
    rw [← Complex.exp_sum]
    congr 1
    simp only [neg_div]
    rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Complex.ofReal_sum]
  rw [h3]
  congr 1
  have hnorm_u : ∑ k : Fin n, (u.ofLp k) ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hu]
    norm_num
  have hnorm_v : ∑ k : Fin n, (v.ofLp k) ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hv]
    norm_num
  have hdot : ∑ k : Fin n, u.ofLp k * v.ofLp k = inner ℝ u v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hquad : z.ofLp ⬝ᵥ (corrMat (inner ℝ u v)).mulVec z.ofLp
      = (z.ofLp 0) ^ 2 + 2 * (inner ℝ u v) * (z.ofLp 0 * z.ofLp 1) + (z.ofLp 1) ^ 2 := by
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, corrMat_apply_zero_zero,
      corrMat_apply_zero_one, corrMat_apply_one_zero, corrMat_apply_one_one]
    ring
  have hexpand : ∑ k : Fin n, (z.ofLp 0 * u.ofLp k + z.ofLp 1 * v.ofLp k) ^ 2
      = (z.ofLp 0) ^ 2 * (∑ k : Fin n, (u.ofLp k) ^ 2)
        + 2 * (z.ofLp 0 * z.ofLp 1) * (∑ k : Fin n, u.ofLp k * v.ofLp k)
        + (z.ofLp 1) ^ 2 * (∑ k : Fin n, (v.ofLp k) ^ 2) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hexpand, hnorm_u, hnorm_v, hdot, hquad]
  push_cast
  ring

/-! ### The joint law of the two columns, over all `r` rows -/

/-- The law of the pair `(Zu, Zv)` of Lemma 2.1: `r` independent rows, each with the
two-dimensional Gaussian law of covariance `!![1, ⟪u,v⟫; ⟪u,v⟫, 1]`. -/
theorem map_rows_eq {r n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Measure.map (fun Z : Fin r → Fin n → ℝ => fun i => projFun u v (Z i))
        (gaussianMatrix r n)
      = Measure.pi fun _ : Fin r => multivariateGaussian 0 (corrMat (inner ℝ u v)) := by
  rw [gaussianMatrix, Measure.pi_map_pi (fun _ => (measurable_projFun u v).aemeasurable)]
  congr 1
  exact funext fun _ => map_projFun_eq u v hu hv

/-! ### The reduced integral -/

/-- The integrand `⟪W₀/‖W₀‖, W₁/‖W₁‖⟫` of the reduced two-column integral. -/
lemma measurable_normalize (r : ℕ) : Measurable (normalize r) := by
  unfold normalize
  fun_prop

lemma measurable_colFun (r : ℕ) (j : Fin 2) : Measurable (colFun r j) := by
  unfold colFun
  fun_prop

lemma measurable_reducedIntegrand (r : ℕ) : Measurable (reducedIntegrand r) := by
  unfold reducedIntegrand
  exact Measurable.inner (measurable_normalize r |>.comp (measurable_colFun r 0))
    (measurable_normalize r |>.comp (measurable_colFun r 1))

lemma mulVecE_colFun_zero {r n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) (Z : Fin r → Fin n → ℝ) :
    mulVecE r n Z u = colFun r 0 (fun i => projFun u v (Z i)) := by
  ext i
  simp only [mulVecE, colFun, projFun, Matrix.mulVec, Matrix.of, dotProduct,
    ofLp_equiv_symm, equiv_apply_eq_ofLp, WithLp.ofLp_toLp, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.isValue, Fin.zero_eta, Fin.mk_one]
  exact Finset.sum_congr rfl fun x _ => rfl

lemma mulVecE_colFun_one {r n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) (Z : Fin r → Fin n → ℝ) :
    mulVecE r n Z v = colFun r 1 (fun i => projFun u v (Z i)) := by
  ext i
  simp only [mulVecE, colFun, projFun, Matrix.mulVec, Matrix.of, dotProduct,
    ofLp_equiv_symm, equiv_apply_eq_ofLp, WithLp.ofLp_toLp, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.isValue, Fin.zero_eta, Fin.mk_one]
  exact Finset.sum_congr rfl fun x _ => rfl

/-- **Reduction of Lemma 2.1**: the Gaussian-rounding expectation of `Zu/‖Zu‖` against
`Zv/‖Zv‖` is the integral of `⟪W₀/‖W₀‖, W₁/‖W₁‖⟫` against the explicit law
`reducedLaw r ⟪u,v⟫`, whose rows are independent two-dimensional Gaussians of covariance
`!![1, ⟪u,v⟫; ⟪u,v⟫, 1]`.  In particular it depends only on `⟪u,v⟫`. -/
theorem grothendieckExpectation_eq_reduced {r n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    grothendieckExpectation r n u v
      = ∫ W, reducedIntegrand r W ∂(reducedLaw r (inner ℝ u v)) := by
  have hkey : ∀ Z : Fin r → Fin n → ℝ,
      inner ℝ (normalize r (mulVecE r n Z u)) (normalize r (mulVecE r n Z v))
        = reducedIntegrand r (fun i => projFun u v (Z i)) := by
    intro Z
    rw [mulVecE_colFun_zero u v Z, mulVecE_colFun_one u v Z]
    rfl
  have hmeas : AEMeasurable (fun Z : Fin r → Fin n → ℝ => fun i => projFun u v (Z i))
      (gaussianMatrix r n) :=
    (measurable_pi_lambda _ fun i =>
      (measurable_projFun u v).comp (measurable_pi_apply i)).aemeasurable
  simp only [grothendieckExpectation, hkey, reducedLaw]
  rw [← map_rows_eq u v hu hv]
  rw [integral_map hmeas ((measurable_reducedIntegrand r).aestronglyMeasurable)]

/-! ### Consequences of the reduction -/

/-- `E_r(0) = 0`. -/
lemma Er_zero (r : ℕ) : Er r 0 = 0 := by
  unfold Er
  simp

/-- **Rotation invariance of the expectation**: `grothendieckExpectation r n u v` depends only
on `⟪u, v⟫` (and not on the dimension `n` or on the individual vectors). -/
theorem grothendieckExpectation_congr_inner {r : ℕ} {n m : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (u' v' : EuclideanSpace ℝ (Fin m)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hu' : ‖u'‖ = 1)
    (hv' : ‖v'‖ = 1) (h : inner ℝ u v = inner ℝ u' v') :
    grothendieckExpectation r n u v = grothendieckExpectation r m u' v' := by
  rw [grothendieckExpectation_eq_reduced u v hu hv,
    grothendieckExpectation_eq_reduced u' v' hu' hv', h]

/-- **Reduction of Lemma 2.1 to a single scalar identity.**  If for every `r` and every
`t ∈ [-1,1]` the integral of `⟪W₀/‖W₀‖, W₁/‖W₁‖` against `r` independent two-dimensional
Gaussians of covariance `!![1, t; t, 1]` equals `E_r(t)`, then Lemma 2.1 holds in full. -/
theorem matrix_grothendieck_identity_of_canonical_proof
    (H : ∀ (r : ℕ) (t : ℝ), |t| ≤ 1 →
      ∫ W, reducedIntegrand r W ∂(reducedLaw r t) = Er r t)
    (r n : ℕ) (hr : 1 ≤ r) (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    grothendieckExpectation r n u v = Er r (inner ℝ u v) := by
  rw [grothendieckExpectation_eq_reduced u v hu hv]
  refine H r (inner ℝ u v) ?_
  have h := norm_inner_le_norm (𝕜 := ℝ) u v
  rw [hu, hv, mul_one] at h
  simpa using h

/-- The reduced integrand in coordinates: the cosine of the angle between the two columns. -/
lemma reducedIntegrand_eq (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    reducedIntegrand r W
      = (∑ i, (W i).ofLp 0 * (W i).ofLp 1) /
        (Real.sqrt (∑ i, ((W i).ofLp 0) ^ 2) * Real.sqrt (∑ i, ((W i).ofLp 1) ^ 2)) := by
  have hinner : inner ℝ (colFun r 0 W) (colFun r 1 W)
      = ∑ i, (W i).ofLp 0 * (W i).ofLp 1 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial, colFun, WithLp.ofLp_toLp]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hn0 : ‖colFun r 0 W‖ = Real.sqrt (∑ i, ((W i).ofLp 0) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.real_norm_sq_eq]
    simp [colFun]
  have hn1 : ‖colFun r 1 W‖ = Real.sqrt (∑ i, ((W i).ofLp 1) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.real_norm_sq_eq]
    simp [colFun]
  unfold reducedIntegrand normalize
  rw [real_inner_smul_left, real_inner_smul_right, hinner, hn0, hn1]
  rw [inv_mul_eq_div, inv_mul_eq_div, div_div, mul_comm]

/-! ### The case `⟪u,v⟫ = 0`: a verified instance of Lemma 2.1

When the two unit vectors are orthogonal, the two Gaussian vectors `Zu` and `Zv` are
independent and identically distributed, so the expectation vanishes, matching `E_r(0) = 0`.
We prove this by the symmetry that flips the second coordinate of every row. -/

/-- The flip of the second coordinate on the coordinate space. -/
lemma measurable_flipCoord : Measurable flipCoord := by
  unfold flipCoord
  apply measurable_pi_iff.mpr
  intro j
  fin_cases j <;> simp <;> fun_prop

lemma measurable_flip2 : Measurable flip2 := by
  unfold flip2
  exact (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp
    (measurable_flipCoord.comp (WithLp.measurable_ofLp 2 (Fin 2 → ℝ)))

lemma flip2_toLp (x : Fin 2 → ℝ) :
    flip2 (WithLp.toLp 2 x) = WithLp.toLp 2 (flipCoord x) := by
  simp [flip2]

lemma inner_flip2 (y z : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (flip2 y) z = inner ℝ y (flip2 z) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, flip2, flipCoord, WithLp.ofLp_toLp, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, Fin.zero_eta, Fin.mk_one]
  ring

lemma norm_flip2 (z : EuclideanSpace ℝ (Fin 2)) : ‖flip2 z‖ = ‖z‖ := by
  have h : ‖flip2 z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp only [flip2, flipCoord, WithLp.ofLp_toLp, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue, Fin.zero_eta, Fin.mk_one]
    ring
  nlinarith [norm_nonneg (flip2 z), norm_nonneg z]

/-- Flipping the second coordinate of `ℝ²` preserves the product of two standard Gaussians. -/
lemma map_flipCoord_pi :
    Measure.map flipCoord (Measure.pi fun _ : Fin 2 => gaussianReal 0 1)
      = Measure.pi fun _ : Fin 2 => gaussianReal 0 1 := by
  have hcoord : flipCoord
      = fun x (i : Fin 2) => (![id, (fun t : ℝ => -t)] : Fin 2 → ℝ → ℝ) i (x i) := by
    funext x i
    fin_cases i <;> rfl
  rw [hcoord, Measure.pi_map_pi]
  · congr 1
    funext i
    fin_cases i
    · simp
    · simpa using gaussianReal_map_neg (μ := 0) (v := 1)
  · intro i
    fin_cases i
    · exact measurable_id.aemeasurable
    · exact measurable_neg.aemeasurable

/-- The standard Gaussian on `ℝ²` is invariant under flipping the second coordinate. -/
lemma map_flip2_stdGaussian :
    Measure.map flip2 (stdGaussian (EuclideanSpace ℝ (Fin 2)))
      = stdGaussian (EuclideanSpace ℝ (Fin 2)) := by
  conv_lhs => rw [← map_pi_eq_stdGaussian (ι := Fin 2)]
  have hfun : flip2 ∘ (WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2))
      = (WithLp.toLp 2) ∘ flipCoord := by
    funext x
    exact flip2_toLp x
  rw [Measure.map_map measurable_flip2 (WithLp.measurable_toLp 2 (Fin 2 → ℝ)), hfun,
    ← Measure.map_map (WithLp.measurable_toLp 2 (Fin 2 → ℝ)) measurable_flipCoord,
    map_flipCoord_pi, map_pi_eq_stdGaussian]

/-- Flipping the second coordinate of every row. -/
lemma measurable_flipRows (r : ℕ) : Measurable (flipRows r) := by
  unfold flipRows
  exact measurable_pi_lambda _ fun i => measurable_flip2.comp (measurable_pi_apply i)

lemma corrMat_zero : corrMat 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [corrMat]

lemma reducedLaw_zero (r : ℕ) :
    reducedLaw r 0 = Measure.pi fun _ : Fin r => stdGaussian (EuclideanSpace ℝ (Fin 2)) := by
  simp [reducedLaw, corrMat_zero]

/-- The law `reducedLaw r 0` is invariant under flipping the second coordinate of every row. -/
lemma map_flipRows_reducedLaw_zero (r : ℕ) :
    Measure.map (flipRows r) (reducedLaw r 0) = reducedLaw r 0 := by
  rw [reducedLaw_zero]
  have hunf : flipRows r = fun (W : Fin r → EuclideanSpace ℝ (Fin 2)) i => flip2 (W i) := rfl
  rw [hunf, Measure.pi_map_pi]
  · congr 1
    funext i
    exact map_flip2_stdGaussian
  · exact fun _ => measurable_flip2.aemeasurable

lemma colFun_flipRows_zero (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    colFun r 0 (flipRows r W) = colFun r 0 W := by
  unfold colFun flipRows flip2 flipCoord
  simp

lemma colFun_flipRows_one (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    colFun r 1 (flipRows r W) = - colFun r 1 W := by
  unfold colFun flipRows flip2 flipCoord
  ext i
  simp

lemma normalize_neg (r : ℕ) (y : EuclideanSpace ℝ (Fin r)) :
    normalize r (-y) = - normalize r y := by
  unfold normalize
  rw [norm_neg, smul_neg]

lemma reducedIntegrand_flipRows (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    reducedIntegrand r (flipRows r W) = - reducedIntegrand r W := by
  unfold reducedIntegrand
  rw [colFun_flipRows_zero, colFun_flipRows_one, normalize_neg, inner_neg_right]

/-- **The orthogonal case of Lemma 2.1**: if `⟪u,v⟫ = 0` the expectation vanishes. -/
theorem grothendieckExpectation_eq_zero_of_inner_eq_zero {r n : ℕ}
    (u v : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : inner ℝ u v = 0) :
    grothendieckExpectation r n u v = 0 := by
  rw [grothendieckExpectation_eq_reduced u v hu hv, h]
  have hstep : ∫ W, reducedIntegrand r W ∂(reducedLaw r 0)
      = - ∫ W, reducedIntegrand r W ∂(reducedLaw r 0) := by
    conv_lhs => rw [← map_flipRows_reducedLaw_zero r]
    rw [integral_map (f := reducedIntegrand r) (measurable_flipRows r).aemeasurable
      (measurable_reducedIntegrand r).aestronglyMeasurable]
    simp only [reducedIntegrand_flipRows]
    exact integral_neg _
  linarith

/-- Lemma 2.1 in the orthogonal case `⟪u,v⟫ = 0`, with the exact binders of the target. -/
theorem matrix_grothendieck_identity_of_orthogonal (r n : ℕ) (_hr : 1 ≤ r)
    (u v : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : inner ℝ u v = 0) :
    grothendieckExpectation r n u v = Er r (inner ℝ u v) := by
  rw [grothendieckExpectation_eq_zero_of_inner_eq_zero u v hu hv h, h, Er_zero]

/-! ### Removing `CFC.sqrt`: the reduced law as an explicit transform of standard Gaussians

`multivariateGaussian 0 !![1,t;t,1]` is defined through `CFC.sqrt`, which is awkward to
compute with.  We identify it with the law of `(y₀, t y₀ + √(1-t²) y₁)` for a standard
Gaussian `y ∈ ℝ²`, i.e. with the Cholesky parametrisation of the correlation. -/

/-- The Cholesky map `y ↦ (y₀, t y₀ + √(1-t²) y₁)`. -/
lemma measurable_cholMap (t : ℝ) : Measurable (cholMap t) := by
  unfold cholMap
  refine (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp ?_
  apply measurable_pi_iff.mpr
  intro j
  fin_cases j <;> simp <;> fun_prop

lemma inner_cholMap (t : ℝ) (y z : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (cholMap t y) z = inner ℝ y (cholAdj t z) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, cholMap, cholAdj, WithLp.ofLp_toLp, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, Fin.zero_eta, Fin.mk_one]
  ring

lemma norm_sq_cholAdj {t : ℝ} (ht : |t| ≤ 1) (z : EuclideanSpace ℝ (Fin 2)) :
    ‖cholAdj t z‖ ^ 2 = z.ofLp ⬝ᵥ (corrMat t).mulVec z.ofLp := by
  have h1 : (0:ℝ) ≤ 1 - t ^ 2 := by
    have := abs_le.mp ht
    nlinarith
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [cholAdj, WithLp.ofLp_toLp, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.isValue, Fin.zero_eta, Fin.mk_one]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, corrMat_apply_zero_zero,
    corrMat_apply_zero_one, corrMat_apply_one_zero, corrMat_apply_one_one]
  rw [mul_pow, Real.sq_sqrt h1]
  ring

/-- **The correlation law in Cholesky form**: the two-dimensional Gaussian with covariance
`!![1,t;t,1]` is the law of `(y₀, t y₀ + √(1-t²) y₁)` for a standard Gaussian `y ∈ ℝ²`. -/
lemma map_cholMap_stdGaussian {t : ℝ} (ht : |t| ≤ 1) :
    Measure.map (cholMap t) (stdGaussian (EuclideanSpace ℝ (Fin 2)))
      = multivariateGaussian 0 (corrMat t) := by
  have hS : (corrMat t).PosSemidef := corrMat_posSemidef ht
  apply Measure.ext_of_charFun
  ext z
  rw [charFun_multivariateGaussian hS]
  simp only [inner_zero_right, Complex.ofReal_zero, mul_zero, zero_mul, sub_zero]
  rw [charFun_apply]
  have hcont : Continuous fun y : EuclideanSpace ℝ (Fin 2) =>
      Complex.exp (↑⟪y, z⟫ * Complex.I) := by fun_prop
  rw [integral_map (measurable_cholMap t).aemeasurable hcont.aestronglyMeasurable]
  simp only [inner_cholMap]
  rw [← charFun_apply, charFun_stdGaussian]
  congr 1
  rw [← Complex.ofReal_pow, norm_sq_cholAdj ht]
  push_cast
  ring

/-- The reduced law, written with `r` independent standard Gaussians on `ℝ²`. -/
theorem grothendieckExpectation_eq_chol {r n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    grothendieckExpectation r n u v
      = ∫ V, reducedIntegrand r (fun i => cholMap (inner ℝ u v) (V i))
          ∂(Measure.pi fun _ : Fin r => stdGaussian (EuclideanSpace ℝ (Fin 2))) := by
  have habs : |inner ℝ u v| ≤ 1 := by
    have h := norm_inner_le_norm (𝕜 := ℝ) u v
    rw [hu, hv, mul_one] at h
    simpa using h
  have hmap : Measure.map (fun V : Fin r → EuclideanSpace ℝ (Fin 2) =>
      fun i => cholMap (inner ℝ u v) (V i))
      (Measure.pi fun _ : Fin r => stdGaussian (EuclideanSpace ℝ (Fin 2)))
      = reducedLaw r (inner ℝ u v) := by
    rw [Measure.pi_map_pi]
    · rw [reducedLaw]
      congr 1
      funext i
      exact map_cholMap_stdGaussian habs
    · exact fun _ => (measurable_cholMap _).aemeasurable
  have hφ : AEMeasurable
      (fun V : Fin r → EuclideanSpace ℝ (Fin 2) => fun i => cholMap (inner ℝ u v) (V i))
      (Measure.pi fun _ : Fin r => stdGaussian (EuclideanSpace ℝ (Fin 2))) :=
    (measurable_pi_lambda _ fun i => (measurable_cholMap _).comp (measurable_pi_apply i)).aemeasurable
  rw [grothendieckExpectation_eq_reduced u v hu hv, ← hmap,
    integral_map (f := reducedIntegrand r) hφ (measurable_reducedIntegrand r).aestronglyMeasurable]

/-- **The explicit form of the reduction.**  With `t = ⟪u,v⟫` and `s = √(1-t²)`, the
expectation is the integral, against `2r` independent standard normal variables
`(a_i, b_i)`, of the cosine between the vectors `a` and `t·a + s·b`. -/
theorem grothendieckExpectation_eq_explicit {r n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    grothendieckExpectation r n u v
      = ∫ V : Fin r → EuclideanSpace ℝ (Fin 2),
          (∑ i, (V i).ofLp 0 * (inner ℝ u v * (V i).ofLp 0
              + Real.sqrt (1 - (inner ℝ u v) ^ 2) * (V i).ofLp 1)) /
          (Real.sqrt (∑ i, ((V i).ofLp 0) ^ 2) *
            Real.sqrt (∑ i, (inner ℝ u v * (V i).ofLp 0
              + Real.sqrt (1 - (inner ℝ u v) ^ 2) * (V i).ofLp 1) ^ 2))
        ∂(Measure.pi fun _ : Fin r => stdGaussian (EuclideanSpace ℝ (Fin 2))) := by
  rw [grothendieckExpectation_eq_chol u v hu hv]
  congr 1 with V
  rw [reducedIntegrand_eq]
  simp [cholMap]

/-- **Product form of the reduction** (ready for Tonelli/Fubini): the reduced law is the
image of a product of `2r` independent standard Gaussians, so the expectation is an
integral over `Z : Fin r → Fin 2 → ℝ` whose entries are independent `N(0,1)` and where
the `i`-th row is `cholMap t` applied to `(Z i 0, Z i 1)`. -/
theorem grothendieckExpectation_eq_prod {r n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    grothendieckExpectation r n u v
      = ∫ Z : Fin r → Fin 2 → ℝ,
          reducedIntegrand r (fun i => cholMap (inner ℝ u v) (WithLp.toLp 2 (Z i)))
          ∂(Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
  have hstd : Measure.pi (fun _ : Fin r => stdGaussian (EuclideanSpace ℝ (Fin 2)))
      = Measure.map (fun Z : Fin r → Fin 2 → ℝ => fun i => WithLp.toLp 2 (Z i))
          (Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
    rw [Measure.pi_map_pi]
    · congr 1
      funext i
      exact (map_pi_eq_stdGaussian (ι := Fin 2)).symm
    · exact fun _ => (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).aemeasurable
  have hφ : AEMeasurable
      (fun Z : Fin r → Fin 2 → ℝ => fun i => WithLp.toLp 2 (Z i))
      (Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin 2 => gaussianReal 0 1) :=
    (measurable_pi_lambda _ fun i =>
      (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp (measurable_pi_apply i)).aemeasurable
  rw [grothendieckExpectation_eq_chol u v hu hv, hstd]
  rw [integral_map hφ]
  · exact (measurable_reducedIntegrand r).comp
      (measurable_pi_lambda _ fun i =>
        (measurable_cholMap _).comp (measurable_pi_apply i)) |>.aestronglyMeasurable

end Grothendieck

open Grothendieck in
theorem solution
    (H : ∀ (r : ℕ) (t : ℝ), |t| ≤ 1 →
      ∫ W, reducedIntegrand r W ∂(reducedLaw r t) = Er r t)
    (r n : ℕ) (hr : 1 ≤ r) (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    grothendieckExpectation r n u v = Er r (inner ℝ u v) :=
  matrix_grothendieck_identity_of_canonical_proof H r n hr u v hu hv
