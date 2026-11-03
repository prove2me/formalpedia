-- Prove2me | solution 1 for Grothendieck.grothendieckExpectation_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T15:00:12.959759+00:00
-- url     : https://prove2.me/submissions/0a7400ef-1005-4896-9241-4f6c4dfba7cf

import Mathlib
import Definitions.Def_Grothendieck_Series
import Definitions.Def_Grothendieck_Gaussian
import Definitions.Def_Grothendieck_Reduced

set_option autoImplicit false

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

namespace Leaf2

/-! ## The sign function -/

/-- `sgn x = x / |x|`, the sign of `x`, with `sgn 0 = 0`. -/
def sgn (x : ℝ) : ℝ := x / |x|

@[simp] lemma sgn_zero : sgn 0 = 0 := by simp [sgn]

lemma sgn_of_pos {x : ℝ} (h : 0 < x) : sgn x = 1 := by
  rw [sgn, abs_of_pos h, div_self h.ne']

lemma sgn_of_neg {x : ℝ} (h : x < 0) : sgn x = -1 := by
  rw [sgn, abs_of_neg h, div_neg, div_self h.ne]

lemma sgn_neg (x : ℝ) : sgn (-x) = -sgn x := by
  simp only [sgn, abs_neg, neg_div]

lemma sgn_mul_pos {c x : ℝ} (hc : 0 < c) : sgn (c * x) = sgn x := by
  rw [sgn, sgn, abs_mul, abs_of_pos hc, mul_div_mul_left x |x| hc.ne']

lemma sq_sgn (x : ℝ) : sgn x * sgn x = if x = 0 then 0 else 1 := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [sgn_of_neg h, if_neg h.ne]
    norm_num
  · rw [h, sgn_zero, if_pos rfl, mul_zero]
  · rw [sgn_of_pos h, if_neg h.ne', mul_one]

lemma abs_sgn_le_one (x : ℝ) : |sgn x| ≤ 1 := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [sgn_of_neg h, abs_neg, abs_one]
  · rw [h, sgn_zero, abs_zero]; norm_num
  · rw [sgn_of_pos h, abs_one]

lemma sgn_mul_sgn (a b : ℝ) : sgn a * sgn b = a * b / (|a| * |b|) := by
  simp only [sgn]
  rw [div_mul_div_comm]

/-! ## The standard normal density and its half-line integrals -/

/-- The standard normal density. -/
def stdPDF (x : ℝ) : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * x ^ 2)

lemma sqrt_two_pi_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) :=
  Real.sqrt_pos.2 (by positivity)

lemma sqrt_two_pi_ne_zero : (Real.sqrt (2 * Real.pi)) ≠ 0 := ne_of_gt sqrt_two_pi_pos

lemma pi_div_half : (π : ℝ) / (1 / 2) = 2 * π := by ring

lemma stdPDF_pos (x : ℝ) : 0 < stdPDF x := by
  have := sqrt_two_pi_pos
  simp only [stdPDF]
  positivity

lemma stdPDF_nonneg (x : ℝ) : 0 ≤ stdPDF x := (stdPDF_pos x).le

lemma stdPDF_le (x : ℝ) : stdPDF x ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
  have h : Real.exp (-(1 / 2) * x ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
  simp only [stdPDF]
  exact mul_le_of_le_one_right (by positivity) h

lemma stdPDF_mul_stdPDF (a b : ℝ) :
    stdPDF a * stdPDF b = (2 * Real.pi)⁻¹ * Real.exp (-(1 / 2) * (a ^ 2 + b ^ 2)) := by
  have h : (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ = (2 * Real.pi)⁻¹ := by
    rw [← mul_inv, ← sq, Real.sq_sqrt (by positivity)]
  have key : (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * a ^ 2)
        * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * b ^ 2))
      = ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹)
        * (Real.exp (-(1 / 2) * a ^ 2) * Real.exp (-(1 / 2) * b ^ 2)) := by ring
  simp only [stdPDF]
  rw [key, h, ← Real.exp_add,
    show -(1 / 2) * a ^ 2 + -(1 / 2) * b ^ 2 = -(1 / 2) * (a ^ 2 + b ^ 2) by ring]

lemma integral_exp_neg_half_sq : ∫ x : ℝ, Real.exp (-(1 / 2) * x ^ 2) = Real.sqrt (2 * Real.pi) := by
  have h := integral_gaussian (1 / 2 : ℝ)
  rwa [pi_div_half] at h

lemma integral_Ioi_exp_neg_half_sq :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(1 / 2) * x ^ 2) = Real.sqrt (2 * Real.pi) / 2 := by
  have h := integral_gaussian_Ioi (1 / 2 : ℝ)
  rwa [pi_div_half] at h

lemma integral_stdPDF : ∫ x : ℝ, stdPDF x = 1 := by
  simp only [stdPDF]
  rw [integral_const_mul, integral_exp_neg_half_sq]
  exact inv_mul_cancel₀ sqrt_two_pi_ne_zero

lemma integral_Ioi_stdPDF : ∫ x in Set.Ioi (0 : ℝ), stdPDF x = 1 / 2 := by
  simp only [stdPDF]
  rw [integral_const_mul, integral_Ioi_exp_neg_half_sq]
  field_simp

lemma integrable_stdPDF : Integrable stdPDF := by
  have h : Integrable fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2) :=
    integrable_exp_neg_mul_sq (by norm_num)
  exact h.const_mul _

lemma integrable_mul_stdPDF : Integrable fun x : ℝ => x * stdPDF x := by
  have h : Integrable fun x : ℝ => x * Real.exp (-(1 / 2) * x ^ 2) :=
    integrable_mul_exp_neg_mul_sq (by norm_num)
  have := h.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [stdPDF]
  ring

lemma integral_Iic_stdPDF (u : ℝ) :
    ∫ x in Set.Iic u, stdPDF x = 1 / 2 + ∫ x in (0 : ℝ)..u, stdPDF x := by
  have h := intervalIntegral.integral_Iic_sub_Iic (f := stdPDF) (a := (0 : ℝ)) (b := u)
    (μ := volume) integrable_stdPDF.integrableOn integrable_stdPDF.integrableOn
  have h0 : ∫ x in Set.Iic (0 : ℝ), stdPDF x = 1 / 2 := by
    have h1 := intervalIntegral.integral_Iic_add_Ioi (f := stdPDF) (b := (0 : ℝ))
      (μ := volume) integrable_stdPDF.integrableOn integrable_stdPDF.integrableOn
    have h2 : 0 ≤ ∫ x in Set.Ioi (0 : ℝ), stdPDF x :=
      integral_nonneg stdPDF_nonneg
    rw [integral_stdPDF, integral_Ioi_stdPDF] at h1
    linarith
  rw [← h0]
  linarith

lemma integral_Iic_stdPDF_nonneg (u : ℝ) : 0 ≤ ∫ x in Set.Iic u, stdPDF x :=
  integral_nonneg stdPDF_nonneg

lemma integral_Iic_stdPDF_le_one (u : ℝ) : ∫ x in Set.Iic u, stdPDF x ≤ 1 := by
  have h1 := intervalIntegral.integral_Iic_add_Ioi (f := stdPDF) (b := u)
    (μ := volume) integrable_stdPDF.integrableOn integrable_stdPDF.integrableOn
  have h2 : 0 ≤ ∫ x in Set.Ioi u, stdPDF x := integral_nonneg stdPDF_nonneg
  rw [integral_stdPDF] at h1
  linarith

/-- `∫_0^∞ x e^{-b x²} = 1/(2b)`. -/
lemma integral_Ioi_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-b * x ^ 2) = (2 * b)⁻¹ := by
  have hbre : 0 < ((b : ℂ)).re := by simpa using hb
  have h := integral_mul_cexp_neg_mul_sq (b := (b : ℂ)) hbre
  have h2 : ∀ x : ℝ, ((x * Real.exp (-b * x ^ 2) : ℝ) : ℂ)
      = (x : ℂ) * Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) := by
    intro x
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    rw [neg_mul]
  refine Complex.ofReal_inj.1 ?_
  rw [show ((∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-b * x ^ 2) : ℝ) : ℂ)
        = ∫ x in Set.Ioi (0 : ℝ), ((x * Real.exp (-b * x ^ 2) : ℝ) : ℂ) from
      integral_ofReal.symm]
  simp only [h2]
  rw [h]
  push_cast
  ring

/-! ## The primitive `Ψ` of twice the normal density -/

/-- `Ψ c = 2 ∫_0^c (2π)^{-1/2} e^{-x²/2} dx`. -/
def stdPsi (c : ℝ) : ℝ := 2 * ∫ x in (0 : ℝ)..c, stdPDF x

lemma stdPsi_zero : stdPsi 0 = 0 := by simp [stdPsi]

lemma stdPDF_neg (x : ℝ) : stdPDF (-x) = stdPDF x := by
  simp only [stdPDF]
  rw [neg_sq]

lemma continuous_stdPDF : Continuous stdPDF := by
  unfold stdPDF
  fun_prop

lemma hasDerivAt_stdPsi (c : ℝ) : HasDerivAt stdPsi (2 * stdPDF c) c := by
  have h := intervalIntegral.integral_hasDerivAt_right
    (f := stdPDF) (a := (0 : ℝ)) (b := c)
    (continuous_stdPDF.intervalIntegrable 0 c)
    (continuous_stdPDF.stronglyMeasurableAtFilter volume (nhds c))
    (continuous_stdPDF.continuousAt)
  show HasDerivAt (fun u : ℝ => 2 * ∫ x in (0 : ℝ)..u, stdPDF x) (2 * stdPDF c) c
  exact h.const_mul 2

lemma continuous_stdPsi : Continuous stdPsi := by
  rw [continuous_iff_continuousAt]
  intro c
  exact (hasDerivAt_stdPsi c).continuousAt

lemma stdPsi_neg (c : ℝ) : stdPsi (-c) = -stdPsi c := by
  have h : ∫ x in (-c)..(0:ℝ), stdPDF x = ∫ x in (0:ℝ)..c, stdPDF x := by
    have h2 := intervalIntegral.integral_comp_neg (f := stdPDF) (a := (0:ℝ)) (b := c)
    simpa [stdPDF_neg] using h2.symm
  unfold stdPsi
  rw [intervalIntegral.integral_symm, h]
  ring

lemma abs_stdPsi_le_one (c : ℝ) : |stdPsi c| ≤ 1 := by
  have h1 := integral_Iic_stdPDF c
  have h2 := integral_Iic_stdPDF_nonneg c
  have h3 := integral_Iic_stdPDF_le_one c
  rw [stdPsi, abs_le]
  constructor <;> linarith

attribute [fun_prop] continuous_stdPDF continuous_stdPsi

/-! ## The key integral `∫_0^∞ Ψ(cx) φ(x) dx` -/

/-- `stdB c = ∫_0^∞ Ψ(c x) (2π)^{-1/2} e^{-x²/2} dx`. -/
def stdB (c : ℝ) : ℝ := ∫ x in Set.Ioi (0 : ℝ), stdPsi (c * x) * stdPDF x

lemma aemeasurable_stdF (c : ℝ) :
    AEStronglyMeasurable (fun x : ℝ => stdPsi (c * x) * stdPDF x)
      (volume.restrict (Set.Ioi 0)) := by
  fun_prop

lemma integrable_stdF (c : ℝ) :
    Integrable (fun x : ℝ => stdPsi (c * x) * stdPDF x) (volume.restrict (Set.Ioi 0)) := by
  refine Integrable.mono' integrable_stdPDF.integrableOn (aemeasurable_stdF c) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stdPDF_nonneg x)]
  exact mul_le_of_le_one_left (stdPDF_nonneg x) (abs_stdPsi_le_one _)

lemma integrable_stdB_bound :
    Integrable (fun x : ℝ => 2 * (Real.sqrt (2 * Real.pi))⁻¹ * |x| * stdPDF x)
      (volume.restrict (Set.Ioi 0)) := by
  have h : Integrable (fun x : ℝ => 2 * (Real.sqrt (2 * Real.pi))⁻¹ * (x * stdPDF x)) volume :=
    integrable_mul_stdPDF.const_mul _
  refine h.integrableOn.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [abs_of_pos hx]
  ring

lemma hasDerivAt_stdB (c : ℝ) :
    HasDerivAt stdB (∫ x in Set.Ioi (0 : ℝ), (2 * stdPDF (c * x)) * x * stdPDF x) c := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun x : ℝ => 2 * (Real.sqrt (2 * Real.pi))⁻¹ * |x| * stdPDF x)
    (F := fun d x => stdPsi (d * x) * stdPDF x)
    (F' := fun d x => (2 * stdPDF (d * x)) * x * stdPDF x)
    (x₀ := c) (s := Set.univ) (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    Filter.univ_mem
    (Filter.Eventually.of_forall fun d => by fun_prop)
    (integrable_stdF c)
    (by fun_prop)
    ?_ integrable_stdB_bound ?_
  · exact key.2
  · refine Filter.Eventually.of_forall fun a => ?_
    intro d _
    have hP : 0 ≤ stdPDF (d * a) := stdPDF_nonneg _
    have hQ : 0 ≤ stdPDF a := stdPDF_nonneg a
    have hle : stdPDF (d * a) ≤ (Real.sqrt (2 * Real.pi))⁻¹ := stdPDF_le _
    rw [Real.norm_eq_abs,
      show |(2 * stdPDF (d * a)) * a * stdPDF a| = 2 * stdPDF (d * a) * |a| * stdPDF a by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg hQ]]
    have h1 : 2 * stdPDF (d * a) * |a| * stdPDF a
        ≤ 2 * (Real.sqrt (2 * Real.pi))⁻¹ * |a| * stdPDF a := by
      have h2 : 2 * stdPDF (d * a) * |a| ≤ 2 * (Real.sqrt (2 * Real.pi))⁻¹ * |a| := by
        have := mul_le_mul_of_nonneg_right hle (abs_nonneg a)
        linarith
      exact mul_le_mul_of_nonneg_right h2 hQ
    linarith [h1]
  · refine Filter.Eventually.of_forall fun a => ?_
    intro d _
    have h1 : HasDerivAt (fun d : ℝ => d * a) a d := by
      simpa using (hasDerivAt_id d).mul_const a
    have h2 := (hasDerivAt_stdPsi (d * a)).comp d h1
    have h3 : HasDerivAt (fun d : ℝ => stdPsi (d * a) * stdPDF a)
        ((2 * stdPDF (d * a)) * a * stdPDF a) d := by
      simpa using h2.mul_const (stdPDF a)
    exact h3

lemma integral_deriv_stdB (c : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ), (2 * stdPDF (c * x)) * x * stdPDF x
      = (1 / Real.pi) * (1 + c ^ 2)⁻¹ := by
  have hb : (0 : ℝ) < (1 + c ^ 2) / 2 := by positivity
  have hpt : ∀ x : ℝ, (2 * stdPDF (c * x)) * x * stdPDF x
      = (1 / Real.pi) * (x * Real.exp (-((1 + c ^ 2) / 2) * x ^ 2)) := by
    intro x
    have h := stdPDF_mul_stdPDF (c * x) x
    have hexp : -(1 / 2) * ((c * x) ^ 2 + x ^ 2) = -((1 + c ^ 2) / 2) * x ^ 2 := by ring
    rw [show (2 * stdPDF (c * x)) * x * stdPDF x = 2 * x * (stdPDF (c * x) * stdPDF x) by ring,
      h, hexp]
    have hc : 2 * (2 * Real.pi)⁻¹ = (Real.pi)⁻¹ := by
      rw [show (2 * Real.pi)⁻¹ = (2 : ℝ)⁻¹ * Real.pi⁻¹ by rw [mul_inv]]
      ring
    calc 2 * x * ((2 * Real.pi)⁻¹ * Real.exp (-((1 + c ^ 2) / 2) * x ^ 2))
        = (2 * (2 * Real.pi)⁻¹) * (x * Real.exp (-((1 + c ^ 2) / 2) * x ^ 2)) := by ring
      _ = Real.pi⁻¹ * (x * Real.exp (-((1 + c ^ 2) / 2) * x ^ 2)) := by rw [hc]
      _ = (1 / Real.pi) * (x * Real.exp (-((1 + c ^ 2) / 2) * x ^ 2)) := by rw [one_div]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_Ioi_mul_exp_neg_mul_sq hb]
  rw [show (2 * ((1 + c ^ 2) / 2))⁻¹ = ((1 + c ^ 2))⁻¹ from by congr 1; ring]

lemma hasDerivAt_stdB' (c : ℝ) : HasDerivAt stdB ((1 / Real.pi) * (1 + c ^ 2)⁻¹) c := by
  rw [← integral_deriv_stdB c]
  exact hasDerivAt_stdB c

lemma stdB_zero : stdB 0 = 0 := by
  simp [stdB, stdPsi_zero]

lemma continuous_inv_one_add_sq : Continuous fun u : ℝ => (1 + u ^ 2)⁻¹ := by
  apply Continuous.inv₀
  · fun_prop
  · intro u
    positivity

lemma integral_zero_to_inv_one_add_sq (c : ℝ) :
    ∫ u in (0 : ℝ)..c, (1 + u ^ 2)⁻¹ = Real.arctan c := by
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := c)
    (f := Real.arctan) (f' := fun u : ℝ => (1 + u ^ 2)⁻¹)
    (fun u _ => by simpa [one_div] using Real.hasDerivAt_arctan u)
    (continuous_inv_one_add_sq.intervalIntegrable _ _)
  rw [key, Real.arctan_zero, sub_zero]

lemma stdB_eq_arctan (c : ℝ) : stdB c = Real.arctan c / Real.pi := by
  have hint : IntervalIntegrable (fun u : ℝ => (1 / Real.pi) * (1 + u ^ 2)⁻¹) volume 0 c :=
    (continuous_const.mul continuous_inv_one_add_sq).intervalIntegrable _ _
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := c)
    (f := stdB) (f' := fun u : ℝ => (1 / Real.pi) * (1 + u ^ 2)⁻¹)
    (fun u _ => hasDerivAt_stdB' u) hint
  rw [stdB_zero, sub_zero] at key
  rw [← key, intervalIntegral.integral_const_mul, integral_zero_to_inv_one_add_sq]
  ring

/-! ## The Gaussian density of Mathlib and the sign integral -/

lemma measurable_sgn : Measurable sgn := by
  unfold sgn
  exact measurable_id.div measurable_abs

lemma gaussianPDFReal_zero_one (y : ℝ) : gaussianPDFReal 0 1 y = stdPDF y := by
  simp only [gaussianPDFReal, stdPDF, NNReal.coe_one, mul_one, sub_zero]
  rw [show -(y ^ 2) / 2 = -(1 / 2) * y ^ 2 from by ring]

lemma setIntegral_gaussianReal_eq_stdPDF {s : Set ℝ} (hs : MeasurableSet s) (f : ℝ → ℝ) :
    ∫ x in s, f x ∂(gaussianReal 0 1) = ∫ x in s, f x * stdPDF x := by
  rw [← integral_indicator hs]
  rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) one_ne_zero]
  have hpt : ∀ x : ℝ, gaussianPDFReal 0 1 x • (Set.indicator s f x)
      = Set.indicator s (fun x => f x * stdPDF x) x := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, smul_eq_mul,
        gaussianPDFReal_zero_one]
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, smul_zero]
  simp only [hpt]
  rw [integral_indicator hs]

/-- **The key one-dimensional identity**: `∫ sgn(y + c) dN(0,1) = Ψ c`. -/
lemma integral_sgn_add (c : ℝ) :
    ∫ y, sgn (y + c) ∂(gaussianReal 0 1) = stdPsi c := by
  have hdens : ∀ y : ℝ, gaussianPDFReal 0 1 y * sgn (y + c) = sgn (y + c) * stdPDF y := by
    intro y; rw [gaussianPDFReal_zero_one]; ring
  rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) one_ne_zero]
  simp only [smul_eq_mul, hdens]
  have hg : ∀ y : ℝ, sgn (y + c) * stdPDF y
      = Set.indicator (Set.Ioi (-c)) stdPDF y - Set.indicator (Set.Iio (-c)) stdPDF y := by
    intro y
    by_cases hy : y = -c
    · subst hy
      have h1 : -c ∉ Set.Ioi (-c) := by simp
      have h2 : -c ∉ Set.Iio (-c) := by simp
      rw [show -c + c = 0 by ring, sgn_zero, Set.indicator_of_notMem h1,
        Set.indicator_of_notMem h2]
      ring
    · rcases lt_or_gt_of_ne hy with h | h
      · have hyc : y + c < 0 := by linarith
        have h1 : y ∉ Set.Ioi (-c) := by simp [not_lt.mpr h.le]
        have h2 : y ∈ Set.Iio (-c) := by simp [h]
        rw [sgn_of_neg hyc, Set.indicator_of_notMem h1, Set.indicator_of_mem h2]
        ring
      · have hyc : 0 < y + c := by linarith
        have h1 : y ∈ Set.Ioi (-c) := by simp [h]
        have h2 : y ∉ Set.Iio (-c) := by simp [not_lt.mpr h.le]
        rw [sgn_of_pos hyc, Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
        ring
  simp_rw [hg]
  rw [integral_sub (integrable_stdPDF.indicator measurableSet_Ioi)
    (integrable_stdPDF.indicator measurableSet_Iio)]
  rw [integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Iio]
  have hIic : ∫ y in Set.Iic (-c), stdPDF y = 1 / 2 + ∫ y in (0 : ℝ)..(-c), stdPDF y :=
    integral_Iic_stdPDF (-c)
  have hIio : ∫ y in Set.Iio (-c), stdPDF y = 1 / 2 + ∫ y in (0 : ℝ)..(-c), stdPDF y := by
    rw [← integral_Iic_eq_integral_Iio' (measure_singleton (-c))]
    exact integral_Iic_stdPDF (-c)
  have hIoi : ∫ y in Set.Ioi (-c), stdPDF y = 1 / 2 - ∫ y in (0 : ℝ)..(-c), stdPDF y := by
    have h := intervalIntegral.integral_Iic_add_Ioi (f := stdPDF) (b := -c)
      (μ := volume) integrable_stdPDF.integrableOn integrable_stdPDF.integrableOn
    rw [integral_stdPDF, hIic] at h
    linarith
  have hK : stdPsi c = -2 * ∫ y in (0 : ℝ)..(-c), stdPDF y := by
    have h := stdPsi_neg c
    simp only [stdPsi] at h ⊢
    linarith
  rw [hIoi, hIio, hK]
  ring

/-- A function invariant under `x ↦ -x` has equal integrals over the two half-lines. -/
lemma integral_Iio_zero_eq_Ioi {F : ℝ → ℝ} (hFm : Measurable F)
    (hF : ∀ x, F (-x) = F x) :
    ∫ x in Set.Iio (0 : ℝ), F x ∂(gaussianReal 0 1)
      = ∫ x in Set.Ioi (0 : ℝ), F x ∂(gaussianReal 0 1) := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := 0) (v := 1)
  rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi]
  conv_lhs => rw [← hmap]
  rw [integral_map measurable_neg.aemeasurable ((hFm.indicator measurableSet_Iio).aestronglyMeasurable)]
  congr 1 with x
  by_cases hx : 0 < x
  · have h1 : -x ∈ Set.Iio (0 : ℝ) := by simp [hx]
    have h2 : x ∈ Set.Ioi (0 : ℝ) := hx
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, hF]
  · have h1 : -x ∉ Set.Iio (0 : ℝ) := by simp [show ¬ (0 < x) from hx]
    have h2 : x ∉ Set.Ioi (0 : ℝ) := by simp [hx]
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

lemma measurable_sgnPsi (c : ℝ) : Measurable fun x : ℝ => sgn x * stdPsi (c * x) := by
  exact measurable_sgn.mul (continuous_stdPsi.measurable.comp (measurable_const.mul measurable_id))

lemma abs_sgnPsi_le_one (c x : ℝ) : |sgn x * stdPsi (c * x)| ≤ 1 := by
  rw [abs_mul]
  have h1 := abs_sgn_le_one x
  have h2 := abs_stdPsi_le_one (c * x)
  have h3 : 0 ≤ |sgn x| := abs_nonneg _
  nlinarith

lemma integral_Ioi_sgnPsi (c : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ), sgn x * stdPsi (c * x) ∂(gaussianReal 0 1) = stdB c := by
  rw [setIntegral_gaussianReal_eq_stdPDF measurableSet_Ioi]
  rw [show ∫ x in Set.Ioi (0 : ℝ), (sgn x * stdPsi (c * x)) * stdPDF x
        = ∫ x in Set.Ioi (0 : ℝ), stdPsi (c * x) * stdPDF x from ?_]
  · rfl
  · refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [sgn_of_pos hx]
    ring

/-- **The two-dimensional sign integral.** -/
lemma integral_prod_sgn {t s : ℝ} (hs : 0 < s) :
    ∫ p : ℝ × ℝ, sgn p.1 * sgn (t * p.1 + s * p.2)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))
      = (2 / Real.pi) * Real.arctan (t / s) := by
  haveI hns : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hmeas : Measurable fun p : ℝ × ℝ => sgn p.1 * sgn (t * p.1 + s * p.2) := by
    apply Measurable.mul
    · exact measurable_sgn.comp measurable_fst
    · exact measurable_sgn.comp ((measurable_const.mul measurable_fst).add
        (measurable_const.mul measurable_snd))
  have hInt : Integrable (fun p : ℝ × ℝ => sgn p.1 * sgn (t * p.1 + s * p.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := abs_sgn_le_one p.1
    have h2 := abs_sgn_le_one (t * p.1 + s * p.2)
    have h3 : (0:ℝ) ≤ |sgn p.1| := abs_nonneg _
    nlinarith
  rw [integral_prod _ hInt]
  have hinner : ∀ x : ℝ,
      ∫ y, sgn x * sgn (t * x + s * y) ∂(gaussianReal 0 1) = sgn x * stdPsi ((t / s) * x) := by
    intro x
    rw [integral_const_mul]
    congr 1
    have hpt : ∀ y : ℝ, sgn (t * x + s * y) = sgn (y + (t / s) * x) := by
      intro y
      have h : t * x + s * y = s * (y + (t / s) * x) := by
        field_simp
        ring
      rw [h, sgn_mul_pos hs]
    simp only [hpt]
    exact integral_sgn_add ((t / s) * x)
  simp only [hinner]
  have hInt2 : IntegrableOn (fun x : ℝ => sgn x * stdPsi ((t / s) * x)) (Set.Ioi (0:ℝ))
      (gaussianReal 0 1) := by
    refine Integrable.of_bound ((measurable_sgnPsi (t / s)).aestronglyMeasurable) 1 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact abs_sgnPsi_le_one (t / s) x
  have hInt3 : IntegrableOn (fun x : ℝ => sgn x * stdPsi ((t / s) * x)) (Set.Iic (0:ℝ))
      (gaussianReal 0 1) := by
    refine Integrable.of_bound ((measurable_sgnPsi (t / s)).aestronglyMeasurable) 1 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact abs_sgnPsi_le_one (t / s) x
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (f := fun x : ℝ => sgn x * stdPsi ((t / s) * x)) (b := (0:ℝ))
    (μ := gaussianReal 0 1) hInt3 hInt2
  have hIic : ∫ x in Set.Iic (0:ℝ), sgn x * stdPsi ((t / s) * x) ∂(gaussianReal 0 1)
      = ∫ x in Set.Iio (0:ℝ), sgn x * stdPsi ((t / s) * x) ∂(gaussianReal 0 1) :=
    integral_Iic_eq_integral_Iio' (measure_singleton 0)
  have hIio := integral_Iio_zero_eq_Ioi (measurable_sgnPsi (t / s))
    (fun x => by
      have h1 : (t / s) * -x = -((t / s) * x) := by ring
      simp only [h1, sgn_neg, stdPsi_neg]
      ring)
  rw [← hsplit, hIic, hIio]
  rw [integral_Ioi_sgnPsi (t / s), stdB_eq_arctan]
  ring

/-! ## Reduction of the `r = 1` expectation to the bivariate integral -/

lemma reducedIntegrand_one_chol {t : ℝ} (z : Fin 2 → ℝ) :
    reducedIntegrand 1 (fun _ : Fin 1 => cholMap t (WithLp.toLp 2 z))
      = sgn (z 0) * sgn (t * z 0 + Real.sqrt (1 - t ^ 2) * z 1) := by
  rw [reducedIntegrand_eq]
  simp only [Fin.sum_univ_one, cholMap, WithLp.ofLp_toLp, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.isValue, Fin.zero_eta, Fin.mk_one]
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, ← sgn_mul_sgn]

theorem grothendieckExpectation_one_eq_prod {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    grothendieckExpectation 1 n u v
      = ∫ p : ℝ × ℝ,
          sgn p.1 * sgn (inner ℝ u v * p.1 + Real.sqrt (1 - (inner ℝ u v) ^ 2) * p.2)
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  rw [grothendieckExpectation_eq_prod u v hu hv]
  have hA : (∫ Z : Fin 1 → Fin 2 → ℝ,
        reducedIntegrand 1 (fun i => cholMap (inner ℝ u v) (WithLp.toLp 2 (Z i)))
        ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin 2 => gaussianReal 0 1))
      = ∫ z : Fin 2 → ℝ,
          reducedIntegrand 1 (fun _ : Fin 1 => cholMap (inner ℝ u v) (WithLp.toLp 2 z))
          ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
    have h := (measurePreserving_funUnique (Measure.pi fun _ : Fin 2 => gaussianReal 0 1)
      (Fin 1)).integral_comp' (fun z : Fin 2 → ℝ =>
        reducedIntegrand 1 (fun _ : Fin 1 => cholMap (inner ℝ u v) (WithLp.toLp 2 z)))
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
    show reducedIntegrand 1 (fun i => cholMap (inner ℝ u v) (WithLp.toLp 2 (Z i)))
        = reducedIntegrand 1 (fun _ : Fin 1 => cholMap (inner ℝ u v)
            (WithLp.toLp 2 (MeasurableEquiv.funUnique (Fin 1) (Fin 2 → ℝ) Z)))
    have hZ : MeasurableEquiv.funUnique (Fin 1) (Fin 2 → ℝ) Z = Z default := rfl
    rw [hZ]
    congr 1
    funext i
    rw [Subsingleton.elim i default]
  rw [hA]
  have hB : (∫ z : Fin 2 → ℝ,
        reducedIntegrand 1 (fun _ : Fin 1 => cholMap (inner ℝ u v) (WithLp.toLp 2 z))
        ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1))
      = ∫ p : ℝ × ℝ,
          reducedIntegrand 1 (fun _ : Fin 1 =>
            cholMap (inner ℝ u v) (WithLp.toLp 2 (MeasurableEquiv.finTwoArrow.symm p)))
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    have h := (measurePreserving_finTwoArrow (gaussianReal 0 1)).integral_comp'
      (fun p : ℝ × ℝ => reducedIntegrand 1 (fun _ : Fin 1 =>
        cholMap (inner ℝ u v) (WithLp.toLp 2 (MeasurableEquiv.finTwoArrow.symm p))))
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show reducedIntegrand 1 (fun _ : Fin 1 => cholMap (inner ℝ u v) (WithLp.toLp 2 z))
        = reducedIntegrand 1 (fun _ : Fin 1 => cholMap (inner ℝ u v) (WithLp.toLp 2
            (MeasurableEquiv.finTwoArrow.symm (MeasurableEquiv.finTwoArrow z))))
    rw [MeasurableEquiv.symm_apply_apply]
  rw [hB]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show reducedIntegrand 1 (fun _ : Fin 1 =>
        cholMap (inner ℝ u v) (WithLp.toLp 2 (MeasurableEquiv.finTwoArrow.symm p)))
      = sgn p.1 * sgn (inner ℝ u v * p.1 + Real.sqrt (1 - (inner ℝ u v) ^ 2) * p.2)
  rw [reducedIntegrand_one_chol]
  have h0 : (MeasurableEquiv.finTwoArrow.symm p) 0 = p.1 := by simp
  have h1 : (MeasurableEquiv.finTwoArrow.symm p) 1 = p.2 := by simp
  rw [h0, h1]

/-! ## The `r = 1` case of Lemma 2.1 -/

lemma integral_sgn_sq_prod :
    ∫ p : ℝ × ℝ, sgn p.1 * sgn p.1 ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = 1 := by
  haveI hns : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hzero : ((gaussianReal 0 1).prod (gaussianReal 0 1)) {p : ℝ × ℝ | p.1 = 0} = 0 := by
    have hset : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
      ext p
      simp [eq_comm]
    rw [hset, Measure.prod_prod, measure_singleton, zero_mul]
  have hae0 : ∀ᵐ p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)), p.1 ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using hzero
  have hae : ∀ᵐ p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)), sgn p.1 * sgn p.1 = 1 := by
    filter_upwards [hae0] with p hp
    rw [sq_sgn, if_neg hp]
  rw [integral_congr_ae hae, integral_const]
  have hreal : ((gaussianReal 0 1).prod (gaussianReal 0 1)).real Set.univ = 1 := by
    simp [Measure.real]
  rw [hreal, one_smul]

/-- **The `r = 1` case of Lemma 2.1**: the arcsine law. -/
theorem grothendieckExpectation_one_proof {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    grothendieckExpectation 1 n u v = 2 / Real.pi * Real.arcsin (inner ℝ u v) := by
  haveI hns : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [grothendieckExpectation_one_eq_prod u v hu hv]
  set t := inner ℝ u v with ht
  have htabs : |t| ≤ 1 := by
    have h := norm_inner_le_norm (𝕜 := ℝ) u v
    rw [hu, hv, mul_one] at h
    rw [ht]
    exact h
  have htle : t ≤ 1 := (abs_le.1 htabs).2
  have htge : -1 ≤ t := (abs_le.1 htabs).1
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · rcases lt_trichotomy t (-1) with h2 | h2 | h2
    · linarith
    · -- t = -1
      rw [h2]
      have hae : ∀ᵐ p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)),
          sgn p.1 * sgn (-1 * p.1 + Real.sqrt (1 - (-1 : ℝ) ^ 2) * p.2)
            = -(sgn p.1 * sgn p.1) := by
        filter_upwards with p
        have hsp : (-1 : ℝ) * p.1 + Real.sqrt (1 - (-1 : ℝ) ^ 2) * p.2 = -p.1 := by
          norm_num
        rw [hsp, sgn_neg]
        ring
      rw [integral_congr_ae hae, integral_neg, integral_sgn_sq_prod, Real.arcsin_neg_one]
      field_simp
    · -- -1 < t < 1
      have hsq : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
      have hs : (0 : ℝ) < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.2 hsq
      rw [integral_prod_sgn (t := t) (s := Real.sqrt (1 - t ^ 2)) hs]
      rw [Real.arcsin_eq_arctan (show t ∈ Set.Ioo (-(1 : ℝ)) 1 from ⟨h2, hlt⟩)]
  · -- t = 1
    rw [heq]
    have hae : ∀ᵐ p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)),
        sgn p.1 * sgn (1 * p.1 + Real.sqrt (1 - (1 : ℝ) ^ 2) * p.2) = sgn p.1 * sgn p.1 := by
      filter_upwards with p
      have hsp : (1 : ℝ) * p.1 + Real.sqrt (1 - (1 : ℝ) ^ 2) * p.2 = p.1 := by
        norm_num
      rw [hsp]
    rw [integral_congr_ae hae, integral_sgn_sq_prod, Real.arcsin_one]
    field_simp
  · linarith

end Leaf2
end Grothendieck

open Grothendieck in
theorem solution {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    grothendieckExpectation 1 n u v = 2 / Real.pi * Real.arcsin (inner ℝ u v) :=
  Grothendieck.Leaf2.grothendieckExpectation_one_proof u v hu hv
