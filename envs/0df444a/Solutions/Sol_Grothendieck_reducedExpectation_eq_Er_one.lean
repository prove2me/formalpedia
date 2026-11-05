-- Prove2me | solution 1 for Grothendieck.reducedExpectation_eq_Er_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T07:16:12.380215+00:00
-- url     : https://prove2.me/submissions/a96dda8c-eeae-435d-9a0e-9c2f2d501852

import Mathlib
import Definitions.Def_Grothendieck_Series
import Definitions.Def_Grothendieck_Gaussian
import Definitions.Def_Grothendieck_Reduced

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Real RealInnerProductSpace

namespace Grothendieck

lemma equiv_apply_eq_ofLp {m : Type*} [Fintype m] (x : EuclideanSpace ℝ m) (i : m) :
    (EuclideanSpace.equiv m ℝ) x i = x.ofLp i := by
  rw [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_apply]

lemma ofLp_equiv_symm {m : Type*} [Fintype m] (y : m → ℝ) (i : m) :
    ((EuclideanSpace.equiv m ℝ).symm y).ofLp i = y i := by
  simp [EuclideanSpace.equiv]

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

lemma integral_gaussian_exp (c : ℝ) :
    ∫ t : ℝ, Complex.exp (↑(t * c) * Complex.I) ∂(gaussianReal 0 1)
      = Complex.exp (-↑(c ^ 2) / 2) := by
  simp only [← Real.inner_apply]
  rw [← charFun_apply, charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one, one_mul]
  congr 1
  rw [Complex.ofReal_pow]
  ring

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

theorem map_rows_eq {r n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Measure.map (fun Z : Fin r → Fin n → ℝ => fun i => projFun u v (Z i))
        (gaussianMatrix r n)
      = Measure.pi fun _ : Fin r => multivariateGaussian 0 (corrMat (inner ℝ u v)) := by
  rw [gaussianMatrix, Measure.pi_map_pi (fun _ => (measurable_projFun u v).aemeasurable)]
  congr 1
  exact funext fun _ => map_projFun_eq u v hu hv

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

lemma Er_zero (r : ℕ) : Er r 0 = 0 := by
  unfold Er
  simp

theorem grothendieckExpectation_congr_inner {r : ℕ} {n m : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (u' v' : EuclideanSpace ℝ (Fin m)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hu' : ‖u'‖ = 1)
    (hv' : ‖v'‖ = 1) (h : inner ℝ u v = inner ℝ u' v') :
    grothendieckExpectation r n u v = grothendieckExpectation r m u' v' := by
  rw [grothendieckExpectation_eq_reduced u v hu hv,
    grothendieckExpectation_eq_reduced u' v' hu' hv', h]

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

lemma measurable_flipRows (r : ℕ) : Measurable (flipRows r) := by
  unfold flipRows
  exact measurable_pi_lambda _ fun i => measurable_flip2.comp (measurable_pi_apply i)

lemma corrMat_zero : corrMat 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [corrMat]

lemma reducedLaw_zero (r : ℕ) :
    reducedLaw r 0 = Measure.pi fun _ : Fin r => stdGaussian (EuclideanSpace ℝ (Fin 2)) := by
  simp [reducedLaw, corrMat_zero]

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

theorem matrix_grothendieck_identity_of_orthogonal (r n : ℕ) (_hr : 1 ≤ r)
    (u v : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : inner ℝ u v = 0) :
    grothendieckExpectation r n u v = Er r (inner ℝ u v) := by
  rw [grothendieckExpectation_eq_zero_of_inner_eq_zero u v hu hv h, h, Er_zero]

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

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Real RealInnerProductSpace

namespace Grothendieck

lemma Er_zero_lean (r : ℕ) : Er r 0 = 0 := by
  unfold Er
  simp

namespace Leaf2
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

theorem grothendieckExpectation_one {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
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

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

set_option maxHeartbeats 1000000

noncomputable section
open scoped BigOperators Real Topology
open Filter
namespace Grothendieck

lemma risingFact_succ' (a : ℝ) (k : ℕ) :
    risingFact a (k + 1) = risingFact a k * (a + (k : ℝ)) := by
  simp [risingFact, Finset.prod_range_succ]

lemma risingFact_three_half (k : ℕ) :
    risingFact (1 / 2 + 1) k = (2 * (k : ℝ) + 1) * risingFact (1 / 2) k := by
  induction k with
  | zero => simp [risingFact]
  | succ n ih =>
      rw [risingFact_succ', ih, risingFact_succ']
      push_cast
      ring

lemma risingFact_half_pos (k : ℕ) : 0 < risingFact (1 / 2) k := by
  induction k with
  | zero => simp [risingFact]
  | succ n ih =>
      rw [risingFact_succ']
      have : (0:ℝ) < 1 / 2 + (n:ℝ) := by positivity
      positivity

def bc (k : ℕ) : ℝ := risingFact (1 / 2) k / (k.factorial : ℝ)

lemma bc_zero : bc 0 = 1 := by simp [bc, risingFact]

lemma bc_pos (k : ℕ) : 0 < bc k := by
  unfold bc
  have h1 : (0:ℝ) < risingFact (1/2) k := risingFact_half_pos k
  have h2 : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  exact div_pos h1 h2

lemma bc_succ (k : ℕ) : ((k:ℝ) + 1) * bc (k+1) = ((k:ℝ) + 1/2) * bc k := by
  unfold bc
  rw [risingFact_succ', Nat.factorial_succ]
  push_cast
  have hpos : (0:ℝ) < risingFact (1/2) k := risingFact_half_pos k
  have hk : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hk0 : ((k:ℝ) + 1) ≠ 0 := ne_of_gt hk
  have hfk : ((k.factorial : ℕ) : ℝ) ≠ 0 := by
    have : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    exact ne_of_gt this
  field_simp
  ring

lemma bc_succ_div (k : ℕ) : bc (k+1) = bc k * (((k:ℝ) + 1/2) / ((k:ℝ) + 1)) := by
  have h := bc_succ k
  have hk : ((k:ℝ) + 1) ≠ 0 := by positivity
  field_simp at h ⊢
  linarith

lemma bc_le_one : ∀ k : ℕ, bc k ≤ 1 := by
  intro k
  induction k with
  | zero => simp [bc_zero]
  | succ n ih =>
      rw [bc_succ_div]
      have hle : (((n:ℝ) + 1/2) / ((n:ℝ) + 1)) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have hnn : 0 ≤ (((n:ℝ) + 1/2) / ((n:ℝ) + 1)) := by positivity
      nlinarith [bc_pos n]

lemma bc_nonneg (k : ℕ) : 0 ≤ bc k := le_of_lt (bc_pos k)

lemma bc_sq_bound : ∀ k : ℕ, (2*(k:ℝ)+1) * (bc k)^2 ≤ 1 := by
  intro k
  induction k with
  | zero => simp [bc_zero]
  | succ n ih =>
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hkey : bc (n+1) = bc n * (((n:ℝ) + 1/2) / ((n:ℝ) + 1)) := bc_succ_div n
      have hratio : (2*(n:ℝ)+3) * ((n:ℝ) + 1/2)^2 ≤ (2*(n:ℝ)+1) * ((n:ℝ) + 1)^2 := by
        nlinarith
      have hbn : (0:ℝ) ≤ (bc n)^2 := sq_nonneg _
      have h2 : (0:ℝ) < ((n:ℝ) + 1)^2 := by positivity
      have hmul : (2*(n:ℝ)+3) * ((n:ℝ) + 1/2)^2 * (bc n)^2
          ≤ (2*(n:ℝ)+1) * (bc n)^2 * ((n:ℝ) + 1)^2 := by
        have h := mul_le_mul_of_nonneg_right hratio hbn
        calc (2*(n:ℝ)+3) * ((n:ℝ) + 1/2)^2 * (bc n)^2
            ≤ ((2*(n:ℝ)+1) * ((n:ℝ) + 1)^2) * (bc n)^2 := h
          _ = (2*(n:ℝ)+1) * (bc n)^2 * ((n:ℝ) + 1)^2 := by ring
      have hid : (2*(n:ℝ)+3) * (bc (n+1))^2 * ((n:ℝ)+1)^2
          = (2*(n:ℝ)+3) * ((n:ℝ)+1/2)^2 * (bc n)^2 := by
        rw [hkey]
        field_simp
      have hstep : (2*(n:ℝ)+3) * (bc (n+1))^2 ≤ (2*(n:ℝ)+1) * (bc n)^2 := by
        have h := hmul
        rw [← hid] at h
        exact le_of_mul_le_mul_right h h2
      have hgoal : (2*((n:ℝ)+1)+1) * bc (n+1)^2 ≤ 1 := by
        rw [show (2*((n:ℝ)+1)+1) = 2*(n:ℝ)+3 by ring]
        linarith
      push_cast
      exact hgoal

lemma summable_abs_pow_sub_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (n:ℝ) * r^(n-1)) := by
  have hr1' : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hr0]
  have hid : (fun n : ℕ => (n:ℝ) * r^(n-1)) = fun n : ℕ => ((n:ℝ) * r^n) / r := by
    funext n
    rcases n with _ | k
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]
      field_simp
  rw [hid]
  simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 hr1').div_const r

lemma summable_abs_pow_sub_one' {x : ℝ} (hx : |x| < 1) :
    Summable (fun n : ℕ => (n:ℝ) * |x|^(n-1)) := by
  rcases eq_or_lt_of_le (abs_nonneg x) with h | h
  · rw [← h]
    refine summable_of_ne_finset_zero (s := ({0, 1} : Finset ℕ)) ?_
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    obtain ⟨h1, h0⟩ := hn
    have hne : n - 1 ≠ 0 := by omega
    rw [zero_pow hne]
    ring
  · exact summable_abs_pow_sub_one h hx

lemma summable_bc_mul_pow {x : ℝ} (hx : |x| < 1) : Summable (fun k : ℕ => bc k * x^k) := by
  have hg : Summable (fun k : ℕ => ‖x‖^k) :=
    summable_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs, abs_abs] using hx)
  refine Summable.of_norm_bounded hg (fun k => ?_)
  rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos (bc_pos k)]
  have h1 : bc k ≤ 1 := bc_le_one k
  have h0 : (0:ℝ) ≤ ‖x‖^k := by positivity
  nlinarith

lemma summable_bc_mul_pow_shift {x : ℝ} (hx : |x| < 1) :
    Summable (fun n : ℕ => (n:ℝ) * bc n * x^(n-1)) := by
  refine Summable.of_norm_bounded (summable_abs_pow_sub_one' hx) (fun n => ?_)
  have hstep : ‖(n:ℝ) * bc n * x^(n-1)‖ = (n:ℝ) * bc n * |x|^(n-1) := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (bc_pos n),
        abs_of_nonneg (Nat.cast_nonneg n)]
  rw [hstep]
  have h1 : bc n ≤ 1 := bc_le_one n
  have hy : (0:ℝ) ≤ |x|^(n-1) := by positivity
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have h2 : (n:ℝ) * bc n * |x|^(n-1) ≤ (n:ℝ) * 1 * |x|^(n-1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hn) hy
  linarith

def Bfun (x : ℝ) : ℝ := ∑' k : ℕ, bc k * x^k

def Afun (x : ℝ) : ℝ := ∑' k : ℕ, ((k:ℝ)+1) * bc (k+1) * x^k

lemma Bfun_zero : Bfun 0 = 1 := by
  rw [Bfun, tsum_eq_single 0]
  · simp [bc_zero]
  · intro b hb
    simp [hb]

lemma summable_Afun {x : ℝ} (hx : |x| < 1) :
    Summable (fun k : ℕ => ((k:ℝ)+1) * bc (k+1) * x^k) := by
  have hs : Summable (fun n : ℕ => (n:ℝ) * bc n * x^(n-1)) := summable_bc_mul_pow_shift hx
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => (n:ℝ) * bc n * x^(n-1)) 1).mpr hs
  simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using hshift

lemma tsum_deriv_shift {x : ℝ} (hx : |x| < 1) :
    (∑' n : ℕ, (n:ℝ) * bc n * x^(n-1)) = Afun x := by
  have hs := summable_bc_mul_pow_shift hx
  have h := Summable.tsum_eq_zero_add hs
  simp only [Nat.cast_zero, zero_mul, Nat.zero_sub, pow_zero, mul_one, zero_add,
    Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at h
  rw [Afun, ← h]

lemma hasDerivAt_Bfun {x : ℝ} (hx : |x| < 1) : HasDerivAt Bfun (Afun x) x := by
  obtain ⟨r, hrx, hr1⟩ : ∃ r : ℝ, |x| < r ∧ r < 1 := ⟨(|x| + 1)/2, by linarith, by linarith⟩
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg x) hrx
  have hmem : x ∈ Set.Ioo (-r) r := by
    rw [Set.mem_Ioo]
    exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have hu : Summable (fun n : ℕ => (n:ℝ) * r^(n-1)) := summable_abs_pow_sub_one hr0 hr1
  have hderiv : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-r) r →
      HasDerivAt (fun y : ℝ => bc n * y^n) ((n:ℝ) * bc n * y^(n-1)) y := by
    intro n y _
    have h1 : HasDerivAt (fun y : ℝ => y^n) ((n:ℝ) * y^(n-1)) y := hasDerivAt_pow n y
    have h2 := h1.const_mul (bc n)
    have he : bc n * ((n:ℝ) * y^(n-1)) = (n:ℝ) * bc n * y^(n-1) := by ring
    rw [he] at h2
    exact h2
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-r) r →
      ‖(n:ℝ) * bc n * y^(n-1)‖ ≤ (n:ℝ) * r^(n-1) := by
    intro n y hy
    have hy' : |y| ≤ r := by
      rw [abs_le]; exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp
    · have hstep : ‖(n:ℝ) * bc n * y^(n-1)‖ = (n:ℝ) * bc n * |y|^(n-1) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (bc_pos n),
          abs_of_nonneg (Nat.cast_nonneg n)]
      rw [hstep]
      have hpow : |y|^(n-1) ≤ r^(n-1) := pow_le_pow_left₀ (abs_nonneg y) hy' _
      have h1 : bc n ≤ 1 := bc_le_one n
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have h3 : (0:ℝ) ≤ |y|^(n-1) := by positivity
      have hb1 : (n:ℝ) * bc n * |y|^(n-1) ≤ (n:ℝ) * 1 * |y|^(n-1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hn) h3
      have hb2 : (n:ℝ) * 1 * |y|^(n-1) ≤ (n:ℝ) * 1 * r^(n-1) :=
        mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ) ≤ (n:ℝ) * 1)
      calc (n:ℝ) * bc n * |y|^(n-1) ≤ (n:ℝ) * 1 * |y|^(n-1) := hb1
        _ ≤ (n:ℝ) * 1 * r^(n-1) := hb2
        _ = (n:ℝ) * r^(n-1) := by ring
  have hpt : (0:ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, by linarith⟩
  have hsum0 : Summable (fun n : ℕ => bc n * (0:ℝ)^n) := by
    refine summable_of_ne_finset_zero (s := ({0} : Finset ℕ)) ?_
    intro n hn
    have hn0 : n ≠ 0 := by simpa using hn
    simp [hn0]
  have hmain := hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ) (y₀ := (0:ℝ))
    (u := fun n : ℕ => (n:ℝ) * r^(n-1))
    (g := fun (n:ℕ) (y:ℝ) => bc n * y^n)
    (g' := fun (n:ℕ) (y:ℝ) => (n:ℝ) * bc n * y^(n-1))
    (t := Set.Ioo (-r) r) hu isOpen_Ioo isPreconnected_Ioo hderiv hbound hpt hsum0 hmem
  rw [← tsum_deriv_shift hx]
  exact hmain

lemma bc_recur (k : ℕ) : ((k:ℝ)+1) * bc (k+1) - (k:ℝ) * bc k = (1/2) * bc k := by
  have h := bc_succ k
  linarith

lemma summable_k_bc_pow {x : ℝ} (hx : |x| < 1) :
    Summable (fun k : ℕ => (k:ℝ) * bc k * x^k) := by
  have hg : Summable (fun k : ℕ => (k:ℝ) * |x|^k) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1
      (r := |x|) (by simpa only [Real.norm_eq_abs, abs_abs] using hx)
    simpa using h
  refine Summable.of_norm_bounded hg (fun n => ?_)
  have hstep : ‖(n:ℝ) * bc n * x^n‖ = (n:ℝ) * bc n * |x|^n := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (bc_pos n),
      abs_of_nonneg (Nat.cast_nonneg n)]
  rw [hstep]
  have h1 : bc n ≤ 1 := bc_le_one n
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have h3 : (0:ℝ) ≤ |x|^n := by positivity
  have hb1 : (n:ℝ) * bc n * |x|^n ≤ (n:ℝ) * 1 * |x|^n :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hn) h3
  calc (n:ℝ) * bc n * |x|^n ≤ (n:ℝ) * 1 * |x|^n := hb1
    _ = (n:ℝ) * |x|^n := by ring

lemma Bfun_ode {x : ℝ} (hx : |x| < 1) : (1 - x) * Afun x = (1/2) * Bfun x := by
  have hA : Summable (fun k : ℕ => ((k:ℝ)+1) * bc (k+1) * x^k) := summable_Afun hx
  have hB : Summable (fun k : ℕ => bc k * x^k) := summable_bc_mul_pow hx
  have hk : Summable (fun k : ℕ => (k:ℝ) * bc k * x^k) := summable_k_bc_pow hx
  have hxA : x * Afun x = ∑' k : ℕ, ((k:ℝ)+1) * bc (k+1) * x^(k+1) := by
    rw [Afun, ← Summable.tsum_mul_left x hA]
    exact tsum_congr (fun k => by ring)
  have hshift : (∑' k : ℕ, ((k:ℝ)+1) * bc (k+1) * x^(k+1))
      = ∑' k : ℕ, (k:ℝ) * bc k * x^k := by
    have h := Summable.tsum_eq_zero_add hk
    simp only [Nat.cast_zero, zero_mul, zero_add] at h
    refine Eq.trans ?_ h.symm
    refine tsum_congr (fun k => ?_)
    push_cast
    ring
  have hsub : Afun x - x * Afun x
      = ∑' k : ℕ, (((k:ℝ)+1) * bc (k+1) - (k:ℝ) * bc k) * x^k := by
    rw [hxA, Afun, hshift, ← Summable.tsum_sub hA hk]
    exact tsum_congr (fun k => by ring)
  have hhalf : (∑' k : ℕ, (((k:ℝ)+1) * bc (k+1) - (k:ℝ) * bc k) * x^k)
      = (1/2) * Bfun x := by
    rw [Bfun, ← Summable.tsum_mul_left (1/2) hB]
    exact tsum_congr (fun k => by rw [bc_recur k]; ring)
  rw [← hhalf, ← hsub]
  ring

def Qfun (x : ℝ) : ℝ := (1 - x) ^ (-(1/2) : ℝ)

lemma hasDerivAt_Qfun {x : ℝ} (hx : x < 1) :
    HasDerivAt Qfun ((1/2) * (1-x)^(-(3/2) : ℝ)) x := by
  have hf : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub (1:ℝ)
  have hg : HasDerivAt (fun _ : ℝ => (-(1/2) : ℝ)) 0 x := hasDerivAt_const x _
  have hpos : (0:ℝ) < 1 - x := by linarith
  have h := hf.rpow hg hpos
  have hsimp : (-1 : ℝ) * (-(1/2)) * (1-x)^((-(1/2) : ℝ) - 1) + 0 * (1-x)^(-(1/2):ℝ) * Real.log (1-x)
      = (1/2) * (1-x)^(-(3/2) : ℝ) := by
    rw [show (-(1/2) : ℝ) - 1 = -(3/2) by ring]
    ring
  rw [hsimp] at h
  exact h

lemma Qfun_ode {x : ℝ} (hx : x < 1) :
    (1 - x) * ((1/2) * (1-x)^(-(3/2) : ℝ)) = (1/2) * Qfun x := by
  unfold Qfun
  have hpos : (0:ℝ) < 1 - x := by linarith
  have h := Real.rpow_add hpos (1:ℝ) (-(3/2) : ℝ)
  rw [show (1:ℝ) + (-(3/2)) = -(1/2) by ring, Real.rpow_one] at h
  rw [h]
  ring

lemma eq_zero_of_hasDerivAt_zero {f : ℝ → ℝ}
    (h : ∀ y ∈ Set.Ioo (-1:ℝ) 1, HasDerivAt f 0 y) (h0 : f 0 = 0) :
    ∀ x ∈ Set.Ioo (-1:ℝ) 1, f x = 0 := by
  intro x hx
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hlt
      (fun y hy => ((h y ⟨by linarith [hy.1, hx.1], by linarith [hy.2]⟩).continuousAt).continuousWithinAt)
      (fun y hy => (h y ⟨by linarith [hy.1, hx.1], by linarith [hy.2]⟩).differentiableAt.differentiableWithinAt)
    have hc' : c ∈ Set.Ioo (-1:ℝ) 1 := ⟨by linarith [hc.1, hx.1], by linarith [hc.2]⟩
    rw [(h c hc').deriv] at hcd
    have hne : (0:ℝ) - x ≠ 0 := by linarith
    field_simp at hcd
    linarith [hcd]
  · rw [heq]; exact h0
  · obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hgt
      (fun y hy => ((h y ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩).continuousAt).continuousWithinAt)
      (fun y hy => (h y ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩).differentiableAt.differentiableWithinAt)
    have hc' : c ∈ Set.Ioo (-1:ℝ) 1 := ⟨by linarith [hc.1], by linarith [hc.2, hx.2]⟩
    rw [(h c hc').deriv] at hcd
    have hne : x - 0 ≠ 0 := by linarith
    field_simp at hcd
    linarith [hcd]

theorem Bfun_eq {x : ℝ} (hx : |x| < 1) : Bfun x = (1 - x) ^ (-(1/2) : ℝ) := by
  obtain ⟨hx1, hx2⟩ := abs_lt.mp hx
  set D : ℝ → ℝ := fun y => Bfun y - Qfun y with hD
  have hDderiv : ∀ y ∈ Set.Ioo (-1:ℝ) 1, HasDerivAt D (D y / (2*(1-y))) y := by
    intro y hy
    have hy1 : y < 1 := hy.2
    have habs : |y| < 1 := by rw [abs_lt]; exact hy
    have h1 : HasDerivAt Bfun (Afun y) y := hasDerivAt_Bfun habs
    have h2 : HasDerivAt Qfun ((1/2)*(1-y)^(-(3/2) : ℝ)) y := hasDerivAt_Qfun hy1
    have hB := Bfun_ode habs
    have hQ := Qfun_ode hy1
    have hne : (1:ℝ) - y ≠ 0 := by linarith
    have hval : Afun y - (1/2)*(1-y)^(-(3/2) : ℝ) = (Bfun y - Qfun y)/(2*(1-y)) := by
      field_simp
      linarith [hB, hQ]
    have h3 : HasDerivAt (fun z => Bfun z - Qfun z) ((Bfun y - Qfun y)/(2*(1-y))) y := by
      have h1' : HasDerivAt (fun z => Bfun z - Qfun z)
          (Afun y - (1/2)*(1-y)^(-(3/2) : ℝ)) y := h1.sub h2
      rw [hval] at h1'
      exact h1'
    rw [hD]
    exact h3
  have hE : ∀ y ∈ Set.Ioo (-1:ℝ) 1, HasDerivAt (fun z => (D z)^2 * (1-z)) 0 y := by
    intro y hy
    have h1 : HasDerivAt D (D y / (2*(1-y))) y := hDderiv y hy
    have h2 : HasDerivAt (fun z => D z * D z)
        ((D y/(2*(1-y))) * D y + D y * (D y/(2*(1-y)))) y := h1.mul h1
    have h3 : HasDerivAt (fun z : ℝ => 1 - z) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub (1:ℝ)
    have h4 : HasDerivAt (fun z => (D z * D z) * (1-z))
        (((D y/(2*(1-y))) * D y + D y * (D y/(2*(1-y)))) * (1-y) + (D y * D y) * (-1)) y :=
      h2.mul h3
    have hne : (1:ℝ) - y ≠ 0 := by linarith [hy.2]
    have hzero : ((D y/(2*(1-y))) * D y + D y * (D y/(2*(1-y)))) * (1-y) + (D y * D y) * (-1) = 0 := by
      field_simp
      ring
    rw [hzero] at h4
    convert h4 using 1
    ring_nf
  have hone := eq_zero_of_hasDerivAt_zero hE (by simp [D, Bfun_zero, Qfun])
  have hdx : D x = 0 := by
    have hz := hone x ⟨hx1, hx2⟩
    have h1x : (0:ℝ) < 1 - x := by linarith
    have hsq : (D x)^2 = 0 := by
      rcases mul_eq_zero.mp hz with h | h
      · exact h
      · exact absurd h (ne_of_gt h1x)
    by_contra hne0
    have hpos : (0:ℝ) < (D x)^2 := by positivity
    linarith
  rw [hD] at hdx
  simpa [Qfun, sub_eq_zero] using hdx

def Ffun (t : ℝ) : ℝ := ∑' k : ℕ, bc k / (2*(k:ℝ)+1) * t^(2*k+1)

lemma Ffun_zero : Ffun 0 = 0 := by
  rw [Ffun]
  have h : (fun k : ℕ => bc k / (2*(k:ℝ)+1) * (0:ℝ)^(2*k+1)) = fun _ => 0 := by
    funext k
    have hz : (2*k+1) ≠ 0 := by omega
    rw [zero_pow hz]
    ring
  rw [h, tsum_zero]

lemma summable_Ffun {t : ℝ} (ht : |t| < 1) :
    Summable (fun k : ℕ => bc k / (2*(k:ℝ)+1) * t^(2*k+1)) := by
  have hg : Summable (fun k : ℕ => |t|^k) :=
    summable_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs, abs_abs] using ht)
  refine Summable.of_norm_bounded hg (fun n => ?_)
  have hd : (0:ℝ) < 2*(n:ℝ)+1 := by positivity
  have hstep : ‖bc n / (2*(n:ℝ)+1) * t^(2*n+1)‖ = bc n / (2*(n:ℝ)+1) * |t|^(2*n+1) := by
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (bc_pos n), abs_of_pos hd, abs_pow]
  rw [hstep]
  have ht0 : |t| < 1 := ht
  have ht1 : |t| ^ (2*n+1) ≤ |t|^n := by
    have hnn : (0:ℝ) ≤ |t| := abs_nonneg t
    exact pow_le_pow_of_le_one hnn ht0.le (by omega)
  have hle : bc n / (2*(n:ℝ)+1) * |t|^(2*n+1) ≤ 1 * |t|^n := by
    have hbc : bc n / (2*(n:ℝ)+1) ≤ 1 := by
      rw [div_le_one hd]
      have h1 : bc n ≤ 1 := bc_le_one n
      linarith
    have hnn : (0:ℝ) ≤ |t|^(2*n+1) := by positivity
    calc bc n / (2*(n:ℝ)+1) * |t|^(2*n+1) ≤ 1 * |t|^(2*n+1) :=
          mul_le_mul_of_nonneg_right hbc hnn
      _ ≤ 1 * |t|^n := mul_le_mul_of_nonneg_left ht1 zero_le_one
  simpa using hle

lemma hasDerivAt_Ffun {t : ℝ} (ht : |t| < 1) : HasDerivAt Ffun (Bfun (t^2)) t := by
  obtain ⟨r, hrt, hr1⟩ : ∃ r : ℝ, |t| < r ∧ r < 1 := ⟨(|t| + 1)/2, by linarith, by linarith⟩
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg t) hrt
  have hmem : t ∈ Set.Ioo (-r) r := by
    rw [Set.mem_Ioo]
    exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  -- summable bound: r^{2n}
  have hr2 : r^2 < 1 := by nlinarith [hr0, hr1]
  have hu : Summable (fun n : ℕ => ((r^2)^n)) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < r^2)]
    exact hr2
  have hderiv : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-r) r →
      HasDerivAt (fun y : ℝ => bc n / (2*(n:ℝ)+1) * y^(2*n+1)) (bc n * y^(2*n)) y := by
    intro n y _
    have h1 : HasDerivAt (fun y : ℝ => y^(2*n+1)) ((2*(n:ℝ)+1) * y^(2*n)) y := by
      have h := hasDerivAt_pow (2*n+1) y
      have he : ((2*n+1 : ℕ) : ℝ) = 2*(n:ℝ)+1 := by push_cast; ring
      rw [he] at h
      have hsub : 2*n+1-1 = 2*n := by omega
      rw [hsub] at h
      exact h
    have h2 := h1.const_mul (bc n / (2*(n:ℝ)+1))
    have hden : (2*(n:ℝ)+1) ≠ 0 := by positivity
    have heq : bc n / (2*(n:ℝ)+1) * ((2*(n:ℝ)+1) * y^(2*n)) = bc n * y^(2*n) := by
      field_simp
    rw [heq] at h2
    exact h2
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-r) r → ‖bc n * y^(2*n)‖ ≤ (r^2)^n := by
    intro n y hy
    have hy' : |y| ≤ r := by rw [abs_le]; exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hstep : ‖bc n * y^(2*n)‖ = bc n * |y|^(2*n) := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (bc_pos n), abs_pow]
    rw [hstep]
    have h1 : bc n ≤ 1 := bc_le_one n
    have hpow : |y|^(2*n) ≤ r^(2*n) := pow_le_pow_left₀ (abs_nonneg y) hy' _
    have hrw : r^(2*n) = (r^2)^n := by rw [← pow_mul]
    rw [hrw] at hpow
    calc bc n * |y|^(2*n) ≤ 1 * (r^2)^n := by
          apply mul_le_mul h1 hpow (by positivity) (by positivity)
      _ = (r^2)^n := by ring
  have hpt : (0:ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, by linarith⟩
  have hsum0 : Summable (fun n : ℕ => bc n / (2*(n:ℝ)+1) * (0:ℝ)^(2*n+1)) := by
    refine summable_of_ne_finset_zero (s := (∅ : Finset ℕ)) ?_
    intro n _
    have h : (2*n+1) ≠ 0 := by omega
    rw [zero_pow h]
    ring
  have hmain := hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ) (y₀ := (0:ℝ))
    (u := fun n : ℕ => (r^2)^n)
    (g := fun (n:ℕ) (y:ℝ) => bc n / (2*(n:ℝ)+1) * y^(2*n+1))
    (g' := fun (n:ℕ) (y:ℝ) => bc n * y^(2*n))
    (t := Set.Ioo (-r) r) hu isOpen_Ioo isPreconnected_Ioo hderiv hbound hpt hsum0 hmem
  have hfin : (∑' n : ℕ, bc n * t^(2*n)) = Bfun (t^2) := by
    rw [Bfun]
    exact tsum_congr (fun n => by rw [pow_mul])
  rw [← hfin]
  exact hmain

lemma hasDerivAt_arcsin' {t : ℝ} (ht : |t| < 1) :
    HasDerivAt Real.arcsin ((1 - t^2) ^ (-(1/2) : ℝ)) t := by
  have ht1 : t ≠ 1 := by
    intro h; rw [h] at ht; norm_num at ht
  have ht2 : t ≠ -1 := by
    intro h; rw [h] at ht; norm_num at ht
  have h := Real.hasDerivAt_arcsin ht2 ht1
  have hpos : (0:ℝ) < 1 - t^2 := by
    have := abs_lt.mp ht
    nlinarith [this.1, this.2]
  have heq : (1:ℝ) / √(1 - t^2) = (1 - t^2) ^ (-(1/2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hpos.le]
  rw [heq] at h
  exact h

theorem Ffun_eq_arcsin {t : ℝ} (ht : |t| < 1) : Ffun t = Real.arcsin t := by
  have key : ∀ y ∈ Set.Ioo (-1:ℝ) 1, HasDerivAt (fun z => Ffun z - Real.arcsin z) 0 y := by
    intro y hy
    have hyabs : |y| < 1 := by rw [abs_lt]; exact hy
    have h1 : HasDerivAt Ffun (Bfun (y^2)) y := hasDerivAt_Ffun hyabs
    have h2 : HasDerivAt Real.arcsin ((1-y^2)^(-(1/2):ℝ)) y := hasDerivAt_arcsin' hyabs
    have hy2 : |y^2| < 1 := by
      rw [abs_lt]; constructor <;> nlinarith [hy.1, hy.2]
    have h3 : Bfun (y^2) = (1-y^2)^(-(1/2):ℝ) := Bfun_eq hy2
    have h4 : HasDerivAt (fun z => Ffun z - Real.arcsin z)
        (Bfun (y^2) - (1-y^2)^(-(1/2):ℝ)) y := h1.sub h2
    rw [h3, sub_self] at h4
    exact h4
  have h0 : (fun z => Ffun z - Real.arcsin z) 0 = 0 := by
    simp [Ffun_zero]
  have hfin := eq_zero_of_hasDerivAt_zero key h0 t (abs_lt.mp ht)
  simp only [sub_eq_zero] at hfin
  exact hfin

lemma Cr_one : Cr 1 = 2 / Real.pi := by
  unfold Cr
  norm_num
  rw [Real.Gamma_one_half_eq, Real.sq_sqrt Real.pi_pos.le, div_eq_mul_inv]

lemma ErCoeff_one (k : ℕ) : ErCoeff 1 k = Cr 1 * (bc k / (2*(k:ℝ)+1)) := by
  unfold ErCoeff bc
  simp only [Nat.cast_one]
  rw [risingFact_three_half]
  push_cast
  have hpos : (0:ℝ) < risingFact (1/2) k := risingFact_half_pos k
  have hk : ((k.factorial : ℕ) : ℝ) ≠ 0 := by
    have : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    exact ne_of_gt this
  have h2k : (2*(k:ℝ)+1) ≠ 0 := by positivity
  field_simp

theorem Er_one {t : ℝ} (ht : |t| < 1) : Er 1 t = 2 / Real.pi * Real.arcsin t := by
  have hsummable : Summable (fun k : ℕ => bc k / (2*(k:ℝ)+1) * t^(2*k+1)) := summable_Ffun ht
  have hstep : (∑' k : ℕ, ErCoeff 1 k * t^(2*k+1)) = (2/Real.pi) * Ffun t := by
    rw [Ffun, ← Summable.tsum_mul_left (2/Real.pi) hsummable]
    exact tsum_congr (fun k => by rw [ErCoeff_one, Cr_one]; ring)
  rw [Er, hstep, Ffun_eq_arcsin ht]

lemma bc_telescope (k : ℕ) : bc k - bc (k+1) = bc k / (2*((k:ℝ)+1)) := by
  have h := bc_succ k
  have hk : ((k:ℝ)+1) ≠ 0 := by positivity
  field_simp at h ⊢
  linarith

lemma bc_div_le (k : ℕ) : bc k / (2*(k:ℝ)+1) ≤ 2 * (bc k - bc (k+1)) := by
  rw [bc_telescope]
  have h1 : (0:ℝ) < (k:ℝ)+1 := by positivity
  have h3 : (0:ℝ) ≤ bc k := bc_nonneg k
  have h4 : (k:ℝ)+1 ≤ 2*(k:ℝ)+1 := by
    have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have h5 : bc k / (2*(k:ℝ)+1) ≤ bc k / ((k:ℝ)+1) :=
    div_le_div_of_nonneg_left h3 h1 h4
  have h6 : (2:ℝ) * (bc k / (2*((k:ℝ)+1))) = bc k / ((k:ℝ)+1) := by
    field_simp
  rw [h6]
  exact h5

lemma summable_bc_div : Summable (fun k : ℕ => bc k / (2*(k:ℝ)+1)) := by
  refine summable_of_sum_range_le (f := fun k : ℕ => bc k / (2*(k:ℝ)+1)) (c := 2)
    (fun n => ?_) (fun n => ?_)
  · have h1 : (0:ℝ) < bc n := bc_pos n
    have h2 : (0:ℝ) < 2*(n:ℝ)+1 := by positivity
    positivity
  · calc ∑ k ∈ Finset.range n, bc k / (2*(k:ℝ)+1)
        ≤ ∑ k ∈ Finset.range n, 2 * (bc k - bc (k+1)) :=
          Finset.sum_le_sum (fun k _ => bc_div_le k)
      _ = 2 * (bc 0 - bc n) := by
          rw [← Finset.mul_sum]
          have h := Finset.sum_range_sub (f := bc) n
          have h2 : ∑ i ∈ Finset.range n, (bc i - bc (i + 1))
              = -(∑ i ∈ Finset.range n, (bc (i + 1) - bc i)) := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl (fun i _ => by ring)
          rw [h2, h]
          ring
      _ ≤ 2 := by
          have h1 : bc 0 = 1 := bc_zero
          have h2 : 0 < bc n := bc_pos n
          rw [h1]
          linarith

lemma ErCoeff_one_nonneg (n : ℕ) : 0 ≤ ErCoeff 1 n := by
  rw [ErCoeff_one]
  have h1 : (0:ℝ) < Cr 1 := by rw [Cr_one]; positivity
  have h2 : (0:ℝ) ≤ bc n / (2*(n:ℝ)+1) := by
    have h3 : (0:ℝ) < bc n := bc_pos n
    have h4 : (0:ℝ) < 2*(n:ℝ)+1 := by positivity
    positivity
  positivity

lemma summable_ErCoeff_one : Summable (fun k : ℕ => ErCoeff 1 k) := by
  have h := summable_bc_div.mul_left (Cr 1)
  have h2 : (fun k : ℕ => Cr 1 * (bc k / (2*(k:ℝ)+1))) = fun k => ErCoeff 1 k := by
    funext k
    exact (ErCoeff_one k).symm
  rw [h2] at h
  exact h

lemma continuousOn_Er_one : ContinuousOn (fun t => Er 1 t) (Set.Icc (-1:ℝ) 1) := by
  have hu := summable_ErCoeff_one
  have hb : ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (-1:ℝ) 1 →
      ‖ErCoeff 1 n * x^(2*n+1)‖ ≤ ErCoeff 1 n := by
    intro n x hx
    have hx1 : |x| ≤ 1 := by rw [abs_le]; exact ⟨hx.1, hx.2⟩
    have hlt : |x|^(2*n+1) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (ErCoeff_one_nonneg n)]
    calc ErCoeff 1 n * |x|^(2*n+1) ≤ ErCoeff 1 n * 1 := by
          apply mul_le_mul_of_nonneg_left hlt (ErCoeff_one_nonneg n)
      _ = ErCoeff 1 n := by ring
  have hunif := tendstoUniformlyOn_tsum hu hb
  have hcont : ∀ (s : Finset ℕ), ContinuousOn
      (fun t : ℝ => ∑ k ∈ s, ErCoeff 1 k * t^(2*k+1)) (Set.Icc (-1:ℝ) 1) := by
    intro s
    have hc : Continuous (fun t : ℝ => ∑ k ∈ s, ErCoeff 1 k * t^(2*k+1)) := by
      apply continuous_finset_sum
      intro k _
      fun_prop
    exact hc.continuousOn
  exact hunif.continuousOn (Eventually.of_forall hcont).frequently

theorem Er_one_arcsin {t : ℝ} (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    Er 1 t = 2 / Real.pi * Real.arcsin t := by
  obtain ⟨ht1, ht2⟩ := ht
  have keym1 : Er 1 (-1) = 2 / Real.pi * Real.arcsin (-1) := by
    haveI : (𝓝[Set.Ioo (-1:ℝ) 1] (-1)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num : (-1:ℝ) ≠ 1)]
      exact ⟨le_rfl, by norm_num⟩
    have hcontIcc : ContinuousWithinAt (fun t => Er 1 t) (Set.Icc (-1:ℝ) 1) (-1) :=
      continuousOn_Er_one.continuousWithinAt (by simp)
    have h2 : Tendsto (fun t => Er 1 t) (𝓝[Set.Ioo (-1:ℝ) 1] (-1)) (𝓝 (Er 1 (-1))) :=
      hcontIcc.mono_left (nhdsWithin_mono _ Set.Ioo_subset_Icc_self)
    have hg : ContinuousWithinAt (fun t => 2 / Real.pi * Real.arcsin t) (Set.Ioo (-1:ℝ) 1) (-1) :=
      (continuous_const.mul Real.continuous_arcsin).continuousWithinAt
    have h3 : Tendsto (fun t => Er 1 t) (𝓝[Set.Ioo (-1:ℝ) 1] (-1))
        (𝓝 (2 / Real.pi * Real.arcsin (-1))) :=
      hg.congr' (eventually_of_mem self_mem_nhdsWithin
        (fun y hy => (Er_one (by rw [abs_lt]; exact hy)).symm))
    exact tendsto_nhds_unique h2 h3
  have key1 : Er 1 1 = 2 / Real.pi * Real.arcsin 1 := by
    haveI : (𝓝[Set.Ioo (-1:ℝ) 1] 1).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num : (-1:ℝ) ≠ 1)]
      exact ⟨by norm_num, le_rfl⟩
    have hcontIcc : ContinuousWithinAt (fun t => Er 1 t) (Set.Icc (-1:ℝ) 1) 1 :=
      continuousOn_Er_one.continuousWithinAt (by simp)
    have h2 : Tendsto (fun t => Er 1 t) (𝓝[Set.Ioo (-1:ℝ) 1] 1) (𝓝 (Er 1 1)) :=
      hcontIcc.mono_left (nhdsWithin_mono _ Set.Ioo_subset_Icc_self)
    have hg : ContinuousWithinAt (fun t => 2 / Real.pi * Real.arcsin t) (Set.Ioo (-1:ℝ) 1) 1 :=
      (continuous_const.mul Real.continuous_arcsin).continuousWithinAt
    have h3 : Tendsto (fun t => Er 1 t) (𝓝[Set.Ioo (-1:ℝ) 1] 1)
        (𝓝 (2 / Real.pi * Real.arcsin 1)) :=
      hg.congr' (eventually_of_mem self_mem_nhdsWithin
        (fun y hy => (Er_one (by rw [abs_lt]; exact hy)).symm))
    exact tendsto_nhds_unique h2 h3
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · rcases lt_trichotomy t (-1) with h | h | h
    · linarith
    · rw [h]; exact keym1
    · exact Er_one (by rw [abs_lt]; exact ⟨h, hlt⟩)
  · rw [heq]; exact key1
  · linarith

lemma Cr_pos {r : ℕ} (hr : 1 ≤ r) : 0 < Cr r := by
  unfold Cr
  have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have h1 : (0:ℝ) < Real.Gamma (((r:ℝ)+1)/2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have h2 : (0:ℝ) < Real.Gamma ((r:ℝ)/2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have : (0:ℝ) < Real.Gamma (((r:ℝ)+1)/2) / Real.Gamma ((r:ℝ)/2) := div_pos h1 h2
  positivity

lemma risingFact_half_sq_pos (k : ℕ) : 0 < (risingFact (1/2) k)^2 := by
  have := risingFact_half_pos k
  positivity

lemma risingFact_arg_pos {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : 0 < risingFact ((r:ℝ)/2+1) k := by
  unfold risingFact
  apply Finset.prod_pos
  intro i _
  have h1 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
  have h2 : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  push_cast
  linarith

theorem ErCoeff_nonneg {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : 0 ≤ ErCoeff r k := by
  unfold ErCoeff
  have h1 : 0 < Cr r := Cr_pos hr
  have h2 : 0 < (risingFact (1/2) k)^2 := risingFact_half_sq_pos k
  have h3 : 0 < risingFact ((r:ℝ)/2+1) k := risingFact_arg_pos hr k
  have h4 : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  positivity

theorem abs_Er_one_le_one {t : ℝ} (ht : t ∈ Set.Icc (-1:ℝ) 1) : |Er 1 t| ≤ 1 := by
  rw [Er_one_arcsin ht, abs_mul]
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h1 : |2 / Real.pi| = 2 / Real.pi := by
    rw [abs_of_pos]; positivity
  rw [h1]
  have h2 : |Real.arcsin t| ≤ Real.pi / 2 :=
    abs_le.mpr ⟨Real.neg_pi_div_two_le_arcsin t, Real.arcsin_le_pi_div_two t⟩
  calc 2 / Real.pi * |Real.arcsin t| ≤ 2 / Real.pi * (Real.pi / 2) := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 := by field_simp

end Grothendieck

namespace Grothendieck

lemma risingFact_mono_arg {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    risingFact (1/2+1) k ≤ risingFact ((r:ℝ)/2+1) k := by
  unfold risingFact
  apply Finset.prod_le_prod
  · intro i _
    have h : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
    linarith
  · intro i _
    have h : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    linarith

lemma ErCoeff_le {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    ErCoeff r k ≤ Cr r * (bc k / (2*(k:ℝ)+1)) := by
  unfold ErCoeff
  have hC : 0 < Cr r := Cr_pos hr
  have hsq : 0 < (risingFact (1/2) k)^2 := risingFact_half_sq_pos k
  have hfk : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hden1 : 0 < risingFact (1/2+1) k := by
    unfold risingFact
    apply Finset.prod_pos
    intro i _
    have h : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
    push_cast
    linarith
  have hden2 : 0 < risingFact ((r:ℝ)/2+1) k := risingFact_arg_pos hr k
  have hmono : risingFact (1/2+1) k ≤ risingFact ((r:ℝ)/2+1) k := risingFact_mono_arg hr k
  have h1 : (risingFact (1/2) k)^2 / (risingFact ((r:ℝ)/2+1) k * (k.factorial:ℝ))
      ≤ (risingFact (1/2) k)^2 / (risingFact (1/2+1) k * (k.factorial:ℝ)) := by
    apply div_le_div_of_nonneg_left (le_of_lt hsq) (by positivity)
    exact mul_le_mul_of_nonneg_right hmono (le_of_lt hfk)
  calc Cr r * (risingFact (1/2) k)^2 / (risingFact ((r:ℝ)/2+1) k * (k.factorial:ℝ))
      = Cr r * ((risingFact (1/2) k)^2 / (risingFact ((r:ℝ)/2+1) k * (k.factorial:ℝ))) := by
        field_simp
    _ ≤ Cr r * ((risingFact (1/2) k)^2 / (risingFact (1/2+1) k * (k.factorial:ℝ))) := by
        apply mul_le_mul_of_nonneg_left h1 (le_of_lt hC)
    _ = Cr r * (bc k / (2*(k:ℝ)+1)) := by
        rw [risingFact_three_half]
        unfold bc
        have h2k : (0:ℝ) < 2*(k:ℝ)+1 := by positivity
        have hrf : (0:ℝ) < risingFact (1/2) k := risingFact_half_pos k
        field_simp

lemma summable_ErCoeff {r : ℕ} (hr : 1 ≤ r) : Summable (fun k : ℕ => ErCoeff r k) := by
  have h := summable_bc_div.mul_left (Cr r)
  exact Summable.of_nonneg_of_le (fun k => ErCoeff_nonneg hr k) (fun k => ErCoeff_le hr k) h

lemma continuousOn_Er {r : ℕ} (hr : 1 ≤ r) : ContinuousOn (fun t => Er r t) (Set.Icc (-1:ℝ) 1) := by
  have hu := summable_ErCoeff hr
  have hb : ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (-1:ℝ) 1 →
      ‖ErCoeff r n * x^(2*n+1)‖ ≤ ErCoeff r n := by
    intro n x hx
    have hx1 : |x| ≤ 1 := by rw [abs_le]; exact ⟨hx.1, hx.2⟩
    have hlt : |x|^(2*n+1) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (ErCoeff_nonneg hr n)]
    calc ErCoeff r n * |x|^(2*n+1) ≤ ErCoeff r n * 1 :=
          mul_le_mul_of_nonneg_left hlt (ErCoeff_nonneg hr n)
      _ = ErCoeff r n := by ring
  have hunif := tendstoUniformlyOn_tsum hu hb
  have hcont : ∀ (s : Finset ℕ), ContinuousOn
      (fun t : ℝ => ∑ k ∈ s, ErCoeff r k * t^(2*k+1)) (Set.Icc (-1:ℝ) 1) := by
    intro s
    have hc : Continuous (fun t : ℝ => ∑ k ∈ s, ErCoeff r k * t^(2*k+1)) := by
      apply continuous_finset_sum
      intro k _
      fun_prop
    exact hc.continuousOn
  exact hunif.continuousOn (Eventually.of_forall hcont).frequently

lemma Er_mono {r : ℕ} (hr : 1 ≤ r) {s t : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hst : s ≤ t) : Er r s ≤ Er r t := by
  have hsum : Summable (fun k : ℕ => ErCoeff r k * t^(2*k+1)) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (summable_ErCoeff hr)
    · exact mul_nonneg (ErCoeff_nonneg hr k) (pow_nonneg ht.1 _)
    · calc ErCoeff r k * t^(2*k+1) ≤ ErCoeff r k * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1 (by linarith [ht.2]))
              (ErCoeff_nonneg hr k)
        _ = ErCoeff r k := by ring
  have hsum_s : Summable (fun k : ℕ => ErCoeff r k * s^(2*k+1)) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (summable_ErCoeff hr)
    · exact mul_nonneg (ErCoeff_nonneg hr k) (pow_nonneg hs.1 _)
    · calc ErCoeff r k * s^(2*k+1) ≤ ErCoeff r k * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hs.1 (by linarith [hs.2]))
              (ErCoeff_nonneg hr k)
        _ = ErCoeff r k := by ring
  have hle : ∀ k, ErCoeff r k * s^(2*k+1) ≤ ErCoeff r k * t^(2*k+1) := by
    intro k
    apply mul_le_mul_of_nonneg_left _ (ErCoeff_nonneg hr k)
    apply pow_le_pow_left₀ hs.1 hst
  rw [Er, Er]
  exact Summable.tsum_le_tsum hle hsum_s hsum

lemma Er_mono_summable {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Summable (fun k : ℕ => ErCoeff r k * t^(2*k+1)) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (summable_ErCoeff hr)
  · exact mul_nonneg (ErCoeff_nonneg hr k) (pow_nonneg h0 _)
  · calc ErCoeff r k * t^(2*k+1) ≤ ErCoeff r k * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ h0 h1) (ErCoeff_nonneg hr k)
      _ = ErCoeff r k := by ring

lemma pow_sub_pow_nonneg {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (m : ℕ) :
    0 ≤ t^(2*m+1) - s^(2*m+1) :=
  sub_nonneg.mpr (pow_le_pow_left₀ hs hst _)

theorem Er_strictMono {r : ℕ} (hr : 1 ≤ r) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (ht : t ≤ 1) : Er r s < Er r t := by
  have hstle : s ≤ t := le_of_lt hst
  have hs1 : s ≤ 1 := le_trans hstle ht
  -- summability of the difference series
  have ht0 : (0:ℝ) ≤ t := le_trans hs hstle
  have hdiff : Summable (fun k : ℕ => ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)) :=
    (Er_mono_summable hr ht0 ht).sub (Er_mono_summable hr hs hs1)
  have hnonneg : ∀ k, 0 ≤ (ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)) := by
    intro k
    have h := pow_sub_pow_nonneg hs hstle k
    have h2 : ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)
        = ErCoeff r k * (t^(2*k+1) - s^(2*k+1)) := by ring
    rw [h2]
    exact mul_nonneg (ErCoeff_nonneg hr k) h
  have hpos0 : 0 < ErCoeff r 0 * t^(2*0+1) - ErCoeff r 0 * s^(2*0+1) := by
    have hC : 0 < Cr r := Cr_pos hr
    have hE0 : ErCoeff r 0 = Cr r := by
      unfold ErCoeff
      norm_num [risingFact]
    have hE : 0 < ErCoeff r 0 := by rw [hE0]; exact hC
    have hpow : ∀ x : ℝ, x^(2*0+1) = x := by intro x; norm_num
    have : ErCoeff r 0 * t^(2*0+1) - ErCoeff r 0 * s^(2*0+1) = ErCoeff r 0 * (t - s) := by
      rw [hpow t, hpow s]; ring
    rw [this]
    exact mul_pos hE (sub_pos.mpr hst)
  have htsum : 0 < ∑' k : ℕ, (ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)) :=
    hdiff.tsum_pos hnonneg 0 hpos0
  have hsplit : (∑' k : ℕ, (ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)))
      = Er r t - Er r s := by
    show (∑' k : ℕ, (ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)))
        = (∑' k : ℕ, ErCoeff r k * t^(2*k+1)) - (∑' k : ℕ, ErCoeff r k * s^(2*k+1))
    rw [Summable.tsum_sub (Er_mono_summable hr ht0 ht) (Er_mono_summable hr hs hs1)]
  rw [hsplit] at htsum
  linarith

lemma summable_Er_abs {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht : |t| ≤ 1) :
    Summable (fun k : ℕ => ErCoeff r k * t^(2*k+1)) := by
  have hb : ∀ k : ℕ, ‖ErCoeff r k * t^(2*k+1)‖ ≤ ErCoeff r k := by
    intro k
    have h1 : |t|^(2*k+1) ≤ 1 := (pow_le_one₀ (abs_nonneg t) ht : |t|^(2*k+1) ≤ 1)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (ErCoeff_nonneg hr k)]
    calc ErCoeff r k * |t|^(2*k+1) ≤ ErCoeff r k * 1 :=
          mul_le_mul_of_nonneg_left h1 (ErCoeff_nonneg hr k)
      _ = ErCoeff r k := by ring
  exact Summable.of_norm_bounded (summable_ErCoeff hr) hb

lemma neg_pow_odd (t : ℝ) (k : ℕ) : (-t)^(2*k+1) = -(t^(2*k+1)) := by
  rw [neg_pow]
  have h1 : (-1:ℝ)^(2*k+1) = -1 := by
    rw [show 2*k+1 = 2*k + 1 by ring, pow_succ, Even.neg_one_pow ⟨k, by ring⟩]
    ring
  rw [h1]
  ring

theorem Er_neg {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht : |t| ≤ 1) : Er r (-t) = -Er r t := by
  have hcongr : (fun k : ℕ => ErCoeff r k * (-t)^(2*k+1))
      = fun k : ℕ => -(ErCoeff r k * t^(2*k+1)) := by
    funext k
    rw [neg_pow_odd t k]
    ring
  rw [Er, hcongr, tsum_neg]
  rfl

theorem Er_injOn_Icc {r : ℕ} (hr : 1 ≤ r) : Set.InjOn (Er r) (Set.Icc (0:ℝ) 1) := by
  intro s hs t ht h
  rcases lt_trichotomy s t with hlt | heq | hgt
  · exact absurd h (ne_of_lt (Er_strictMono hr hs.1 hlt ht.2))
  · exact heq
  · exact absurd h.symm (ne_of_lt (Er_strictMono hr ht.1 hgt hs.2))

theorem Er_one_one : Er 1 1 = 1 := by
  have h := Er_one_arcsin (t := 1) (Set.mem_Icc.mpr ⟨by norm_num, le_rfl⟩)
  have harc : Real.arcsin 1 = Real.pi / 2 := Real.arcsin_eq_pi_div_two.mpr le_rfl
  rw [harc] at h
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  rw [h]
  field_simp

theorem Er_one_maps (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    Er 1 t ∈ Set.Icc (-1:ℝ) 1 :=
  Set.mem_Icc.mpr ⟨neg_le_of_abs_le (abs_Er_one_le_one ht), le_of_abs_le (abs_Er_one_le_one ht)⟩

end Grothendieck

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

noncomputable def e1v : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![1, 0]

noncomputable def tv (τ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![τ, Real.sqrt (1 - τ ^ 2)]

theorem norm_e1v : ‖e1v‖ = 1 := by
  simp [e1v, EuclideanSpace.norm_eq, Fin.sum_univ_two]

theorem norm_tv {τ : ℝ} (hτ : |τ| < 1) : ‖tv τ‖ = 1 := by
  have h1 : (0:ℝ) ≤ 1 - τ ^ 2 := by
    have := abs_lt.mp hτ
    nlinarith
  simp [tv, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sq_sqrt h1]

theorem inner_e1v_tv {τ : ℝ} : inner ℝ e1v (tv τ) = τ := by
  simp [e1v, tv, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]

theorem reducedExpectation_eq_Er_one_proof {τ : ℝ} (hτ : |τ| < 1) :
    (∫ W, reducedIntegrand 1 W ∂(reducedLaw 1 τ)) = Er 1 τ := by
  have hmem : τ ∈ Set.Icc (-1 : ℝ) 1 := by
    have := abs_lt.mp hτ
    exact ⟨le_of_lt this.1, le_of_lt this.2⟩
  -- the bridge, read backwards, at the explicit pair `(e₁, tv τ)`
  have hbridge := grothendieckExpectation_eq_reduced (r := 1) (n := 2) e1v (tv τ)
    norm_e1v (norm_tv hτ)
  rw [inner_e1v_tv] at hbridge
  rw [← hbridge]
  -- and the published arcsine law
  rw [Leaf2.grothendieckExpectation_one (n := 2) e1v (tv τ) norm_e1v (norm_tv hτ), inner_e1v_tv]
  rw [Er_one_arcsin hmem]

end Grothendieck

open MeasureTheory in
theorem solution {τ : ℝ} (hτ : |τ| < 1) :
    (∫ W, Grothendieck.reducedIntegrand 1 W ∂(Grothendieck.reducedLaw 1 τ)) = Grothendieck.Er 1 τ :=
  Grothendieck.reducedExpectation_eq_Er_one_proof hτ
