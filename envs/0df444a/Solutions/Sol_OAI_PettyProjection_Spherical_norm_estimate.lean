-- Prove2me | solution 1 for OAI.PettyProjection.Spherical.norm_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:10:52.534039+00:00
-- url     : https://prove2.me/submissions/e149de4f-a755-4450-8da9-ecdd8eea3c26

import Mathlib
import Definitions.Def_PettyProjectionVolume
import Definitions.Def_OAIQWPP000

section
-- module Solutions.OAIQW_PettyProjection.SphericalCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal RealInnerProductSpace Pointwise

namespace PettyProjection.Spherical

lemma mean_const (n : ℕ) [NeZero n] (c : ℝ) : mean (fun _ : Sphere n => c) = c := by
  simp [mean]

lemma sum_coordinateProduct (n : ℕ) :
    ∑ i : Fin n, coordinateProduct n i i = ContinuousMap.const (Sphere n) 1 := by
  ext u
  have h := EuclideanSpace.real_norm_sq_eq (u : Space n)
  rw [norm_coe, one_pow] at h
  simpa [coordinateProduct, sq] using h.symm

lemma constant_mem_lowSpace (n : ℕ) [NeZero n] (c : ℝ) :
    toH n (ContinuousMap.const (Sphere n) c) ∈ lowSpace n := by
  have h1 : toH n (ContinuousMap.const (Sphere n) 1) ∈ lowSpace n := by
    rw [← sum_coordinateProduct, map_sum]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.subset_span ⟨(i, i), rfl⟩
  have hf : ContinuousMap.const (Sphere n) c =
      c • ContinuousMap.const (Sphere n) (1 : ℝ) := by ext; simp
  rw [hf, map_smul]
  exact (lowSpace n).smul_mem c h1

lemma Q_eq_sub (n : ℕ) [NeZero n] (f : H n) :
    Q n f = f - (lowSpace n).starProjection f :=
  Submodule.starProjection_orthogonal_val f

lemma Q_constant (n : ℕ) [NeZero n] (c : ℝ) :
    Q n (toH n (ContinuousMap.const (Sphere n) c)) = 0 := by
  rw [Q_eq_sub, Submodule.starProjection_eq_self_iff.mpr (constant_mem_lowSpace n c),
    sub_self]

lemma norm_Q_le (n : ℕ) [NeZero n] (f : H n) : ‖Q n f‖ ≤ ‖f‖ :=
  (lowSpace n)ᗮ.norm_starProjection_apply_le f

lemma inner_toH (n : ℕ) [NeZero n] (f g : C(Sphere n, ℝ)) :
    ⟪toH n f, toH n g⟫ = mean (fun u => f u * g u) := by
  simpa [toH, mean, mul_comm] using ContinuousMap.inner_toLp (sigma n) f g

lemma norm_toH_sq (n : ℕ) [NeZero n] (f : C(Sphere n, ℝ)) :
    ‖toH n f‖ ^ 2 = mean (fun u => (f u) ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, inner_toH]
  simp [sq]

lemma norm_Q_le_centered (n : ℕ) [NeZero n] (f : C(Sphere n, ℝ)) (c : ℝ) :
    ‖Q n (toH n f)‖ ^ 2 ≤ mean (fun u => (f u - c) ^ 2) := by
  have h := norm_Q_le n (toH n (f - ContinuousMap.const (Sphere n) c))
  have hQ : Q n (toH n (f - ContinuousMap.const (Sphere n) c)) = Q n (toH n f) := by
    simp only [map_sub, Q_constant, sub_zero]
  rw [hQ] at h
  have hh := (sq_le_sq₀ (norm_nonneg (Q n (toH n f)))
    (norm_nonneg (toH n (f - ContinuousMap.const (Sphere n) c)))).mpr h
  simpa only [norm_toH_sq, ContinuousMap.sub_apply, ContinuousMap.const_apply] using hh

attribute [local instance] OAI.PettyProjection.Spherical.instCompleteSpaceContinuousLinearMapRealIdSpace
attribute [local instance] OAI.PettyProjection.Spherical.instNormedAlgebraRatContinuousLinearMapRealIdSpace
lemma rotation_apply {n : ℕ} (T : Space n →L[ℝ] Space n) (hT : star T = -T)
    (t : ℝ) (x : Space n) : rotation T hT t x = NormedSpace.exp (t • T) x := rfl

lemma rotation_zero {n : ℕ} (T : Space n →L[ℝ] Space n) (hT : star T = -T)
    (x : Space n) : rotation T hT 0 x = x := by
  rw [rotation_apply]
  have hz : (0 : ℝ) • T = 0 := zero_smul ℝ T
  rw [hz, NormedSpace.exp_zero]
  rfl

lemma hasDerivAt_rotation {n : ℕ} (T : Space n →L[ℝ] Space n) (hT : star T = -T)
    (t : ℝ) (x : Space n) :
    HasDerivAt (fun s => rotation T hT s x) (T (rotation T hT t x)) t := by
  simpa only [mul_apply_eq_comp, map_zero, add_zero, rotation_apply] using
    (hasDerivAt_exp_smul_const' T t).clm_apply (hasDerivAt_const t x)

/-- Infinitesimal rotation invariance, with differentiation justified using
uniform derivative bounds on the compact sphere. This supplies spherical
integration by parts without postulating it as an interface. -/
lemma mean_fderiv_skew {n : ℕ} [NeZero n] (T : Space n →L[ℝ] Space n)
    (hT : star T = -T) (f : Space n → ℝ) (hf : ContDiff ℝ 1 f) :
    mean (fun u : Sphere n => fderiv ℝ f u (T u)) = 0 := by
  let df : C(Sphere n, Space n →L[ℝ] ℝ) :=
    ⟨fun u => fderiv ℝ f u, (hf.continuous_fderiv (by norm_num)).comp continuous_subtype_val⟩
  let F : ℝ → Sphere n → ℝ := fun t u => f (rotation T hT t u)
  let F' : ℝ → Sphere n → ℝ :=
    fun t u => fderiv ℝ f (rotation T hT t u) (T (rotation T hT t u))
  have hFc (t : ℝ) : Continuous (F t) :=
    hf.continuous.comp ((rotation T hT t).continuous.comp continuous_subtype_val)
  have hF'c (t : ℝ) : Continuous (F' t) := by
    exact ((hf.continuous_fderiv (by norm_num)).comp
      ((rotation T hT t).continuous.comp continuous_subtype_val)).clm_apply
      (T.continuous.comp ((rotation T hT t).continuous.comp continuous_subtype_val))
  have hbound (t : ℝ) (u : Sphere n) : ‖F' t u‖ ≤ ‖df‖ * ‖T‖ := by
    let v : Sphere n := sphereMap (rotation T hT t) u
    calc
      ‖F' t u‖ ≤ ‖fderiv ℝ f v‖ * ‖T v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖df‖ * (‖T‖ * ‖(v : Space n)‖) :=
        mul_le_mul (ContinuousMap.norm_coe_le_norm df v)
          (T.le_opNorm v) (norm_nonneg _) (norm_nonneg df)
      _ = ‖df‖ * ‖T‖ := by rw [norm_coe, mul_one]
  have hderiv (t : ℝ) (u : Sphere n) : HasDerivAt (fun s => F s u) (F' t u) t := by
    exact (hf.differentiable (by norm_num) (rotation T hT t u)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_rotation T hT t u)
  have hI := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sigma n) (x₀ := (0 : ℝ)) (s := univ) (F := F) (F' := F')
    (bound := fun _ => ‖df‖ * ‖T‖) (Filter.univ_mem)
    (Filter.Eventually.of_forall fun t => (hFc t).aestronglyMeasurable)
    (continuous_integrable (hFc 0)) (hF'c 0).aestronglyMeasurable
    (ae_of_all _ fun u t _ => hbound t u) (integrable_const _)
    (ae_of_all _ fun u t _ => hderiv t u)
  have hconst : (fun t => ∫ u, F t u ∂sigma n) = fun _ : ℝ => mean (fun u : Sphere n => f u) := by
    funext t
    exact mean_rotation (rotation T hT t) (fun u : Sphere n => f u)
  rw [hconst] at hI
  have hz := hI.2.unique (hasDerivAt_const (0 : ℝ) (mean (fun u : Sphere n => f u)))
  simpa only [F', rotation_zero, mean] using hz

lemma rotDeriv_mul {n : ℕ} (T : Space n →L[ℝ] Space n)
    {f g : Space n → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : Space n) :
    rotDeriv T (fun y => f y * g y) x =
      f x * rotDeriv T g x + g x * rotDeriv T f x := by
  simp only [rotDeriv, fderiv_fun_mul (hf x) (hg x), add_apply,
    smul_apply, smul_eq_mul]

/-- Genuine spherical integration by parts for each rotation generator. -/
lemma mean_rotDeriv_mul {n : ℕ} [NeZero n] (T : Space n →L[ℝ] Space n)
    (hT : star T = -T) {f g : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    mean (fun u : Sphere n => f u * rotDeriv T g u) =
      - mean (fun u : Sphere n => g u * rotDeriv T f u) := by
  have h := mean_fderiv_skew T hT (fun x => f x * g x) (hf.mul hg)
  change mean (fun u : Sphere n => rotDeriv T (fun x => f x * g x) u) = 0 at h
  simp_rw [rotDeriv_mul T (hf.differentiable (by norm_num))
    (hg.differentiable (by norm_num))] at h
  have hi₁ := continuous_integrable
    ((hf.continuous.comp continuous_subtype_val).mul
      ((continuous_rotDeriv T hg).comp continuous_subtype_val))
  have hi₂ := continuous_integrable
    ((hg.continuous.comp continuous_subtype_val).mul
      ((continuous_rotDeriv T hf).comp continuous_subtype_val))
  change Integrable (fun u : Sphere n => f u * rotDeriv T g u) (sigma n) at hi₁
  change Integrable (fun u : Sphere n => g u * rotDeriv T f u) (sigma n) at hi₂
  rw [mean, integral_add hi₁ hi₂] at h
  exact eq_neg_of_add_eq_zero_left h

lemma generator_skew (n : ℕ) (i j : Fin n) :
    star (generator n i j) = -generator n i j := by
  simp only [generator, ContinuousLinearMap.star_eq_adjoint, map_sub,
    InnerProductSpace.adjoint_rankOne, neg_sub]

lemma generator_apply {n : ℕ} (i j : Fin n) (x : Space n) :
    generator n i j x = x i • EuclideanSpace.single j 1 - x j • EuclideanSpace.single i 1 := by
  simp [generator, EuclideanSpace.inner_single_left]

lemma generator_apply_coord {n : ℕ} (i j a : Fin n) (x : Space n) :
    (generator n i j x) a = x i * (if j = a then 1 else 0) -
      x j * (if i = a then 1 else 0) := by
  simp [generator_apply, PiLp.single_apply, eq_comm]

lemma energy_symm {n : ℕ} (f g : Space n → ℝ) : energy f g = energy g f := by
  simp only [energy, mul_comm]

lemma energy_nonneg {n : ℕ} (f : Space n → ℝ) : 0 ≤ energy f f := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact integral_nonneg fun _ => mul_self_nonneg _

lemma mean_sum {n : ℕ} [NeZero n] {ι : Type uι} (s : Finset ι)
    {f : ι → Sphere n → ℝ} (hf : ∀ i ∈ s, Continuous (f i)) :
    mean (fun u => ∑ i ∈ s, f i u) = ∑ i ∈ s, mean (f i) := by
  exact integral_finsetSum s fun i hi => continuous_integrable (hf i hi)

lemma mean_casimir {n : ℕ} [NeZero n] {f g : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g) :
    mean (fun u : Sphere n => f u * casimir g u) = -energy f g := by
  have hc (i j : Fin n) : Continuous (fun u : Sphere n =>
      f u * rotDeriv (generator n i j) (rotDeriv (generator n i j) g) u) :=
    (hf.continuous.comp continuous_subtype_val).mul
      ((continuous_rotDeriv _ (contDiff_rotDeriv _ hg)).comp continuous_subtype_val)
  have heq : (fun u : Sphere n => f u * casimir g u) =
      fun u : Sphere n => (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
        f u * rotDeriv (generator n i j) (rotDeriv (generator n i j) g) u := by
    funext u
    simp only [casimir, mul_left_comm (f u) (1 / 2 : ℝ), Finset.mul_sum]
  rw [heq, mean, integral_const_mul]
  change (1 / 2 : ℝ) * mean (fun u : Sphere n => ∑ i : Fin n, ∑ j : Fin n,
      f u * rotDeriv (generator n i j) (rotDeriv (generator n i j) g) u) = _
  rw [mean_sum _ (fun i _ => continuous_finsetSum _ fun j _ => hc i j)]
  rw [show -energy f g = (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
      -mean (fun u : Sphere n => rotDeriv (generator n i j) f u *
        rotDeriv (generator n i j) g u) by
    simp [energy, Finset.sum_neg_distrib]]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mean_sum _ (fun j _ => hc i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [mean_rotDeriv_mul _ (generator_skew n i j) hf (contDiff_rotDeriv _ hg)]
  simp only [mul_comm]

lemma rotDeriv_add {n : ℕ} (T : Space n →L[ℝ] Space n)
    {f g : Space n → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : Space n) :
    rotDeriv T (fun y => f y + g y) x = rotDeriv T f x + rotDeriv T g x := by
  simp only [rotDeriv, fderiv_fun_add (hf x) (hg x), add_apply]

lemma rotDeriv_const {n : ℕ} (T : Space n →L[ℝ] Space n) (c : ℝ) (x : Space n) :
    rotDeriv T (fun _ => c) x = 0 := by
  simp [rotDeriv]

lemma rotDeriv_coordinate {n : ℕ} (i j a : Fin n) (x : Space n) :
    rotDeriv (generator n i j) (fun y => y a) x =
      x i * (if j = a then 1 else 0) - x j * (if i = a then 1 else 0) := by
  change fderiv ℝ (EuclideanSpace.proj a) x (generator n i j x) = _
  rw [ContinuousLinearMap.fderiv]
  exact generator_apply_coord i j a x

lemma polynomialRotation_add {n : ℕ} (i j : Fin n) (p q : MvPolynomial (Fin n) ℝ) :
    polynomialRotation i j (p + q) = polynomialRotation i j p + polynomialRotation i j q := by
  simp only [polynomialRotation, map_add]
  ring

lemma polynomialRotation_mul {n : ℕ} (i j : Fin n) (p q : MvPolynomial (Fin n) ℝ) :
    polynomialRotation i j (p * q) =
      p * polynomialRotation i j q + q * polynomialRotation i j p := by
  simp only [polynomialRotation, MvPolynomial.pderiv_mul]
  ring

lemma polynomialRotation_C {n : ℕ} (i j : Fin n) (c : ℝ) :
    polynomialRotation i j (MvPolynomial.C c) = 0 := by
  simp [polynomialRotation]

lemma polynomialFunction_add {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) :
    polynomialFunction (p + q) = fun x => polynomialFunction p x + polynomialFunction q x := by
  funext x
  exact MvPolynomial.eval_add

lemma polynomialFunction_mul {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) :
    polynomialFunction (p * q) = fun x => polynomialFunction p x * polynomialFunction q x := by
  funext x
  exact MvPolynomial.eval_mul

lemma polynomialFunction_X {n : ℕ} (i : Fin n) :
    polynomialFunction (MvPolynomial.X i) = fun x : Space n => x i := by
  funext x
  exact MvPolynomial.eval_X _

lemma polynomialFunction_C {n : ℕ} (c : ℝ) :
    polynomialFunction (MvPolynomial.C c : MvPolynomial (Fin n) ℝ) = fun _ => c := by
  funext x
  exact MvPolynomial.eval_C _

/-- The formal polynomial generator agrees with actual differentiation. -/
lemma rotDeriv_polynomialFunction {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    rotDeriv (generator n i j) (polynomialFunction p) =
      polynomialFunction (polynomialRotation i j p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [polynomialFunction_C, polynomialRotation_C]
    funext x
    simp [rotDeriv_const, polynomialFunction]
  | add p q hp hq =>
    rw [polynomialFunction_add, polynomialRotation_add, polynomialFunction_add]
    funext x
    rw [rotDeriv_add _ ((polynomialFunction_contDiff p).differentiable (by norm_num))
      ((polynomialFunction_contDiff q).differentiable (by norm_num)), hp, hq]
  | mul_X p a hp =>
    rw [polynomialFunction_mul, polynomialRotation_mul, polynomialFunction_add,
      polynomialFunction_mul, polynomialFunction_mul]
    funext x
    rw [rotDeriv_mul _ ((polynomialFunction_contDiff p).differentiable (by norm_num))
      ((polynomialFunction_contDiff (MvPolynomial.X a)).differentiable (by norm_num)), hp]
    congr 1
    rw [polynomialFunction_X, rotDeriv_coordinate]
    by_cases hia : i = a <;> by_cases hja : j = a <;>
      simp [polynomialFunction, polynomialRotation, hia, hja, eq_comm]

open MvPolynomial

lemma polynomialRotation_twice {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    polynomialRotation i j (polynomialRotation i j p) =
      X i ^ 2 * pderiv j (pderiv j p) + X j ^ 2 * pderiv i (pderiv i p) -
      X i * X j * pderiv j (pderiv i p) - X i * X j * pderiv i (pderiv j p) -
      X i * pderiv i p - X j * pderiv j p +
      (if i = j then 2 * (X i * pderiv i p) else 0) := by
  by_cases h : i = j
  · subst j
    simp only [polynomialRotation, sub_self, map_zero, mul_zero, ite_true]
    ring
  · simp only [polynomialRotation, map_sub, MvPolynomial.pderiv_mul,
      pderiv_X, Pi.single_apply, h, Ne.symm h, ite_false, ite_true, one_mul, zero_mul]
    ring

lemma eulerPolynomial_twice {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    eulerPolynomial (eulerPolynomial p) = eulerPolynomial p +
      ∑ i : Fin n, ∑ j : Fin n, X i * X j * pderiv i (pderiv j p) := by
  have h (i : Fin n) : (∑ j : Fin n, X i *
      (pderiv i (X j) * pderiv j p + X j * pderiv i (pderiv j p))) =
      X i * pderiv i p + ∑ j : Fin n, X i * X j * pderiv i (pderiv j p) := by
    simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib]
    congr 1
    simp [pderiv_X, Pi.single_apply, eq_comm]
  simp only [eulerPolynomial, map_sum, MvPolynomial.pderiv_mul, Finset.mul_sum]
  simp_rw [h, Finset.sum_add_distrib]

lemma sum_polynomialRotation_twice {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, polynomialRotation i j (polynomialRotation i j p) =
      2 * (radiusPolynomial n * laplacePolynomial p) -
      2 * eulerPolynomial (eulerPolynomial p) -
      2 * ((n : MvPolynomial (Fin n) ℝ) - 2) * eulerPolynomial p := by
  have hA : (∑ i : Fin n, ∑ j : Fin n, X i ^ 2 * pderiv j (pderiv j p)) =
      radiusPolynomial n * laplacePolynomial p := by
    rw [radiusPolynomial, laplacePolynomial, Finset.sum_mul]
    simp only [Finset.mul_sum]
  have hB : (∑ i : Fin n, ∑ j : Fin n, X j ^ 2 * pderiv i (pderiv i p)) =
      radiusPolynomial n * laplacePolynomial p := by
    rw [Finset.sum_comm]
    exact hA
  have hC : (∑ i : Fin n, ∑ j : Fin n, X i * X j * pderiv j (pderiv i p)) =
      ∑ i : Fin n, ∑ j : Fin n, X i * X j * pderiv i (pderiv j p) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (X j) (X i)]
  have hD : (∑ i : Fin n, ∑ j : Fin n, X i * pderiv i p) =
      (n : MvPolynomial (Fin n) ℝ) * eulerPolynomial p := by
    simp [eulerPolynomial, nsmul_eq_mul, Finset.mul_sum]
  have hE : (∑ i : Fin n, ∑ j : Fin n, X j * pderiv j p) =
      (n : MvPolynomial (Fin n) ℝ) * eulerPolynomial p := by
    rw [Finset.sum_comm]
    exact hD
  have hF : (∑ i : Fin n, ∑ j : Fin n,
      if i = j then 2 * (X i * pderiv i p) else 0) = 2 * eulerPolynomial p := by
    simp [eulerPolynomial, Finset.mul_sum]
  simp only [polynomialRotation_twice, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hA, hB, hC, hD, hE, hF, eulerPolynomial_twice]
  ring

lemma eulerPolynomial_nsmul {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    eulerPolynomial (d • p) = d • eulerPolynomial p := by
  simp only [eulerPolynomial, map_nsmul]
  simp only [nsmul_eq_mul]
  simp_rw [mul_left_comm (X _) (d : MvPolynomial (Fin n) ℝ)]
  rw [← Finset.mul_sum]

lemma eulerPolynomial_homogeneous {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) : eulerPolynomial p = d • p :=
  hp.sum_X_mul_pderiv

lemma sum_polynomialRotation_homogeneous {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) :
    ∑ i : Fin n, ∑ j : Fin n, polynomialRotation i j (polynomialRotation i j p) =
      2 * (radiusPolynomial n * laplacePolynomial p - C (eigenvalue n d) * p) := by
  have he := eulerPolynomial_homogeneous hp
  have hee : eulerPolynomial (eulerPolynomial p) = d • (d • p) := by
    rw [he, eulerPolynomial_nsmul, he]
  rw [sum_polynomialRotation_twice, hee, he]
  simp only [nsmul_eq_mul, eigenvalue, map_mul, map_sub, map_add, map_natCast, map_ofNat]
  ring

lemma polynomialFunction_radius {n : ℕ} (x : Space n) :
    polynomialFunction (radiusPolynomial n) x = ‖x‖ ^ 2 := by
  unfold polynomialFunction radiusPolynomial
  simp only [map_sum, map_pow, eval_X]
  exact (EuclideanSpace.real_norm_sq_eq x).symm

/-- Polar Laplacian identity, derived from finite rotation sums and Euler's
identity rather than assumed as a spherical calculus interface. -/
lemma casimir_polynomialFunction {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (x : Space n) :
    casimir (polynomialFunction p) x =
      ‖x‖ ^ 2 * polynomialFunction (laplacePolynomial p) x -
        eigenvalue n d * polynomialFunction p x := by
  have hs := congrArg (MvPolynomial.eval (fun i => x i))
    (sum_polynomialRotation_homogeneous hp)
  simp only [map_sum, map_mul, map_sub, eval_C, map_ofNat] at hs
  simp only [casimir, rotDeriv_polynomialFunction, polynomialFunction]
  rw [hs]
  have hr := polynomialFunction_radius x
  unfold polynomialFunction at hr
  rw [hr]
  ring

lemma casimir_harmonic {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (hΔp : laplacePolynomial p = 0) (x : Space n) :
    casimir (polynomialFunction p) x = -eigenvalue n d * polynomialFunction p x := by
  rw [casimir_polynomialFunction hp, hΔp]
  simp [polynomialFunction]

lemma eigenvalue_strictMono {n : ℕ} (hn : 2 ≤ n) : StrictMono (eigenvalue n) := by
  intro d e hde
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hde' : (d : ℝ) < e := by exact_mod_cast hde
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  unfold eigenvalue
  nlinarith

/-- Distinct homogeneous harmonic degrees are orthogonal under actual
normalized surface measure. -/
lemma harmonic_orthogonal {n d e : ℕ} (hn : 2 ≤ n)
    {p q : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous e)
    (hΔp : laplacePolynomial p = 0) (hΔq : laplacePolynomial q = 0) (hde : d ≠ e) :
    mean (fun u : Sphere n => polynomialFunction p u * polynomialFunction q u) = 0 := by
  have : NeZero n := ⟨by omega⟩
  have h₁ := mean_casimir (f := polynomialFunction p) (g := polynomialFunction q)
    ((polynomialFunction_contDiff p).of_le le_top) ((polynomialFunction_contDiff q).of_le le_top)
  have h₂ := mean_casimir (f := polynomialFunction q) (g := polynomialFunction p)
    ((polynomialFunction_contDiff q).of_le le_top) ((polynomialFunction_contDiff p).of_le le_top)
  simp_rw [casimir_harmonic hq hΔq, mul_left_comm (polynomialFunction p _) (-eigenvalue n e)] at h₁
  simp_rw [casimir_harmonic hp hΔp, mul_left_comm (polynomialFunction q _) (-eigenvalue n d),
    mul_comm (polynomialFunction q _) (polynomialFunction p _)] at h₂
  rw [mean, integral_const_mul] at h₁ h₂
  rw [energy_symm (polynomialFunction q) (polynomialFunction p)] at h₂
  have hne : eigenvalue n d ≠ eigenvalue n e := (eigenvalue_strictMono hn).injective.ne hde
  unfold mean
  have hz : (eigenvalue n d - eigenvalue n e) *
      (∫ u : Sphere n, polynomialFunction p u * polynomialFunction q u ∂sigma n) = 0 := by
    nlinarith [h₁, h₂]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

lemma laplacePolynomial_sub {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) :
    laplacePolynomial (p - q) = laplacePolynomial p - laplacePolynomial q := by
  simp [laplacePolynomial, Finset.sum_sub_distrib]

lemma laplacePolynomial_homogeneous {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) : (laplacePolynomial p).IsHomogeneous (d - 2) := by
  apply IsHomogeneous.sum
  intro i _
  convert hp.pderiv.pderiv using 1
  omega

lemma pderiv_radiusPolynomial {n : ℕ} (i : Fin n) :
    pderiv i (radiusPolynomial n) = 2 * X i := by
  simp [radiusPolynomial, pderiv_X, Pi.single_apply, eq_comm]

lemma radiusPolynomial_homogeneous (n : ℕ) : (radiusPolynomial n).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_X_pow i 2

lemma laplacePolynomial_radius_mul {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    laplacePolynomial (radiusPolynomial n * p) =
      radiusPolynomial n * laplacePolynomial p + 4 * eulerPolynomial p + 2 * n * p := by
  have hd (i : Fin n) : pderiv i (pderiv i (radiusPolynomial n * p)) =
      radiusPolynomial n * pderiv i (pderiv i p) + 4 * (X i * pderiv i p) + 2 * p := by
    simp only [pderiv_mul, pderiv_radiusPolynomial, map_add, pderiv_X_self]
    have htwo : pderiv i (2 : MvPolynomial (Fin n) ℝ) = 0 := (pderiv i).map_natCast 2
    rw [htwo]
    ring
  simp only [laplacePolynomial, hd, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, eulerPolynomial]
  ring

lemma laplacePolynomial_radius_mul_homogeneous {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) :
    laplacePolynomial (radiusPolynomial n * p) =
      radiusPolynomial n * laplacePolynomial p + C (4 * (d : ℝ) + 2 * n) * p := by
  rw [laplacePolynomial_radius_mul, eulerPolynomial_homogeneous hp]
  simp only [nsmul_eq_mul, map_add, map_mul, map_ofNat, map_natCast]
  ring

lemma radialCoefficient_pos {n : ℕ} (hn : 2 ≤ n) (l j : ℕ) :
    0 < radialCoefficient n l j := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  unfold radialCoefficient
  push_cast
  apply mul_pos (by positivity)
  linarith

lemma radius_pow_mul_homogeneous {n l : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous l) (j : ℕ) :
    ((radiusPolynomial n) ^ j * p).IsHomogeneous (2 * j + l) :=
  ((radiusPolynomial_homogeneous n).pow j).mul hp

lemma laplacePolynomial_radial_harmonic {n l : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous l) (hΔp : laplacePolynomial p = 0) (j : ℕ) :
    laplacePolynomial (radiusPolynomial n ^ (j + 1) * p) =
      C (radialCoefficient n l j) * (radiusPolynomial n ^ j * p) := by
  have hr (a : ℕ) : radiusPolynomial n ^ (a + 1) * p =
      radiusPolynomial n * (radiusPolynomial n ^ a * p) := by rw [pow_succ']; ring
  induction j with
  | zero =>
      simp only [Nat.zero_add, pow_one, pow_zero, one_mul]
      rw [laplacePolynomial_radius_mul_homogeneous hp, hΔp, mul_zero, zero_add]
      congr 2
      simp only [radialCoefficient]
      ring
  | succ j ih =>
      rw [hr (j + 1), laplacePolynomial_radius_mul_homogeneous (radius_pow_mul_homogeneous hp (j + 1)), ih]
      rw [hr j]
      simp only [radialCoefficient, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        map_mul, map_add, map_sub, map_ofNat, map_natCast]
      ring

lemma laplacePolynomial_eq_zero_small {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (hd : d < 2) : laplacePolynomial p = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have h₀ : (pderiv i p).IsHomogeneous 0 := by
    convert hp.pderiv using 1
    omega
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h₀
  rw [h₀, pderiv_C]

lemma fischerSpan_le_homogeneous (n d : ℕ) :
    fischerSpan n d ≤ homogeneousSubmodule (Fin n) ℝ d := by
  apply Submodule.span_le.mpr
  rintro q ⟨j, l, p, hd, hp, _, rfl⟩
  exact hd ▸ radius_pow_mul_homogeneous hp j

lemma harmonic_mem_fischerSpan {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (hΔp : laplacePolynomial p = 0) : p ∈ fischerSpan n d := by
  exact Submodule.subset_span ⟨0, d, p, by omega, hp, hΔp, by simp⟩

lemma fischerSpan_laplace_preimage {n d : ℕ} (hn : 2 ≤ n) {p : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ fischerSpan n d) :
    ∃ q ∈ fischerSpan n (d + 2), laplacePolynomial q = p := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, l, p, hd, hhom, hΔ, rfl⟩ := hx
      refine ⟨(radialCoefficient n l j)⁻¹ • (radiusPolynomial n ^ (j + 1) * p), ?_, ?_⟩
      · apply Submodule.smul_mem
        exact Submodule.subset_span ⟨j + 1, l, p, by omega, hhom, hΔ, rfl⟩
      · rw [laplacePolynomial_smul, laplacePolynomial_radial_harmonic hhom hΔ]
        rw [C_mul', smul_smul, inv_mul_cancel₀ (ne_of_gt (radialCoefficient_pos hn l j)), one_smul]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp [laplacePolynomial]⟩
  | add x y _ _ hx hy =>
      obtain ⟨q, hq, hΔq⟩ := hx
      obtain ⟨r, hr, hΔr⟩ := hy
      exact ⟨q + r, Submodule.add_mem _ hq hr, by rw [laplacePolynomial_add, hΔq, hΔr]⟩
  | smul c x _ hx =>
      obtain ⟨q, hq, hΔq⟩ := hx
      exact ⟨c • q, Submodule.smul_mem _ c hq, by rw [laplacePolynomial_smul, hΔq]⟩

/-- Finite Fischer decomposition: the induction on the degree. -/
lemma homogeneous_mem_fischerSpan {n : ℕ} (hn : 2 ≤ n) (d : ℕ)
    {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous d) : p ∈ fischerSpan n d := by
  induction d using Nat.strong_induction_on generalizing p with
  | h d ih =>
      by_cases hd : d < 2
      · exact harmonic_mem_fischerSpan hp (laplacePolynomial_eq_zero_small hp hd)
      · have hdp := ih (d - 2) (by omega) (laplacePolynomial_homogeneous hp)
        obtain ⟨q, hq, hΔq⟩ := fischerSpan_laplace_preimage hn hdp
        have hd' : d - 2 + 2 = d := by omega
        rw [hd'] at hq
        have hhomq := fischerSpan_le_homogeneous n d hq
        have hrem : p - q ∈ fischerSpan n d := harmonic_mem_fischerSpan (hp.sub hhomq)
          (by rw [laplacePolynomial_sub, hΔq, sub_self])
        simpa only [sub_add_cancel] using (fischerSpan n d).add_mem hrem hq

lemma polynomialRestriction_apply {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (u : Sphere n) :
    polynomialRestriction n p u = polynomialFunction p u := rfl

lemma polynomialRestriction_radius (n : ℕ) : polynomialRestriction n (radiusPolynomial n) = 1 := by
  ext u
  change polynomialFunction (radiusPolynomial n) u = 1
  rw [polynomialFunction_radius, norm_coe, one_pow]

lemma polynomialRestriction_separates (n : ℕ) : (polynomialRestriction n).range.SeparatesPoints := by
  intro u v huv
  have h : ∃ i : Fin n, (u : Space n) i ≠ (v : Space n) i := by
    by_contra! h
    apply huv
    apply Subtype.ext
    exact PiLp.ext h
  obtain ⟨i, hi⟩ := h
  refine ⟨polynomialRestriction n (X i), ⟨polynomialRestriction n (X i), ⟨X i, rfl⟩, rfl⟩, ?_⟩
  simpa only [polynomialRestriction_apply, polynomialFunction_X] using hi

lemma polynomialRestriction_dense (n : ℕ) : DenseRange (polynomialRestriction n) := by
  apply dense_iff_closure_eq.mpr
  change closure (↑(polynomialRestriction n).range : Set C(Sphere n, ℝ)) = univ
  rw [← Subalgebra.topologicalClosure_coe,
    ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
      (polynomialRestriction_separates n)]
  rfl

lemma polynomialL2_dense (n : ℕ) [NeZero n] : DenseRange (polynomialL2 n) :=
  (ContinuousMap.toLp_denseRange ℝ (sigma n) ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).comp
    (polynomialRestriction_dense n) (toH n).continuous

lemma harmonicSpace_orthogonal {n : ℕ} (hn : 2 ≤ n) [NeZero n] :
    OrthogonalFamily ℝ (fun d => harmonicSpace n d) (fun d => (harmonicSpace n d).subtypeₗᵢ) := by
  intro d e hde p q
  obtain ⟨P, hP, hPeq⟩ := p.property
  obtain ⟨Q, hQ, hQeq⟩ := q.property
  change ⟪(p : H n), (q : H n)⟫ = 0
  rw [← hPeq, ← hQeq]
  change ⟪toH n (polynomialRestriction n P), toH n (polynomialRestriction n Q)⟫ = 0
  rw [inner_toH]
  exact harmonic_orthogonal hn hP.1 hQ.1 hP.2 hQ.2 hde

lemma polynomialL2_mem_iSup_of_fischer {n d : ℕ} [NeZero n] {p : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ fischerSpan n d) : polynomialL2 n p ∈ ⨆ l, harmonicSpace n l := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, l, p, _, hhom, hΔ, rfl⟩ := hx
      have hr : polynomialL2 n (radiusPolynomial n ^ j * p) = polynomialL2 n p := by
        change toH n (polynomialRestriction n _) = toH n (polynomialRestriction n p)
        rw [map_mul, map_pow, polynomialRestriction_radius, one_pow, one_mul]
      rw [hr]
      exact Submodule.mem_iSup_of_mem l (Submodule.mem_map.mpr ⟨p, ⟨hhom, hΔ⟩, rfl⟩)
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using Submodule.add_mem _ hp hq
  | smul c p _ hp => simpa only [map_smul] using Submodule.smul_mem _ c hp

lemma polynomialL2_mem_iSup {n : ℕ} (hn : 2 ≤ n) [NeZero n] (p : MvPolynomial (Fin n) ℝ) :
    polynomialL2 n p ∈ ⨆ l, harmonicSpace n l := by
  rw [← sum_homogeneousComponent p, map_sum]
  apply Submodule.sum_mem
  intro d _
  exact polynomialL2_mem_iSup_of_fischer
    (homogeneous_mem_fischerSpan hn d (homogeneousComponent_isHomogeneous d p))

/-- Completeness under the actual measure, using Stone--Weierstrass and finite
Fischer decomposition, with no assumed spectral interface. -/
lemma harmonicSpace_total {n : ℕ} (hn : 2 ≤ n) [NeZero n] :
    (⨆ l, harmonicSpace n l).topologicalClosure = ⊤ := by
  apply SetLike.coe_injective
  rw [Submodule.topologicalClosure_coe, Submodule.top_coe]
  apply dense_iff_closure_eq.mp
  exact (polynomialL2_dense n).mono (by rintro _ ⟨p, rfl⟩; exact polynomialL2_mem_iSup hn p)

lemma energy_add_right {n : ℕ} [NeZero n] {f g h : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h) :
    energy f (fun x => g x + h x) = energy f g + energy f h := by
  unfold energy
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [rotDeriv_add _ (hg.differentiable (by norm_num))
    (hh.differentiable (by norm_num)), mul_add]
  exact integral_add
    (continuous_integrable (((continuous_rotDeriv _ hf).mul (continuous_rotDeriv _ hg)).comp
      continuous_subtype_val))
    (continuous_integrable (((continuous_rotDeriv _ hf).mul (continuous_rotDeriv _ hh)).comp
      continuous_subtype_val))

lemma energy_add_left {n : ℕ} [NeZero n] {f g h : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h) :
    energy (fun x => f x + g x) h = energy f h + energy g h := by
  simpa only [energy_symm] using energy_add_right hh hf hg

lemma rotDeriv_const_mul {n : ℕ} (T : Space n →L[ℝ] Space n)
    {f : Space n → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (x : Space n) :
    rotDeriv T (fun y => c * f y) x = c * rotDeriv T f x := by
  unfold rotDeriv
  rw [fderiv_const_mul (hf x) c]
  rfl

lemma energy_const_mul_right {n : ℕ} {f g : Space n → ℝ}
    (hg : Differentiable ℝ g) (c : ℝ) :
    energy f (fun x => c * g x) = c * energy f g := by
  simp only [energy, rotDeriv_const_mul _ hg c, mul_left_comm _ c, mean, integral_const_mul,
    ← Finset.mul_sum]

lemma energy_const_mul_left {n : ℕ} {f g : Space n → ℝ}
    (hf : Differentiable ℝ f) (c : ℝ) :
    energy (fun x => c * f x) g = c * energy f g := by
  simpa only [energy_symm] using energy_const_mul_right (f := g) hf c

lemma energy_sub_self {n : ℕ} [NeZero n] {f g : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    energy (fun x => f x - g x) (fun x => f x - g x) =
      energy f f - 2 * energy f g + energy g g := by
  have hsub : (fun x => f x - g x) = fun x => f x + (-1) * g x := by funext x; ring
  rw [hsub, energy_add_left hf (contDiff_const.mul hg) (hf.add (contDiff_const.mul hg)),
    energy_add_right hf hf (contDiff_const.mul hg),
    energy_const_mul_left (hg.differentiable (by norm_num)),
    energy_add_right hg hf (contDiff_const.mul hg),
    energy_const_mul_right (hg.differentiable (by norm_num)),
    energy_const_mul_right (hg.differentiable (by norm_num)), energy_symm g f]
  ring

lemma energy_zero_right {n : ℕ} (f : Space n → ℝ) : energy f (fun _ => 0) = 0 := by
  simp [energy, rotDeriv_const, mean]

lemma energy_finset_sum_right {n : ℕ} [NeZero n] {ι : Type uι} (s : Finset ι)
    {f : Space n → ℝ} {g : ι → Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ∀ i, ContDiff ℝ 1 (g i)) :
    energy f (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, energy f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [energy_zero_right]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [energy_add_right hf (hg a) (ContDiff.sum fun i _ => hg i), ih]

/-- Integration by parts against each genuine harmonic eigenfunction. -/
lemma energy_harmonic_right {n d : ℕ} [NeZero n] {f : Space n → ℝ}
    {p : MvPolynomial (Fin n) ℝ} (hf : ContDiff ℝ 1 f) (hp : p.IsHomogeneous d)
    (hΔp : laplacePolynomial p = 0) :
    energy f (polynomialFunction p) = eigenvalue n d *
      mean (fun u : Sphere n => f u * polynomialFunction p u) := by
  have h := mean_casimir hf ((polynomialFunction_contDiff p).of_le le_top)
  simp_rw [casimir_harmonic hp hΔp, mul_left_comm (f _) (-eigenvalue n d)] at h
  rw [mean, integral_const_mul] at h
  unfold mean
  linarith

lemma polynomialFunction_smul_argument {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (c : ℝ) (x : Space n) :
    polynomialFunction p (c • x) = c ^ d * polynomialFunction p x := by
  unfold polynomialFunction
  simp only [MvPolynomial.eval_eq, PiLp.smul_apply, smul_eq_mul, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← hp.degree_eq_sum_deg_support ha]
  ring

lemma harmonicSpace_zero_constant {n : ℕ} [NeZero n] {v : H n} (hv : v ∈ harmonicSpace n 0) :
    ∃ c : ℝ, v = toH n (ContinuousMap.const (Sphere n) c) := by
  obtain ⟨p, hp, rfl⟩ := hv
  have hhom : p.IsHomogeneous 0 := hp.1
  rw [← totalDegree_zero_iff_isHomogeneous,
    totalDegree_eq_zero_iff_eq_C] at hhom
  refine ⟨p.coeff 0, ?_⟩
  rw [hhom]
  simp only [coeff_C]
  change toH n (polynomialRestriction n (C _)) = _
  congr 1
  ext u
  exact congrFun (polynomialFunction_C _) _

lemma constant_mem_harmonicSpace_zero (n : ℕ) [NeZero n] (c : ℝ) :
    toH n (ContinuousMap.const (Sphere n) c) ∈ harmonicSpace n 0 := by
  refine Submodule.mem_map.mpr ⟨C c, ⟨isHomogeneous_C _ _, ?_⟩, ?_⟩
  · simp [LinearMap.mem_ker, laplaceLinear, laplacePolynomial]
  · change toH n (polynomialRestriction n (C c)) = _
    congr 1
    ext u
    exact congrFun (polynomialFunction_C _) _

lemma harmonicSpace_zero_projection (n : ℕ) [NeZero n] (f : C(Sphere n, ℝ)) :
    (harmonicSpace n 0).starProjection (toH n f) =
      toH n (ContinuousMap.const (Sphere n) (mean f)) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (constant_mem_harmonicSpace_zero n _)
  intro v hv
  obtain ⟨c, rfl⟩ := harmonicSpace_zero_constant hv
  rw [← map_sub, inner_toH]
  change mean (fun u : Sphere n => (f u - mean f) * c) = 0
  unfold mean
  rw [integral_mul_const, integral_sub (continuous_integrable f.continuous)
    (integrable_const _)]
  simp

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal RealInnerProductSpace Pointwise
namespace PettyProjection.Spherical

lemma harmonicSpace_isHilbertSum {n : ℕ} (hn : 2 ≤ n) [NeZero n] :
    IsHilbertSum ℝ (fun d : ℕ => harmonicSpace n d)
      (fun d : ℕ => (harmonicSpace n d).subtypeₗᵢ) := by
  let F : ℕ → Submodule ℝ (H n) := fun d => harmonicSpace n d
  have horth : OrthogonalFamily ℝ (fun d => F d) (fun d => (F d).subtypeₗᵢ) :=
    harmonicSpace_orthogonal hn
  have htotal : (⨆ d, F d).topologicalClosure = ⊤ := harmonicSpace_total hn
  let : ∀ d, CompleteSpace (F d) := fun d => FiniteDimensional.complete ℝ (harmonicSpace n d)
  exact IsHilbertSum.mkInternal F horth htotal.ge

open MvPolynomial

lemma polynomialL2_X_mul_X (n : ℕ) [NeZero n] (i j : Fin n) :
    polynomialL2 n (X i * X j) = toH n (coordinateProduct n i j) := by
  change toH n (polynomialRestriction n (X i * X j)) = _
  congr 1
  ext u
  simp [polynomialRestriction_apply, polynomialFunction, coordinateProduct]

lemma polynomialL2_X_mul_mem_lowSpace {n : ℕ} [NeZero n] (i : Fin n)
    {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous 1) :
    polynomialL2 n (X i * p) ∈ lowSpace n := by
  have hmem : p ∈ Submodule.span ℝ (Set.range (X : Fin n → MvPolynomial (Fin n) ℝ)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hp
  clear hp
  induction hmem using Submodule.span_induction with
  | mem q hq =>
      obtain ⟨j, rfl⟩ := hq
      rw [polynomialL2_X_mul_X]
      exact Submodule.subset_span ⟨(i,j), rfl⟩
  | zero => simp
  | add p q _ _ hp hq =>
      simpa only [mul_add, map_add] using Submodule.add_mem (lowSpace n) hp hq
  | smul c p _ hp =>
      simpa only [mul_smul_comm, map_smul] using Submodule.smul_mem (lowSpace n) c hp

lemma homogeneous_two_mem_lowSpace {n : ℕ} [NeZero n] {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous 2) : polynomialL2 n p ∈ lowSpace n := by
  have hsum : polynomialL2 n (∑ i : Fin n, X i * pderiv i p) ∈ lowSpace n := by
    rw [map_sum]
    exact Submodule.sum_mem _ fun i _ => polynomialL2_X_mul_mem_lowSpace i hp.pderiv
  have htwo : (2 : ℝ) • polynomialL2 n p ∈ lowSpace n := by
    simpa only [hp.sum_X_mul_pderiv, two_nsmul, map_add, two_smul ℝ] using hsum
  exact (Submodule.smul_mem_iff (lowSpace n) (by norm_num : (2 : ℝ) ≠ 0)).mp htwo

lemma harmonicSpace_two_le_lowSpace (n : ℕ) [NeZero n] :
    harmonicSpace n 2 ≤ lowSpace n := by
  rintro v ⟨p, hp, rfl⟩
  exact homogeneous_two_mem_lowSpace hp.1

end PettyProjection.Spherical
end

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {F : ℕ → Submodule ℝ E} [∀ i, CompleteSpace (F i)]

lemma hilbertSum_component (h : IsHilbertSum ℝ (fun i => F i) (fun i => (F i).subtypeₗᵢ))
    (x : E) (i : ℕ) :
    (F i).starProjection x = (h.linearIsometryEquiv x i : E) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (h.linearIsometryEquiv x i).property
  intro w hw
  have hh := h.linearIsometryEquiv.symm.inner_map_map (h.linearIsometryEquiv x)
    (lp.single 2 i (⟨w,hw⟩ : F i))
  rw [LinearIsometryEquiv.symm_apply_apply, h.linearIsometryEquiv_symm_apply_single,
    lp.inner_single_right] at hh
  change ⟪x, w⟫ = ⟪(h.linearIsometryEquiv x i : E), w⟫ at hh
  rw [inner_sub_left, hh, sub_self]

lemma hilbertSum_hasSum_projection_norm_sq
    (h : IsHilbertSum ℝ (fun i => F i) (fun i => (F i).subtypeₗᵢ)) (x : E) :
    HasSum (fun i => ‖(F i).starProjection x‖ ^ 2) (‖x‖ ^ 2) := by
  have hh := lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (h.linearIsometryEquiv x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
    hilbertSum_component h, Submodule.norm_coe] using hh

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.SphericalGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology MvPolynomial
open scoped ENNReal RealInnerProductSpace Pointwise
namespace PettyProjection.Spherical

lemma polynomialFunction_odd {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (hd : Odd d) : Function.Odd (polynomialFunction p) := by
  intro x
  simpa only [neg_one_smul, hd.neg_one_pow, neg_one_mul] using
    polynomialFunction_smul_argument hp (-1) x

lemma mean_even_mul_odd {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    {f : Space n → ℝ} (heven : Function.Even f) (hp : p.IsHomogeneous d) (hd : Odd d) :
    mean (fun u : Sphere n => f u * polynomialFunction p u) = 0 := by
  have h := mean_rotation (LinearIsometryEquiv.neg ℝ : Space n ≃ₗᵢ[ℝ] Space n)
    (fun u : Sphere n => f u * polynomialFunction p u)
  have hh : (fun u : Sphere n =>
      f (sphereMap (LinearIsometryEquiv.neg ℝ) u) *
        polynomialFunction p (sphereMap (LinearIsometryEquiv.neg ℝ) u)) =
      (fun u : Sphere n => -(f u * polynomialFunction p u)) := by
    funext u
    change f (-↑u) * polynomialFunction p (-↑u) = _
    rw [heven, polynomialFunction_odd hp hd, mul_neg]
  rw [hh, mean, integral_neg] at h
  unfold mean at h ⊢
  linarith

lemma projection_odd_zero {n d : ℕ} [NeZero n] {f : Space n → ℝ}
    (hf : Continuous f) (heven : Function.Even f) (hd : Odd d) :
    (harmonicSpace n d).starProjection (toH n (restrictContinuous f hf)) = 0 := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  rintro v ⟨p, hp, rfl⟩
  rw [sub_zero]
  change ⟪toH n (restrictContinuous f hf), toH n (polynomialRestriction n p)⟫ = 0
  rw [inner_toH]
  exact mean_even_mul_odd heven hp.1 hd

lemma harmonicRepresentative_homogeneous {n d : ℕ} [NeZero n] (v : harmonicSpace n d) :
    (harmonicRepresentative v).IsHomogeneous d :=
  (Classical.choose_spec v.property).1.1

lemma harmonicRepresentative_laplace {n d : ℕ} [NeZero n] (v : harmonicSpace n d) :
    laplacePolynomial (harmonicRepresentative v) = 0 :=
  (Classical.choose_spec v.property).1.2

lemma harmonicRepresentative_toH {n d : ℕ} [NeZero n] (v : harmonicSpace n d) :
    polynomialL2 n (harmonicRepresentative v) = (v : H n) :=
  (Classical.choose_spec v.property).2

lemma inner_projection_self {n d : ℕ} [NeZero n] (v : H n) :
    ⟪v, (harmonicSpace n d).starProjection v⟫ = ‖(harmonicSpace n d).starProjection v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, Submodule.inner_starProjection_left_eq_right]
  rw [Submodule.starProjection_eq_self_iff.mpr
    ((harmonicSpace n d).starProjection_apply_mem v)]

lemma energy_harmonicRepresentative_right {n d : ℕ} [NeZero n]
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (v : harmonicSpace n d) :
    energy f (polynomialFunction (harmonicRepresentative v)) =
      eigenvalue n d * ⟪toH n (restrictContinuous f hf.continuous), (v : H n)⟫ := by
  rw [energy_harmonic_right hf (harmonicRepresentative_homogeneous v)
    (harmonicRepresentative_laplace v)]
  rw [← harmonicRepresentative_toH v]
  change _ = eigenvalue n d * ⟪toH n (restrictContinuous f hf.continuous),
    toH n (polynomialRestriction n (harmonicRepresentative v))⟫
  rw [inner_toH]
  rfl

lemma sum_inner_projection {n : ℕ} (hn : 2 ≤ n) [NeZero n] (s : Finset ℕ)
    (v : H n) {e : ℕ} (he : e ∈ s) :
    ⟪∑ d ∈ s, (harmonicSpace n d).starProjection v,
        (harmonicSpace n e).starProjection v⟫ =
      ‖(harmonicSpace n e).starProjection v‖ ^ 2 := by
  rw [sum_inner]
  rw [Finset.sum_eq_single e]
  · exact real_inner_self_eq_norm_sq _
  · intro d _ hde
    have h := harmonicSpace_orthogonal hn hde
      ((harmonicSpace n d).orthogonalProjectionOnto v)
      ((harmonicSpace n e).orthogonalProjectionOnto v)
    simpa only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype,
      Submodule.coe_orthogonalProjectionOnto_apply] using h
  · exact fun h => False.elim (h he)

/-- The finite Bessel bound, established by subtracting a finite harmonic
polynomial sum. No infinite series is differentiated. -/
lemma energy_bessel_finset {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (s : Finset ℕ) :
    ∑ d ∈ s, eigenvalue n d * ‖(harmonicSpace n d).starProjection
      (toH n (restrictContinuous f hf.continuous))‖ ^ 2 ≤ energy f f := by
  let v := toH n (restrictContinuous f hf.continuous)
  let vs (d : ℕ) := (harmonicSpace n d).orthogonalProjectionOnto v
  let ps (d : ℕ) := harmonicRepresentative (vs d)
  let g : Space n → ℝ := fun x => ∑ d ∈ s, polynomialFunction (ps d) x
  have hpd (d : ℕ) : ContDiff ℝ 1 (polynomialFunction (ps d)) :=
    (polynomialFunction_contDiff _).of_le le_top
  have hg : ContDiff ℝ 1 g := ContDiff.sum fun d _ => hpd d
  have hG : toH n (restrictContinuous g hg.continuous) =
      ∑ d ∈ s, (harmonicSpace n d).starProjection v := by
    have hr : restrictContinuous g hg.continuous = ∑ d ∈ s, polynomialRestriction n (ps d) := by
      ext u
      simp [restrictContinuous, g, polynomialRestriction_apply]
    rw [hr, map_sum]
    apply Finset.sum_congr rfl
    intro d _
    exact (harmonicRepresentative_toH (vs d)).trans
      ((harmonicSpace n d).coe_orthogonalProjectionOnto_apply v)
  have hfg : energy f g =
      ∑ d ∈ s, eigenvalue n d * ‖(harmonicSpace n d).starProjection v‖ ^ 2 := by
    rw [energy_finset_sum_right s hf hpd]
    apply Finset.sum_congr rfl
    intro d _
    rw [energy_harmonicRepresentative_right hf (vs d)]
    exact congrArg (eigenvalue n d * ·) (inner_projection_self v)
  have hgg : energy g g =
      ∑ d ∈ s, eigenvalue n d * ‖(harmonicSpace n d).starProjection v‖ ^ 2 := by
    rw [energy_finset_sum_right s hg hpd]
    apply Finset.sum_congr rfl
    intro d hd
    rw [energy_harmonicRepresentative_right hg (vs d), hG]
    exact congrArg (eigenvalue n d * ·) (sum_inner_projection hn s v hd)
  have hpos := energy_nonneg (fun x => f x - g x)
  rw [energy_sub_self hf hg, hfg, hgg] at hpos
  linarith

lemma eigenvalue_four_le {n d : ℕ} (hn : 2 ≤ n) (hd : 4 ≤ d) :
    eigenvalue n 4 ≤ eigenvalue n d := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd' : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hprod := mul_nonneg (sub_nonneg.mpr hd') (sub_nonneg.mpr hn')
  norm_num [eigenvalue]
  nlinarith

lemma Q_zero_of_mem_lowSpace {n : ℕ} [NeZero n] {v : H n} (hv : v ∈ lowSpace n) :
    Q n v = 0 := by
  rw [Q_eq_sub, Submodule.starProjection_eq_self_iff.mpr hv, sub_self]

lemma projection_zero_mem_lowSpace {n : ℕ} [NeZero n] (v : H n) :
    (harmonicSpace n 0).starProjection v ∈ lowSpace n := by
  obtain ⟨c, hc⟩ := harmonicSpace_zero_constant ((harmonicSpace n 0).starProjection_apply_mem v)
  rw [hc]
  exact constant_mem_lowSpace n c

lemma projection_inner_ne {n : ℕ} (hn : 2 ≤ n) [NeZero n] (v : H n)
    {d e : ℕ} (hde : d ≠ e) :
    ⟪(harmonicSpace n d).starProjection v, (harmonicSpace n e).starProjection v⟫ = 0 := by
  have h := harmonicSpace_orthogonal hn hde
    ((harmonicSpace n d).orthogonalProjectionOnto v)
    ((harmonicSpace n e).orthogonalProjectionOnto v)
  simpa only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype,
    Submodule.coe_orthogonalProjectionOnto_apply] using h

lemma norm_Q_sq_le_remainder {n : ℕ} (hn : 2 ≤ n) [NeZero n] (v : H n) :
    ‖Q n v‖ ^ 2 ≤ ‖v‖ ^ 2 - ‖(harmonicSpace n 0).starProjection v‖ ^ 2 -
      ‖(harmonicSpace n 2).starProjection v‖ ^ 2 := by
  let p0 := (harmonicSpace n 0).starProjection v
  let p2 := (harmonicSpace n 2).starProjection v
  have h0 : Q n p0 = 0 := Q_zero_of_mem_lowSpace (projection_zero_mem_lowSpace v)
  have h2 : Q n p2 = 0 := Q_zero_of_mem_lowSpace
    (harmonicSpace_two_le_lowSpace n ((harmonicSpace n 2).starProjection_apply_mem v))
  have hQ : Q n (v - p0 - p2) = Q n v := by simp only [map_sub, h0, h2, sub_zero]
  have h := norm_Q_le n (v - p0 - p2)
  rw [hQ] at h
  have hsq := sq_le_sq₀ (norm_nonneg (Q n v)) (norm_nonneg (v - p0 - p2)) |>.mpr h
  have hnorm : ‖v - p0 - p2‖ ^ 2 = ‖v‖ ^ 2 - ‖p0‖ ^ 2 - ‖p2‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_left,
      inner_projection_self v, inner_projection_self v,
      projection_inner_ne hn v (by decide : (0 : ℕ) ≠ 2)]
    ring
  exact hsq.trans_eq hnorm

lemma energy_spectral_lower {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (heven : Function.Even f) :
    let v := toH n (restrictContinuous f hf.continuous)
    eigenvalue n 4 * ‖v‖ ^ 2 - eigenvalue n 4 * ‖(harmonicSpace n 0).starProjection v‖ ^ 2 -
      (eigenvalue n 4 - eigenvalue n 2) * ‖(harmonicSpace n 2).starProjection v‖ ^ 2 ≤
        energy f f := by
  let v := toH n (restrictContinuous f hf.continuous)
  let a (d : ℕ) := ‖(harmonicSpace n d).starProjection v‖ ^ 2
  let b (d : ℕ) := eigenvalue n 4 * a d -
    (if d = 0 then eigenvalue n 4 * a 0 else 0) -
    (if d = 2 then (eigenvalue n 4 - eigenvalue n 2) * a 2 else 0)
  have ha : HasSum a (‖v‖ ^ 2) :=
    hilbertSum_hasSum_projection_norm_sq (harmonicSpace_isHilbertSum hn) v
  have hb : HasSum b (eigenvalue n 4 * ‖v‖ ^ 2 - eigenvalue n 4 * a 0 -
      (eigenvalue n 4 - eigenvalue n 2) * a 2) :=
    ((ha.mul_left (eigenvalue n 4)).sub (hasSum_ite_eq 0 _)).sub (hasSum_ite_eq 2 _)
  have hb_le (d : ℕ) : b d ≤ eigenvalue n d * a d := by
    by_cases h0 : d = 0
    · subst d; simp [b, eigenvalue]
    by_cases h2 : d = 2
    · subst d; simp only [b, ite_eq_right (by decide : (2 : ℕ) ≠ 0), ite_true, sub_zero]; ring_nf; exact le_rfl
    by_cases h1 : d = 1
    · subst d
      have hz : a 1 = 0 := by
        simp [a, v, projection_odd_zero hf.continuous heven (by decide : Odd 1)]
      simp [b, hz]
    by_cases h3 : d = 3
    · subst d
      have hz : a 3 = 0 := by
        simp [a, v, projection_odd_zero hf.continuous heven (by decide : Odd 3)]
      simp [b, hz]
    have hd : 4 ≤ d := by omega
    simpa only [b, ite_eq_right h0, ite_eq_right h2, sub_zero] using
      mul_le_mul_of_nonneg_right (eigenvalue_four_le hn hd) (sq_nonneg _)
  apply le_of_tendsto hb
  apply Eventually.of_forall
  intro s
  exact (Finset.sum_le_sum fun d _ => hb_le d).trans (energy_bessel_finset hn hf s)

/-- The genuine degree-two-removed even spherical spectral gap, under the
canonical probability measure. `energy` is the integrated squared tangential
derivative represented by the coordinate rotation generators. -/
lemma even_spectral_gap {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (heven : Function.Even f) :
    (2 * n : ℝ) * variance (fun u : Sphere n => f u) + (2 * n + 8 : ℝ) *
      ‖Q n (toH n (restrictContinuous f hf.continuous))‖ ^ 2 ≤ energy f f := by
  let F := restrictContinuous f hf.continuous
  let v := toH n F
  have h0 : ‖(harmonicSpace n 0).starProjection v‖ ^ 2 = (mean F) ^ 2 := by
    rw [harmonicSpace_zero_projection n F, norm_toH_sq]
    simpa only [ContinuousMap.const_apply] using mean_const n ((mean F) ^ 2)
  have hvar : variance (fun u : Sphere n => f u) = ‖v‖ ^ 2 - (mean F) ^ 2 := by
    rw [norm_toH_sq]
    rfl
  have h := energy_spectral_lower hn hf heven
  have hQ := norm_Q_sq_le_remainder hn v
  change eigenvalue n 4 * ‖v‖ ^ 2 - eigenvalue n 4 * ‖(harmonicSpace n 0).starProjection v‖ ^ 2 -
    (eigenvalue n 4 - eigenvalue n 2) * ‖(harmonicSpace n 2).starProjection v‖ ^ 2 ≤ energy f f at h
  rw [h0] at h hQ
  rw [hvar]
  have hmul := mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ 2 * n + 8)
  norm_num [eigenvalue] at h
  nlinarith

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal RealInnerProductSpace Pointwise
namespace PettyProjection.Spherical

lemma line_convex {n : ℕ} {f : Space n → ℝ} (hc : ConvexOn ℝ univ f)
    (x y : Space n) : ConvexOn ℝ univ (fun t : ℝ => f (x + t • y)) := by
  constructor
  · exact convex_univ
  · intro a _ b _ s t hs ht hst
    have h := hc.2 (mem_univ (x + a • y)) (mem_univ (x + b • y)) hs ht hst
    have he : x + (s * a + t * b) • y = s • (x + a • y) + t • (x + b • y) := by
      calc
        _ = (s + t) • x + (s * a + t * b) • y := by rw [hst, one_smul]
        _ = _ := by module
    simpa only [smul_eq_mul, ← he] using h

lemma line_hasDerivAt {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] (x y : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x + s • y) y t := by
  have h : HasDerivAt (fun s : ℝ => s • y) y t := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const y
  exact h.const_add x

lemma line_second_hasDerivAt {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x y : E) :
    HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • y) y)
      (fderiv ℝ (fderiv ℝ f) x y y) 0 := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hh : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    (hfd.differentiable (by norm_num) x).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => x + t • y) y 0 := line_hasDerivAt x y 0
  have hdx : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • y))
      (fderiv ℝ (fderiv ℝ f) x y) 0 := by
    have hh' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (x + (0 : ℝ) • y) := by
      simpa only [zero_smul, add_zero] using hh
    exact hh'.comp_hasDerivAt 0 hl
  have hd : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • y) y)
      (fderiv ℝ (fderiv ℝ f) x y y + fderiv ℝ f (x + (0 : ℝ) • y) 0) 0 :=
    hdx.clm_apply (hasDerivAt_const 0 y)
  simpa only [map_zero, add_zero] using hd

lemma hessian_nonneg_of_convex {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : ConvexOn ℝ univ f) (x y : Space n) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x y y := by
  have hdf (t : ℝ) : HasDerivAt (fun s : ℝ => f (x + s • y))
      (fderiv ℝ f (x + t • y) y) t :=
    (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t (line_hasDerivAt x y t)
  have hmono : Monotone (fun t : ℝ => fderiv ℝ f (x + t • y) y) := by
    have h := (line_convex hc x y).monotoneOn_deriv (fun t _ => (hdf t).differentiableAt)
    have heq : deriv (fun t : ℝ => f (x + t • y)) =
        (fun t => fderiv ℝ f (x + t • y) y) := funext fun t => (hdf t).deriv
    rw [heq] at h
    exact monotoneOn_univ.mp h
  rw [← (line_second_hasDerivAt hf x y).deriv]
  exact hmono.deriv_nonneg

lemma rotDeriv_rotDeriv {n : ℕ} (T : Space n →L[ℝ] Space n) {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Space n) :
    rotDeriv T (rotDeriv T f) x =
      fderiv ℝ (fderiv ℝ f) x (T x) (T x) + fderiv ℝ f x (T (T x)) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hd := (hfd.differentiable (by norm_num) x).hasFDerivAt.clm_apply T.hasFDerivAt
  change fderiv ℝ (fun y => fderiv ℝ f y (T y)) x (T x) = _
  rw [hd.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, add_comm]

lemma generator_square_coord {n : ℕ} (i j a : Fin n) (x : Space n) :
    (generator n i j (generator n i j x)) a =
      2 * (if i = j then if i = a then x a else 0 else 0) -
        (if j = a then x a else 0) - (if i = a then x a else 0) := by
  by_cases hij : i = j <;> by_cases hia : i = a <;> by_cases hja : j = a <;>
    simp_all [generator_apply_coord, eq_comm]; ring

lemma sum_generator_square {n : ℕ} (x : Space n) :
    ∑ i : Fin n, ∑ j : Fin n, generator n i j (generator n i j x) =
      (-2 * ((n : ℝ) - 1)) • x := by
  ext a
  simp only [WithLp.ofLp_sum, Finset.sum_apply, generator_square_coord, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

lemma convex_casimir_lower {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : ConvexOn ℝ univ f) (x : Space n) :
    -((n : ℝ) - 1) * fderiv ℝ f x x ≤ casimir f x := by
  have h (i j : Fin n) : fderiv ℝ f x (generator n i j (generator n i j x)) ≤
      rotDeriv (generator n i j) (rotDeriv (generator n i j) f) x := by
    rw [rotDeriv_rotDeriv _ hf]
    linarith [hessian_nonneg_of_convex hf hc x (generator n i j x)]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h i j))
  have hh := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simp only [← map_sum, sum_generator_square, map_smul, smul_eq_mul] at hh
  unfold casimir
  nlinarith

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Pointwise Convolution
namespace PettyProjection.Spherical

lemma seminorm_lipschitz (n : ℕ) (g : Seminorm ℝ (Space n)) :
    ∃ C : ℝ≥0, LipschitzWith C g := by
  obtain ⟨C, hC, hbound⟩ := g.bound_of_continuous_normedSpace (seminorm_continuous n g)
  refine ⟨⟨C, hC.le⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  change |g x - g y| ≤ C * dist x y
  exact (abs_sub_map_le_sub g x y).trans (by simpa only [dist_eq_norm] using hbound (x - y))

lemma normSmooth_even {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n)) :
    Function.Even (normSmooth g φ) := by
  intro x
  exact convolution_neg_of_neg_eq (ContinuousLinearMap.lsmul ℝ ℝ) (Eventually.of_forall φ.normed_neg)
    (Eventually.of_forall (fun x => map_neg_eq_map g x))

lemma normSmooth_integrable {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n))
    (x : Space n) : Integrable (fun y => φ.normed volume y * g (x - y)) volume :=
  φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
    (ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed.locallyIntegrable (seminorm_continuous n g) x

lemma normSmooth_convex {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n)) :
    ConvexOn ℝ univ (normSmooth g φ) := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    have hi₁ := (normSmooth_integrable g φ x).const_mul a
    have hi₂ := (normSmooth_integrable g φ y).const_mul b
    change (∫ z, φ.normed volume z * g (a • x + b • y - z)) ≤
        a * (∫ z, φ.normed volume z * g (x - z)) + b * (∫ z, φ.normed volume z * g (y - z))
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hi₁ hi₂]
    apply integral_mono (normSmooth_integrable g φ (a • x + b • y)) (hi₁.add hi₂)
    intro z
    have he : a • x + b • y - z = a • (x - z) + b • (y - z) := by
      calc
        _ = a • x + b • y - (a + b) • z := by rw [hab, one_smul]
        _ = _ := by module
    have h := mul_le_mul_of_nonneg_left
      (g.convexOn.2 (mem_univ (x-z)) (mem_univ (y-z)) ha hb hab) (φ.nonneg_normed (μ := volume) z)
    simp only [Pi.add_apply]
    rw [he]
    simpa only [smul_eq_mul, mul_add, mul_left_comm] using h

lemma normSmooth_dist_le {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n))
    {C : ℝ≥0} (hC : LipschitzWith C g) (x : Space n) :
    dist (normSmooth g φ x) (g x) ≤ C * φ.rOut := by
  apply φ.dist_normed_convolution_le (seminorm_continuous n g).aestronglyMeasurable
  intro y hy
  exact (hC.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left (mem_ball.mp hy).le C.coe_nonneg)

lemma convex_radial_bounds {n : ℕ} {f : Space n → ℝ}
    (hf : Differentiable ℝ f) (hc : ConvexOn ℝ univ f) (x : Space n) :
    f x - f 0 ≤ fderiv ℝ f x x ∧ fderiv ℝ f x x ≤ f ((2 : ℝ) • x) - f x := by
  have hd : HasDerivAt (fun t : ℝ => f (x + t • x)) (fderiv ℝ f x x) 0 := by
    have h : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • x) := by
      simpa only [zero_smul, add_zero] using (hf x).hasFDerivAt
    exact h.comp_hasDerivAt 0 (line_hasDerivAt x x 0)
  have hl := (line_convex hc x x).slope_le_of_hasDerivAt (mem_univ (-1 : ℝ)) (mem_univ 0)
    (by norm_num : (-1 : ℝ) < 0) hd
  have hr := (line_convex hc x x).le_slope_of_hasDerivAt (mem_univ 0) (mem_univ (1 : ℝ))
    (by norm_num : (0 : ℝ) < 1) hd
  simpa only [slope, vsub_eq_sub, neg_smul, one_smul, add_neg_cancel,
    zero_smul, add_zero, two_smul, zero_sub, neg_neg, sub_zero, inv_one, smul_eq_mul, one_mul] using And.intro hl hr

lemma normSmooth_radial_dist_le {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n))
    {C : ℝ≥0} (hC : LipschitzWith C g) (x : Space n) :
    dist (fderiv ℝ (normSmooth g φ) x x) (g x) ≤ 2 * C * φ.rOut := by
  have h := convex_radial_bounds ((normSmooth_contDiff g φ).differentiable (by norm_num))
    (normSmooth_convex g φ) x
  have hx := normSmooth_dist_le g φ hC x
  have h0 := normSmooth_dist_le g φ hC 0
  have h2 := normSmooth_dist_le g φ hC ((2 : ℝ) • x)
  rw [Real.dist_eq, abs_le] at hx h0 h2 ⊢
  simp only [map_zero, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h0 h2
  constructor <;> linarith

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.NormCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal RealInnerProductSpace Pointwise
namespace PettyProjection.Spherical

lemma rotDeriv_comp_scalar {n : ℕ} (T : Space n →L[ℝ] Space n)
    {f : Space n → ℝ} {G : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hG : Differentiable ℝ G) (x : Space n) :
    rotDeriv T (G ∘ f) x = deriv G (f x) * rotDeriv T f x := by
  have h := (hG (f x)).hasDerivAt.comp_hasFDerivAt x (hf x).hasFDerivAt
  simp only [rotDeriv, h.fderiv, smul_apply, smul_eq_mul]

lemma energy_comp_relation {n : ℕ} (f : Space n → ℝ) (G I : ℝ → ℝ) (b : ℝ)
    (hf : Differentiable ℝ f) (hG : Differentiable ℝ G) (hI : Differentiable ℝ I)
    (hrel : ∀ z, deriv G z ^ 2 = b ^ 2 * deriv I z) :
    energy (G ∘ f) (G ∘ f) = b ^ 2 * energy (I ∘ f) f := by
  unfold energy
  simp_rw [rotDeriv_comp_scalar _ hf hG, rotDeriv_comp_scalar _ hf hI]
  have he (i j : Fin n) :
      (fun u : Sphere n => deriv G (f u) * rotDeriv (generator n i j) f u *
        (deriv G (f u) * rotDeriv (generator n i j) f u)) =
      (fun u : Sphere n => b ^ 2 *
        (deriv I (f u) * rotDeriv (generator n i j) f u * rotDeriv (generator n i j) f u)) := by
    funext u
    calc
      _ = deriv G (f u) ^ 2 * (rotDeriv (generator n i j) f u) ^ 2 := by ring
      _ = _ := by rw [hrel]; ring
  simp_rw [he, mean, integral_const_mul]
  simp only [← Finset.mul_sum]
  ring

lemma smooth_convex_energy_bound {n : ℕ} [NeZero n]
    {f : Space n → ℝ} {G I : ℝ → ℝ} {b : ℝ}
    (hf : ContDiff ℝ 2 f) (hc : ConvexOn ℝ univ f)
    (hG : ContDiff ℝ 1 G) (hI : ContDiff ℝ 1 I)
    (hpos : ∀ z, 0 ≤ I z) (hrel : ∀ z, deriv G z ^ 2 = b ^ 2 * deriv I z) :
    energy (G ∘ f) (G ∘ f) ≤ ((n : ℝ) - 1) * b ^ 2 *
      mean (fun u : Sphere n => I (f u) * fderiv ℝ f u u) := by
  have hfc : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hr := energy_comp_relation f G I b (hf.differentiable (by norm_num))
    (hG.differentiable (by norm_num)) (hI.differentiable (by norm_num)) hrel
  rw [hr]
  have hibp := mean_casimir (hI.comp hfc) hf
  have hcont : Continuous (fun u : Sphere n => I (f u) * casimir f u) := by
    apply (hI.continuous.comp (hf.continuous.comp continuous_subtype_val)).mul
    unfold casimir
    exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ =>
        (continuous_rotDeriv _ (contDiff_rotDeriv _ hf)).comp continuous_subtype_val)
  have hcont' : Continuous (fun u : Sphere n =>
      -((n : ℝ) - 1) * (I (f u) * fderiv ℝ f u u)) :=
    continuous_const.mul ((hI.continuous.comp (hf.continuous.comp continuous_subtype_val)).mul
      ((hf.continuous_fderiv (by norm_num)).comp continuous_subtype_val |>.clm_apply continuous_subtype_val))
  have hle : mean (fun u : Sphere n => -((n : ℝ) - 1) * (I (f u) * fderiv ℝ f u u)) ≤
      mean (fun u : Sphere n => I (f u) * casimir f u) := by
    apply integral_mono (continuous_integrable hcont') (continuous_integrable hcont)
    intro u
    have h := mul_le_mul_of_nonneg_left (convex_casimir_lower hf hc u) (hpos (f u))
    nlinarith
  rw [mean, integral_const_mul] at hle
  change -((n : ℝ) - 1) * mean (fun u : Sphere n => I (f u) * fderiv ℝ f u u) ≤ _ at hle
  simp only [Function.comp_apply] at hibp
  rw [hibp] at hle
  have h := mul_le_mul_of_nonneg_left hle (sq_nonneg b)
  nlinarith

lemma smooth_convex_curvature {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {f : Space n → ℝ} {G I : ℝ → ℝ} {b : ℝ}
    (hf : ContDiff ℝ 2 f) (hc : ConvexOn ℝ univ f) (heven : Function.Even f)
    (hG : ContDiff ℝ 1 G) (hI : ContDiff ℝ 1 I)
    (hpos : ∀ z, 0 ≤ I z) (hrel : ∀ z, deriv G z ^ 2 = b ^ 2 * deriv I z) :
    (2 * n : ℝ) * variance (fun u : Sphere n => G (f u)) + (2 * n + 8 : ℝ) *
      ‖Q n (toH n (restrictContinuous (G ∘ f) (hG.continuous.comp hf.continuous)))‖ ^ 2 ≤
      ((n : ℝ) - 1) * b ^ 2 * mean (fun u : Sphere n => I (f u) * fderiv ℝ f u u) := by
  have he : Function.Even (G ∘ f) := fun x => by simp only [Function.comp_apply]; rw [heven x]
  exact (even_spectral_gap hn (hG.comp (hf.of_le (by norm_num))) he).trans
    (smooth_convex_energy_bound hf hc hG hI hpos hrel)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Pointwise Convolution
namespace PettyProjection.Spherical

lemma continuous_mean {n : ℕ} [NeZero n] :
    Continuous (fun f : C(Sphere n, ℝ) => mean f) := by
  have he : (fun f : C(Sphere n, ℝ) => mean f) =
      (fun f => ⟪toH n f, toH n (ContinuousMap.const (Sphere n) 1)⟫) := by
    funext f
    rw [inner_toH]
    simp only [ContinuousMap.const_apply, mul_one]
  rw [he]
  exact (toH n).continuous.inner continuous_const

lemma continuous_variance {n : ℕ} [NeZero n] :
    Continuous (fun f : C(Sphere n, ℝ) => variance f) := by
  have he : (fun f : C(Sphere n, ℝ) => variance f) =
      (fun f => ‖toH n f‖ ^ 2 - (mean f) ^ 2) := by
    funext f
    rw [norm_toH_sq]
    rfl
  rw [he]
  exact ((toH n).continuous.norm.pow 2).sub (continuous_mean.pow 2)

lemma seminorm_approximation {n : ℕ} (g : Seminorm ℝ (Space n)) :
    ∃ F R : ℕ → C(Sphere n, ℝ),
      (∀ j, F j = restrictContinuous (normSmooth g (shrinkingBump n j))
        (normSmooth_contDiff g _).continuous) ∧
      (∀ j u, R j u = fderiv ℝ (normSmooth g (shrinkingBump n j)) u u) ∧
      Tendsto F atTop (𝓝 (restrictContinuous g (seminorm_continuous n g))) ∧
      Tendsto R atTop (𝓝 (restrictContinuous g (seminorm_continuous n g))) := by
  let F : ℕ → C(Sphere n, ℝ) := fun j => restrictContinuous
    (normSmooth g (shrinkingBump n j)) (normSmooth_contDiff g _).continuous
  let R : ℕ → C(Sphere n, ℝ) := fun j => ⟨fun u =>
    fderiv ℝ (normSmooth g (shrinkingBump n j)) u u,
    ((normSmooth_contDiff g _).continuous_fderiv (by norm_num)).comp continuous_subtype_val
      |>.clm_apply continuous_subtype_val⟩
  refine ⟨F, R, fun _ => rfl, fun _ _ => rfl, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := seminorm_lipschitz n g
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun j =>
      (ContinuousMap.dist_le (mul_nonneg C.coe_nonneg (shrinkingBump n j).rOut_pos.le)).mpr
        (fun u => normSmooth_dist_le g _ hC u))
      (by simpa only [mul_zero, shrinkingBump] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (C : ℝ))
  · obtain ⟨C, hC⟩ := seminorm_lipschitz n g
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun j =>
      (ContinuousMap.dist_le (mul_nonneg (mul_nonneg (by norm_num) C.coe_nonneg)
        (shrinkingBump n j).rOut_pos.le)).mpr
        (fun u => normSmooth_radial_dist_le g _ hC u))
      (by simpa only [mul_zero, shrinkingBump] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * C : ℝ))

/-- The nonsmooth curvature inequality, proved by actual even convolution of
an arbitrary seminorm. No smoothness, homogeneity of approximants, or assumed
spectral interface is required. -/
theorem seminorm_curvature {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    (g : Seminorm ℝ (Space n)) {G I : ℝ → ℝ} {b : ℝ}
    (hG : ContDiff ℝ 1 G) (hI : ContDiff ℝ 1 I)
    (hpos : ∀ z, 0 ≤ I z) (hrel : ∀ z, deriv G z ^ 2 = b ^ 2 * deriv I z) :
    (2 * n : ℝ) * variance (fun u : Sphere n => G (g u)) + (2 * n + 8 : ℝ) *
      ‖Q n (toH n (restrictContinuous (G ∘ g) (hG.continuous.comp (seminorm_continuous n g))))‖ ^ 2 ≤
      ((n : ℝ) - 1) * b ^ 2 * mean (fun u : Sphere n => I (g u) * g u) := by
  obtain ⟨F, R, hF, hR, hFt, hRt⟩ := seminorm_approximation g
  let Gc : C(ℝ, ℝ) := ⟨G, hG.continuous⟩
  let Ic : C(ℝ, ℝ) := ⟨I, hI.continuous⟩
  have hGt := Gc.continuous_postcomp.tendsto _ |>.comp hFt
  have hIt := Ic.continuous_postcomp.tendsto _ |>.comp hFt
  have hl := (continuous_variance.tendsto _ |>.comp hGt).const_mul (2 * n : ℝ)
  have hq := (((Q n).continuous.comp (toH n).continuous).tendsto _ |>.comp hGt).norm.pow 2
  have hr := (continuous_mean.tendsto _ |>.comp (hIt.mul hRt)).const_mul
    (((n : ℝ) - 1) * b ^ 2)
  apply le_of_tendsto_of_tendsto' (hl.add (hq.const_mul (2 * n + 8 : ℝ))) hr
  intro j
  have h := smooth_convex_curvature hn (normSmooth_contDiff g (shrinkingBump n j))
    (normSmooth_convex g _) (normSmooth_even g _) hG hI hpos hrel
  simp only [Function.comp_apply, hF, hR, Gc, Ic, ContinuousMap.coe_mk,
    ContinuousMap.coe_mul, Pi.mul_def,
    ContinuousMap.comp, restrictContinuous]
  convert h using 1 <;> rfl

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.ScalarBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PettyProjection.Scalar

/-- A second-order lower bound for inverse powers, valid in every dimension.
This is the low-z convexity estimate. -/
lemma inverse_pow_lower (n : ℕ) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    1 + n * (1 - z) + (n : ℝ) * (n + 1) / 2 * (1 - z)^2 ≤ (z⁻¹)^n := by
  have hx : 0 ≤ 1 - z := sub_nonneg.mpr hz1
  have hinv : 1 + (1 - z) + (1 - z)^2 ≤ z⁻¹ := by
    rw [← one_div z]
    apply (le_div_iff₀ hz).2
    nlinarith [mul_nonneg (sq_nonneg (1-z)) hx]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hprod := mul_le_mul ih hinv (by positivity : 0 ≤ 1 + (1-z) + (1-z)^2)
      (by positivity : 0 ≤ (z⁻¹)^n)
    push_cast
    calc
      1 + ((n : ℝ) + 1) * (1 - z) + ((n : ℝ) + 1) * ((n : ℝ) + 1 + 1) / 2 * (1 - z)^2
          ≤ (1 + (n : ℝ) * (1-z) + (n : ℝ) * (n+1) / 2 * (1-z)^2) *
            (1 + (1-z) + (1-z)^2) := by
              nlinarith [mul_nonneg (by positivity : 0 ≤ (n : ℝ))
                  (mul_nonneg (sq_nonneg (1-z)) hx),
                mul_nonneg (by positivity : 0 ≤ (n : ℝ) * (n+1) / 2)
                  (mul_nonneg (sq_nonneg (1-z)) hx),
                mul_nonneg (by positivity : 0 ≤ (n : ℝ) * (n+1) / 2)
                  (sq_nonneg ((1-z)^2))]
      _ ≤ _ := hprod

lemma coefficient_pos (n : ℕ) : 0 < coefficient n := by
  unfold coefficient
  split_ifs <;> positivity

lemma beta_pos (n : ℕ) : 0 < beta n := by
  unfold beta
  split_ifs <;> norm_num

lemma beta_lt_one (n : ℕ) : beta n < 1 := by
  unfold beta
  split_ifs <;> norm_num

lemma weight_pos (n : ℕ) : 0 < weight n := by
  unfold weight
  split_ifs <;> norm_num

lemma weight_lt_one (n : ℕ) : weight n < 1 := by
  unfold weight
  split_ifs <;> norm_num

/-- Exact positivity margin on the low-z interval in dimensions at least seven. -/
lemma large_local_margin {r : ℝ} (hr : 7 ≤ r) :
    0 < r + 3 - 8 * (r^2 + 5*r + 7) / ((r+1)*(r+3)) := by
  have hden : 0 < (r+1)*(r+3) := by positivity
  have ht : 0 ≤ r - 7 := by linarith
  have hpoly : 0 < r^3 - r^2 - 25*r - 47 := by
    have hcert : r^3-r^2-25*r-47 =
        (r-7)^3 + 20*(r-7)^2 + 108*(r-7) + 72 := by ring
    rw [hcert]
    positivity
  have heq : r+3-8*(r^2+5*r+7)/((r+1)*(r+3)) =
      (r^3-r^2-25*r-47)/((r+1)*(r+3)) := by
    field_simp
    ring
  rw [heq]
  exact div_pos hpoly hden

/-- Scalar mean bound, including every dimension. -/
lemma mean_bound (n : ℕ) (hn : 4 ≤ n) :
    coefficient n * (2*n*beta n^2 / (weight n * (2*n+8)) -
      (1-beta n)^2 / (1-weight n)) ≤
      (2*(exponent n : ℝ)-1) / (exponent n : ℝ)^2 := by
  by_cases h4 : n = 4
  · subst n
    norm_num [coefficient, beta, weight, exponent]
  by_cases h5 : n = 5
  · subst n
    norm_num [coefficient, beta, weight, exponent]
  by_cases h6 : n = 6
  · subst n
    norm_num [coefficient, beta, weight, exponent]
  have hn7 : 7 ≤ n := by omega
  have hr : 7 ≤ (n : ℝ) := by exact_mod_cast hn7
  simp only [coefficient, beta, weight, exponent, h4, h5, h6,
    ite_false, or_self, Nat.cast_ofNat]
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
  have h4' : (n : ℝ) + 4 ≠ 0 := by positivity
  have hd : 0 < 36*((n : ℝ)+1)*(n+3)*(n+4) := by positivity
  have hcert : 3/4 - ( ((n : ℝ)^2+5*n+7) / ((n+1)*(n+3)) *
      (2*n*(2/3)^2 / (1/2*(2*n+8)) - (1-2/3)^2/(1-1/2))) =
      (3*(n : ℝ)^3+128*n^2+505*n+548) / (36*(n+1)*(n+3)*(n+4)) := by
    field_simp
    ring
  have hpos : 0 < 3*(n : ℝ)^3+128*n^2+505*n+548 := by positivity
  have := div_pos hpos hd
  rw [← hcert] at this
  norm_num only [OfNat.ofNat_ne_zero, Nat.reduceAdd, Nat.reduceMul] at *
  linarith

lemma local_margin (n : ℕ) (hn : 4 ≤ n) :
    coefficient n * (exponent n : ℝ)^2 / (1 - weight n) <
      n + 2 * (exponent n : ℝ) - 1 := by
  by_cases h4 : n = 4
  · subst n
    norm_num [coefficient, weight, exponent]
  by_cases h5 : n = 5
  · subst n
    norm_num [coefficient, weight, exponent]
  by_cases h6 : n = 6
  · subst n
    norm_num [coefficient, weight, exponent]
  have hn7 : 7 ≤ n := by omega
  have hr : 7 ≤ (n : ℝ) := by exact_mod_cast hn7
  have h := large_local_margin hr
  simp only [coefficient, weight, exponent, h4, h5, h6, ite_false, or_self,
    Nat.cast_ofNat]
  convert (sub_pos.mp h) using 1 <;> ring

lemma low_W_bound (n : ℕ) (hn : 4 ≤ n) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    (n + 2 * (exponent n : ℝ) - 1) * (z-1)^2 ≤ 2 * W n z := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp := inverse_pow_lower n hz hz1
  have he : -(z-1) + ((n : ℝ)+1)/2 * (z-1)^2 ≤ e n z := by
    unfold e
    apply (le_div_iff₀ hn0).2
    nlinarith [hp]
  by_cases h4 : n = 4
  · subst n
    norm_num only [W, exponent, ite_true, pow_one, Nat.reduceSub, pow_zero,
      Nat.cast_one, Nat.cast_ofNat] at ⊢ he
    nlinarith
  · simp only [W, exponent, h4, ite_false, Nat.reduceSub, pow_one, Nat.cast_ofNat]
    nlinarith

lemma low_D_square (n : ℕ) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    (z ^ exponent n - 1)^2 ≤ (exponent n : ℝ)^2 * (z-1)^2 := by
  by_cases h4 : n = 4
  · simp [exponent, h4]
  · simp only [exponent, h4, ite_false, Nat.cast_ofNat]
    have hs : (z+1)^2 ≤ 4 := by nlinarith
    have := mul_le_mul_of_nonneg_left hs (sq_nonneg (z-1))
    nlinarith

lemma low_pointwise (n : ℕ) (hn : 4 ≤ n) {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    L n z ≤ 2 * W n z ∧ (L n z = 2 * W n z ↔ z = 1) := by
  have hnot : ¬ 1 < z := not_lt.mpr hz1
  have hwt : 0 < 1 - weight n := sub_pos.mpr (weight_lt_one n)
  have hc : 0 < coefficient n / (1-weight n) := div_pos (coefficient_pos n) hwt
  have hL : L n z = coefficient n / (1-weight n) * (z ^ exponent n - 1)^2 := by
    simp [L, D, G, I, hnot, div_mul_eq_mul_div]
    ring
  by_cases heq : z = 1
  · subst z
    simp [L, G, I, D, W, e]
  have hsq : 0 < (z-1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr heq)
  have hlt : L n z < 2 * W n z := calc
    L n z = coefficient n / (1-weight n) * (z ^ exponent n - 1)^2 := hL
    _ ≤ coefficient n / (1-weight n) * ((exponent n : ℝ)^2 * (z-1)^2) :=
      mul_le_mul_of_nonneg_left (low_D_square n hz hz1) hc.le
    _ = (coefficient n * (exponent n : ℝ)^2 / (1-weight n)) * (z-1)^2 := by ring
    _ < (n + 2 * (exponent n : ℝ) - 1) * (z-1)^2 :=
      mul_lt_mul_of_pos_right (local_margin n hn) hsq
    _ ≤ 2 * W n z := low_W_bound n hn hz hz1
  exact ⟨hlt.le, iff_of_false (ne_of_lt hlt) heq⟩

lemma certificate_4 {z : ℝ} (hz : 1 < z) :
    2880 * z^8 * (2 * W 4 z - L 4 z) = P4 z := by
  have hz0 : z ≠ 0 := by linarith
  simp only [W, L, D, G, I, M, e, exponent, coefficient, weight, beta, P4]
  norm_num [hz]
  field_simp
  ring

lemma U4_pos (x : ℝ) : 0 < U4 x := by
  have h1 : 1446*x ≤ 400 + 1400*x^2 := by
    nlinarith [sq_nonneg (2800*x-1446)]
  have h2 : 8111*x^2 ≤ 1000 + 17052*x^4 := by
    nlinarith [sq_nonneg (34104*x^2-8111)]
  dsimp [U4]
  linarith

lemma P4_pos {z : ℝ} (hz : 1 < z) : 0 < P4 z := by
  let x := z-1
  have hx : 0 < x := sub_pos.mpr hz
  have heq : P4 z = x^2 * (U4 x + (462 * x^8 + 3637 * x^7 + 12036 * x^6 + 20796 * x^5 + 1173 * x^3)) := by
    dsimp [P4, U4, x]
    ring
  rw [heq]
  have hu := U4_pos x
  positivity

lemma high_pointwise_4 {z : ℝ} (hz : 1 < z) : L 4 z < 2 * W 4 z := by
  have h := P4_pos hz
  rw [← certificate_4 hz] at h
  have hp : 0 < (2880 : ℝ) * z^8 := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp h)

lemma certificate_5 {z : ℝ} (hz : 1 < z) :
    712800 * z^10 * (2 * W 5 z - L 5 z) = P5 z := by
  have hz0 : z ≠ 0 := by linarith
  simp only [W, L, D, G, I, M, e, exponent, coefficient, weight, beta, P5]
  norm_num [hz]
  field_simp
  ring

lemma U5_pos (x : ℝ) : 0 < U5 x := by
  have h1 : 1505900*x ≤ 200000 + 2900000*x^2 := by
    nlinarith [sq_nonneg (5800000*x-1505900)]
  have h2 : 8702775*x^2 ≤ 230000 + 86314305*x^4 := by
    nlinarith [sq_nonneg (172628610*x^2-8702775)]
  dsimp [U5]
  linarith

lemma P5_pos {z : ℝ} (hz : 1 < z) : 0 < P5 z := by
  let x := z-1
  have hx : 0 < x := sub_pos.mpr hz
  have heq : P5 z = x^2 * (U5 x + (151525 * x^12 + 2121350 * x^11 + 13515205 * x^10 + 51191460 * x^9 + 127070262 * x^8 + 215105220 * x^7 + 249497490 * x^6 + 191506920 * x^5 + 12849430 * x^3)) := by
    dsimp [P5, U5, x]
    ring
  rw [heq]
  have hu := U5_pos x
  positivity

lemma high_pointwise_5 {z : ℝ} (hz : 1 < z) : L 5 z < 2 * W 5 z := by
  have h := P5_pos hz
  rw [← certificate_5 hz] at h
  have hp : 0 < (712800 : ℝ) * z^10 := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp h)

lemma certificate_6 {z : ℝ} (hz : 1 < z) :
    221130 * z^12 * (2 * W 6 z - L 6 z) = P6 z := by
  have hz0 : z ≠ 0 := by linarith
  simp only [W, L, D, G, I, M, e, exponent, coefficient, weight, beta, P6]
  norm_num [hz]
  field_simp
  ring

lemma U6_pos (x : ℝ) : 0 < U6 x := by
  dsimp [U6]
  nlinarith [sq_nonneg (102538904*x^2-132249)]

lemma P6_pos {z : ℝ} (hz : 1 < z) : 0 < P6 z := by
  let x := z-1
  have hx : 0 < x := sub_pos.mpr hz
  have heq : P6 z = x^2 * (U6 x + (48399 * x^14 + 774384 * x^13 + 5731986 * x^12 + 25822920 * x^11 + 78631735 * x^10 + 170208636 * x^9 + 268133580 * x^8 + 308783332 * x^7 + 256021935 * x^6 + 146058120 * x^5 + 7800780 * x^3 + 679380 * x)) := by
    dsimp [P6, U6, x]
    ring
  rw [heq]
  have hu := U6_pos x
  positivity

lemma high_pointwise_6 {z : ℝ} (hz : 1 < z) : L 6 z < 2 * W 6 z := by
  have h := P6_pos hz
  rw [← certificate_6 hz] at h
  have hp : 0 < (221130 : ℝ) * z^12 := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp h)

lemma certificate_7 {z : ℝ} (hz : 1 < z) :
    138600 * z^14 * (2 * W 7 z - L 7 z) = P7 z := by
  have hz0 : z ≠ 0 := by linarith
  simp only [W, L, D, G, I, M, e, exponent, coefficient, weight, beta, P7]
  norm_num [hz]
  field_simp
  ring

lemma P7_pos {z : ℝ} (hz : 1 < z) : 0 < P7 z := by
  let x := z-1
  have hx : 0 < x := sub_pos.mpr hz
  have heq : P7 z = x^2 * (3185 * x^16 + 57330 * x^15 + 565215 * x^14 + 3660048 * x^13 + 16414605 * x^12 + 52863510 * x^11 + 125758815 * x^10 + 225405180 * x^9 + 307786479 * x^8 + 320870550 * x^7 + 253378125 * x^6 + 148489200 * x^5 + 62263215 * x^4 + 17740674 * x^3 + 3396645 * x^2 + 598500 * x + 124740) := by
    dsimp [P7, x]
    ring
  rw [heq]
  positivity

lemma high_pointwise_7 {z : ℝ} (hz : 1 < z) : L 7 z < 2 * W 7 z := by
  have h := P7_pos hz
  rw [← certificate_7 hz] at h
  have hp : 0 < (138600 : ℝ) * z^14 := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp h)

lemma certificate_8 {z : ℝ} (hz : 1 < z) :
    181764 * z^16 * (2 * W 8 z - L 8 z) = P8 z := by
  have hz0 : z ≠ 0 := by linarith
  simp only [W, L, D, G, I, M, e, exponent, coefficient, weight, beta, P8]
  norm_num [hz]
  field_simp
  ring

lemma P8_pos {z : ℝ} (hz : 1 < z) : 0 < P8 z := by
  let x := z-1
  have hx : 0 < x := sub_pos.mpr hz
  have heq : P8 z = x^2 * (5032 * x^18 + 100640 * x^17 + 1062976 * x^16 + 7415480 * x^15 + 36699889 * x^14 + 134016848 * x^13 + 371287480 * x^12 + 796445648 * x^11 + 1341571660 * x^10 + 1789629712 * x^9 + 1896594800 * x^8 + 1593208720 * x^7 + 1052388995 * x^6 + 539061976 * x^5 + 210340388 * x^4 + 61812136 * x^3 + 14025170 * x^2 + 2645608 * x + 369036) := by
    dsimp [P8, x]
    ring
  rw [heq]
  positivity

lemma high_pointwise_8 {z : ℝ} (hz : 1 < z) : L 8 z < 2 * W 8 z := by
  have h := P8_pos hz
  rw [← certificate_8 hz] at h
  have hp : 0 < (181764 : ℝ) * z^16 := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp h)

lemma certificate_9 {z : ℝ} (hz : 1 < z) :
    568620 * z^18 * (2 * W 9 z - L 9 z) = P9 z := by
  have hz0 : z ≠ 0 := by linarith
  simp only [W, L, D, G, I, M, e, exponent, coefficient, weight, beta, P9]
  norm_num [hz]
  field_simp
  ring

lemma P9_pos {z : ℝ} (hz : 1 < z) : 0 < P9 z := by
  let x := z-1
  have hx : 0 < x := sub_pos.mpr hz
  have heq : P9 z = x^2 * (17955 * x^20 + 395010 * x^19 + 4492431 * x^18 + 33775884 * x^17 + 182612144 * x^16 + 741405888 * x^15 + 2325627540 * x^14 + 5752968096 * x^13 + 11391705882 * x^12 + 18245048652 * x^11 + 23789022114 * x^10 + 25324311168 * x^9 + 21996503100 * x^8 + 15523044480 * x^7 + 8829652644 * x^6 + 4002804432 * x^5 + 1428705963 * x^4 + 398939634 * x^3 + 87942807 * x^2 + 15343236 * x + 1781676) := by
    dsimp [P9, x]
    ring
  rw [heq]
  positivity

lemma high_pointwise_9 {z : ℝ} (hz : 1 < z) : L 9 z < 2 * W 9 z := by
  have h := P9_pos hz
  rw [← certificate_9 hz] at h
  have hp : 0 < (568620 : ℝ) * z^18 := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp h)

open Finset

/-- The exact coefficient comparison used in the all-dimensional scalar estimate. -/
lemma choose_double (n j : ℕ) : 2^j * n.choose j ≤ (2*n).choose j := by
  induction n generalizing j with
  | zero => cases j <;> simp
  | succ n ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [Nat.choose_succ_succ]
      calc
        2^(j+1)*(n.choose j + n.choose (j+1)) =
            2*(2^j*n.choose j) + 2^(j+1)*n.choose (j+1) := by ring
        _ ≤ 2*(2*n).choose j + (2*n).choose (j+1) :=
          Nat.add_le_add (Nat.mul_le_mul_left 2 (ih j)) (ih (j+1))
        _ ≤ (2*(n+1)).choose (j+1) := by
          have hh := Nat.choose_le_succ (2*n) j
          have heq : 2*(n+1) = (2*n+1)+1 := by omega
          rw [heq, Nat.choose_succ_succ, Nat.choose_succ_succ]
          simp only [Nat.succ_eq_add_one] at hh ⊢
          omega

lemma choose_double_cubic {n j : ℕ} (hj : 3 ≤ j) :
    8 * (n.choose j : ℝ) ≤ ((2*n).choose j : ℝ) := by
  have hp : 8 ≤ 2^j := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hj
    norm_num at this ⊢
    exact this
  exact_mod_cast le_trans (Nat.mul_le_mul_right (n.choose j) hp) (choose_double n j)

lemma tail_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ tail n x := by
  apply sum_nonneg
  intro j _
  split_ifs <;> positivity

lemma tail_expansion (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    (1+x)^n = 1 + n*x + (n.choose 2 : ℝ)*x^2 + tail n x := by
  have heq : n+1 = 3 + (n-2) := by omega
  have hp := add_pow x (1:ℝ) n
  simp only [one_pow,mul_one] at hp
  rw [add_comm] at hp
  rw [hp]
  simp only [tail]
  rw [heq, sum_range_add, sum_range_add]
  have hsum : (∑ j ∈ range (n-2), x^(3+j)*(n.choose (3+j) : ℝ)) =
      ∑ j ∈ range (n-2), if 3 ≤ 3+j then (n.choose (3+j) : ℝ)*x^(3+j) else 0 := by
    apply sum_congr rfl
    intro j _
    simp [mul_comm]
  rw [hsum]
  norm_num [sum_range_succ, Nat.choose_one_right]
  ring

lemma tail_double (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    8 * tail n x ≤ tail (2*n) x := by
  let f : ℕ → ℝ := fun j => if 3 ≤ j then (n.choose j : ℝ)*x^j else 0
  have hzero : ∀ j, n+1 ≤ j → f j = 0 := by
    intro j hj
    unfold f
    rw [Nat.choose_eq_zero_of_lt (by omega : n < j)]
    simp
  have hext : tail n x = ∑ j ∈ range (2*n+1), f j := by
    change (∑ j ∈ range (n+1), f j) = _
    have heq : 2*n+1 = (n+1)+n := by omega
    rw [heq, sum_range_add (f := f) (n+1) n]
    have : ∑ j ∈ range n, f (n+1+j) = 0 := by
      apply sum_eq_zero
      intro j _
      exact hzero _ (by omega)
    change (∑ j ∈ range (n+1), f j) = _
    rw [this,add_zero]
  rw [hext, mul_sum]
  unfold tail
  apply sum_le_sum
  intro j _
  dsimp [f]
  split_ifs with hj
  · have h := mul_le_mul_of_nonneg_right (choose_double_cubic (n:=n) hj)
      (pow_nonneg hx j)
    nlinarith only [h]
  · simp

/-- Positivity mechanism for the all-dimensional polynomial.
Cancellation of its first two coefficients leaves a positive quadratic term;
all later coefficients are controlled by the doubled binomial comparison. -/
lemma shifted_polynomial_pos (n : ℕ) (hn : 2 ≤ n) {x : ℝ} (hx : 0 < x)
    (a b c d e u v w t : ℝ)
    (hzero : a+u+t=0) (hone : 2*n*a+b+n*u+v=0)
    (htwo : 0 < ((2*n).choose 2 : ℝ)*a+2*n*b+c+(n.choose 2 : ℝ)*u+n*v+w)
    (ha : 0 ≤ a) (hau : 0 ≤ 8*a+u)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hv : 0 ≤ v) (hw : 0 ≤ w) :
    0 < (1+x)^(2*n)*(a+b*x+c*x^2+d*x^3+e*x^4)+
      (1+x)^n*(u+v*x+w*x^2)+t := by
  have htn := tail_nonneg n hx.le
  have ht2n := tail_nonneg (2*n) hx.le
  have hdouble : 0 ≤ tail (2*n) x - 8*tail n x := sub_nonneg.mpr (tail_double n hx.le)
  have hmain : 0 < (((2*n).choose 2 : ℝ)*a+2*n*b+c+(n.choose 2 : ℝ)*u+n*v+w)*x^2 :=
    mul_pos htwo (sq_pos_of_pos hx)
  have hrest : 0 ≤
      a*(tail (2*n) x-8*tail n x) + (8*a+u)*tail n x +
      b*x*(((2*n).choose 2 : ℝ)*x^2+tail (2*n) x) +
      c*x^2*(2*n*x+((2*n).choose 2 : ℝ)*x^2+tail (2*n) x) +
      d*x^3*(1+x)^(2*n) + e*x^4*(1+x)^(2*n) +
      v*x*((n.choose 2 : ℝ)*x^2+tail n x) +
      w*x^2*(n*x+(n.choose 2 : ℝ)*x^2+tail n x) := by positivity
  have hidentity : (1+x)^(2*n)*(a+b*x+c*x^2+d*x^3+e*x^4)+
      (1+x)^n*(u+v*x+w*x^2)+t =
      (((2*n).choose 2 : ℝ)*a+2*n*b+c+(n.choose 2 : ℝ)*u+n*v+w)*x^2 +
      (a*(tail (2*n) x-8*tail n x) + (8*a+u)*tail n x +
      b*x*(((2*n).choose 2 : ℝ)*x^2+tail (2*n) x) +
      c*x^2*(2*n*x+((2*n).choose 2 : ℝ)*x^2+tail (2*n) x) +
      d*x^3*(1+x)^(2*n) + e*x^4*(1+x)^(2*n) +
      v*x*((n.choose 2 : ℝ)*x^2+tail n x) +
      w*x^2*(n*x+(n.choose 2 : ℝ)*x^2+tail n x)) := by
    rw [tail_expansion n hn x, tail_expansion (2*n) (by omega) x]
    have ht : t = -a-u := by linarith
    have hb' : b = -2*n*a-n*u-v := by linarith
    rw [ht, hb']
    push_cast
    ring
  rw [hidentity]
  exact add_pos_of_pos_of_nonneg hmain hrest

lemma V0_pos {r : ℝ} (hr : 10 ≤ r) : 0 < V0 r := by
  have ht : 0 ≤ r-10 := by linarith
  have heq : V0 r = 34*(r-10)^5+1605*(r-10)^4+28534*(r-10)^3+
      227319*(r-10)^2+698128*(r-10)+130692 := by unfold V0; ring
  rw [heq]
  positivity

lemma V1_pos {r : ℝ} (hr : 10 ≤ r) : 0 < V1 r := by
  have ht : 0 ≤ r-10 := by linarith
  have heq : V1 r = 2*(r-10)^5+109*(r-10)^4+2198*(r-10)^3+
      19695*(r-10)^2+69280*(r-10)+30852 := by unfold V1; ring
  rw [heq]
  positivity

lemma V2_pos {r : ℝ} (hr : 7 ≤ r) : 0 < V2 r := by
  have ht : 0 ≤ r-7 := by linarith
  have heq : V2 r = 5*(r-7)^3+113*(r-7)^2+806*(r-7)+1764 := by unfold V2; ring
  rw [heq]
  positivity

lemma R0_pos {r : ℝ} (hr : 7 ≤ r) : 0 < R0 r := by
  have ht : 0 ≤ r-7 := by linarith
  have heq : R0 r = 7*(r-7)^4+204*(r-7)^3+2039*(r-7)^2+7414*(r-7)+4256 := by
    unfold R0
    ring
  rw [heq]
  positivity

lemma q0_identity {r : ℝ} (hr : 0 < r) :
    q0 r+r0 r/8 = V0 r/(4*r^2*(2*r+1)*(r^2+5*r+7)) := by
  unfold q0 r0 A4 A2 A1 A0 B2 B0 H largeC V0
  field_simp
  ring

lemma q1_identity {r : ℝ} (hr : 0 < r) :
    q1 r = 2*V1 r/(r*(2*r+1)*(r^2+5*r+7)) := by
  unfold q1 A4 A2 A1 H largeC V1
  field_simp
  ring

lemma q2_identity {r : ℝ} (hr : 0 < r) :
    q2 r = 2*(r+4)*V2 r/(r*(r^2+5*r+7)) := by
  unfold q2 A4 A2 H largeC V2
  field_simp
  ring

lemma r0_identity {r : ℝ} (hr : 0 < r) :
    r0 r = -2*R0 r/(r^2*(r^2+5*r+7)) := by
  unfold r0 B2 B0 H largeC R0
  field_simp
  ring

lemma large_signs {r : ℝ} (hr : 10 ≤ r) :
    0 < q0 r ∧ 0 < 8*q0 r+r0 r ∧ 0 < q1 r ∧ 0 < q2 r ∧
    0 < q3 r ∧ 0 < q4 r ∧ 0 < r1 r ∧ 0 < r2 r := by
  have hr0 : 0 < r := by linarith
  have hr7 : 7 ≤ r := by linarith
  have hs : 0 < q0 r+r0 r/8 := by
    rw [q0_identity hr0]
    exact div_pos (V0_pos hr) (by positivity)
  have hneg : r0 r < 0 := by
    rw [r0_identity hr0]
    exact div_neg_of_neg_of_pos (by nlinarith [R0_pos hr7]) (by positivity)
  have h8 : 0 < 2*r-8 := by linarith
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [q1_identity hr0]
    exact div_pos (mul_pos (by norm_num) (V1_pos hr)) (by positivity)
  · rw [q2_identity hr0]
    exact div_pos (mul_pos (by positivity) (V2_pos hr7)) (by positivity)
  · unfold q3 A4
    positivity
  · unfold q4 A4
    positivity
  · unfold r1 B2
    positivity
  · unfold r2 B2
    positivity

lemma constant_vanish {r : ℝ} (hr : 0 < r) : q0 r + r0 r + T0 r = 0 := by
  unfold q0 r0 A4 A2 A1 A0 B2 B0 T0 H largeC
  field_simp
  ring

lemma linear_vanish {r : ℝ} (hr : 0 < r) :
    2*r*q0 r + q1 r + r*r0 r + r1 r = 0 := by
  unfold q0 q1 r0 r1 A4 A2 A1 A0 B2 B0 H largeC
  field_simp
  ring

lemma quadratic_identity {r : ℝ} (hr : 0 < r) :
    r*(2*r-1)*q0 r + 2*r*q1 r + q2 r + r*(r-1)/2*r0 r+r*r1 r+r2 r =
      9*(r+4)/largeC r*(r+3-8*largeC r) := by
  unfold q0 q1 q2 r0 r1 r2 A4 A2 A1 A0 B2 B0 H largeC
  field_simp
  ring

lemma large_polynomial_pos (n : ℕ) (hn : 10 ≤ n) {z : ℝ} (hz : 1 < z) :
    0 < z^(2*n)*(A4 n*z^4+A2 n*z^2+A1 n*z+A0 n)+
      z^n*(B2 n*z^2+B0 n)+T0 n := by
  have hr : 10 ≤ (n : ℝ) := by exact_mod_cast hn
  have hr0 : 0 < (n : ℝ) := by linarith
  obtain ⟨hq0,hq0r0,hq1,hq2,hq3,hq4,hr1,hr2⟩ := large_signs hr
  have hc : 0 < largeC n := by unfold largeC; positivity
  have hmargin : 0 < (n : ℝ)+3-8*largeC n := by
    have hm := large_local_margin (r := (n : ℝ)) (by linarith)
    unfold largeC
    convert hm using 1; ring
  have htwo : 0 < (((2*n).choose 2 : ℕ) : ℝ)*q0 n+2*n*q1 n+q2 n+
      (n.choose 2 : ℝ)*r0 n+n*r1 n+r2 n := by
    rw [Nat.cast_choose_two ℝ, Nat.cast_choose_two ℝ]
    push_cast
    have heq : (2*(n:ℝ)*(2*n-1)/2*q0 n+2*n*q1 n+q2 n+
        n*(n-1)/2*r0 n+n*r1 n+r2 n) =
        9*(n+4)/largeC n*(n+3-8*largeC n) := by
      convert quadratic_identity hr0 using 1; ring
    rw [heq]
    positivity
  have hh := shifted_polynomial_pos n (by omega) (sub_pos.mpr hz)
    (q0 n) (q1 n) (q2 n) (q3 n) (q4 n) (r0 n) (r1 n) (r2 n) (T0 n)
    (constant_vanish hr0) (linear_vanish hr0) htwo hq0.le hq0r0.le
    hq1.le hq2.le hq3.le hq4.le hr1.le hr2.le
  have heq : z^(2*n)*(A4 n*z^4+A2 n*z^2+A1 n*z+A0 n)+
      z^n*(B2 n*z^2+B0 n)+T0 n =
      (1+(z-1))^(2*n)*(q0 n+q1 n*(z-1)+q2 n*(z-1)^2+q3 n*(z-1)^3+q4 n*(z-1)^4)+
      (1+(z-1))^n*(r0 n+r1 n*(z-1)+r2 n*(z-1)^2)+T0 n := by
    rw [show 1+(z-1)=z by ring]
    unfold q0 q1 q2 q3 q4 r0 r1 r2
    ring
  rw [heq]
  exact hh

lemma z_mul_inverse_pow_succ {z : ℝ} (hz : z ≠ 0) (m : ℕ) :
    z*(z⁻¹)^(m+1) = (z⁻¹)^m := by
  rw [pow_succ', ← mul_assoc, mul_inv_cancel₀ hz, one_mul]

lemma large_I_formula (n : ℕ) (hn : 7 ≤ n) {z : ℝ} (hz : 1 < z) :
    z*I n z = 4*((z^4-z)/3 - 2*(z-z^2*(z⁻¹)^n)/((n:ℝ)-1) +
      (z-((z⁻¹)^n)^2)/(2*n+1)) := by
  have h4 : n ≠ 4 := by omega
  have hz0 : z ≠ 0 := by linarith
  have hp : (z⁻¹)^(n+1-2) = z*(z⁻¹)^n := by
    have hv := z_mul_inverse_pow_succ hz0 (n+1-2)
    have he : n+1-2+1=n := by omega
    rw [he] at hv
    exact hv.symm
  have hd : z*(z⁻¹)^(2*n+1) = ((z⁻¹)^n)^2 := by
    rw [z_mul_inverse_pow_succ hz0, show 2*n=n*2 by omega, pow_mul]
  have hcast : ((n+1-2 : ℕ) : ℝ) = (n:ℝ)-1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_add]
    norm_num
    ring
  simp only [I, exponent, h4, ite_false, hz, ite_true, Nat.cast_ofNat,
    Nat.reduceMul, Nat.reduceSub, Nat.cast_add, Nat.cast_mul, Nat.cast_one, hcast]
  rw [hp]
  have hr1 : (n:ℝ)-1 ≠ 0 := by
    have hr : 7 ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hr2 : 2*(n:ℝ)+1 ≠ 0 := by positivity
  field_simp
  simp only [inv_eq_one_div] at hd
  linear_combination -12 * ((n : ℝ) - 1) * hd

lemma large_gap_formula (n : ℕ) (hn : 7 ≤ n) {z : ℝ} (hz : 1 < z) :
    9*((n:ℝ)+4)/coefficient n*(2*W n z-L n z) =
      A4 n*z^4+A2 n*z^2+A1 n*z+A0 n+
      (z⁻¹)^n*(B2 n*z^2+B0 n)+((z⁻¹)^n)^2*T0 n := by
  have h4 : n ≠ 4 := by omega
  have h56 : ¬(n=5 ∨ n=6) := by omega
  have hr : 7 ≤ (n:ℝ) := by exact_mod_cast hn
  have hr0 : 0 < (n:ℝ) := by linarith
  have hc : coefficient n = largeC n := by
    simp [coefficient, largeC, h4]
  have hc0 : largeC n ≠ 0 := by
    unfold largeC
    positivity
  have hI := large_I_formula n hn hz
  unfold L
  simp only [W, D, G, M, e, exponent, beta, weight, h4, h56, ite_false, hz,
    ite_true, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [hc]
  have heq : ((n:ℝ)-1)*(2/3)^2*z*I n z = ((n:ℝ)-1)*(2/3)^2*(z*I n z) := by ring
  rw [heq, hI]
  have hr1 : (n:ℝ)-1 ≠ 0 := by linarith
  unfold A4 A2 A1 A0 B2 B0 T0 H largeC
  field_simp [hr1]
  ring

lemma large_cleared_gap (n : ℕ) (hn : 7 ≤ n) {z : ℝ} (hz : 1 < z) :
    9*((n:ℝ)+4)/coefficient n*z^(2*n)*(2*W n z-L n z) =
      z^(2*n)*(A4 n*z^4+A2 n*z^2+A1 n*z+A0 n)+
      z^n*(B2 n*z^2+B0 n)+T0 n := by
  have hz0 : z ≠ 0 := by linarith
  have hzpow : z^n ≠ 0 := pow_ne_zero n hz0
  calc
    _ = z^(2*n)*(9*((n:ℝ)+4)/coefficient n*(2*W n z-L n z)) := by ring
    _ = _ := by
      rw [large_gap_formula n hn hz, show 2*n=n*2 by omega, pow_mul, inv_pow]
      field_simp

lemma high_pointwise_large (n : ℕ) (hn : 10 ≤ n) {z : ℝ} (hz : 1 < z) :
    L n z < 2*W n z := by
  have hp := large_polynomial_pos n hn hz
  rw [← large_cleared_gap n (by omega) hz] at hp
  have hc : 0 < 9*((n:ℝ)+4)/coefficient n*z^(2*n) := by
    have hc := coefficient_pos n
    positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hc).mp hp)

/-- The pointwise scalar estimate, including its exact equality
condition, in every dimension covered by the main theorem. -/
theorem pointwise (n : ℕ) (hn : 4 ≤ n) {z : ℝ} (hz : 0 < z) :
    L n z ≤ 2*W n z ∧ (L n z = 2*W n z ↔ z=1) := by
  by_cases hz1 : z ≤ 1
  · exact low_pointwise n hn hz hz1
  have hz' : 1 < z := lt_of_not_ge hz1
  have hlt : L n z < 2*W n z := by
    by_cases hn10 : 10 ≤ n
    · exact high_pointwise_large n hn10 hz'
    interval_cases n
    · exact high_pointwise_4 hz'
    · exact high_pointwise_5 hz'
    · exact high_pointwise_6 hz'
    · exact high_pointwise_7 hz'
    · exact high_pointwise_8 hz'
    · exact high_pointwise_9 hz'
  exact ⟨hlt.le, iff_of_false (ne_of_lt hlt) (ne_of_gt hz')⟩

end PettyProjection.Scalar
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.ScalarCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology
namespace PettyProjection.Scalar

lemma hasDerivAt_Iformula_four {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (Iformula 4) (Mprime 4 z ^ 2) z := by
  have h := ((((hasDerivAt_pow 1 z).sub_const 1).div_const 1).sub
    (((hasDerivAt_inverse_pow 4 hz).const_sub 1).const_mul 2 |>.div_const 4)).add
    (((hasDerivAt_inverse_pow 9 hz).const_sub 1).div_const 9)
  convert! h using 1
  · funext x
    simp [Iformula, exponent]
  · simp only [Mprime, exponent]
    norm_num
    rw [show 10 = 5 * 2 by omega, pow_mul]
    ring

lemma hasDerivAt_Iformula_other {n : ℕ} (hn : 4 ≤ n) (hne : n ≠ 4)
    {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (Iformula n) (Mprime n z ^ 2) z := by
  have hn1 : (n - 1 : ℝ) ≠ 0 := by
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn2 : (2 * n + 1 : ℝ) ≠ 0 := by positivity
  have h := (((((hasDerivAt_pow 3 z).sub_const 1).div_const 3).sub
    (((hasDerivAt_inverse_pow (n-1) hz).const_sub 1).const_mul 2 |>.div_const (n-1 : ℝ))).add
    (((hasDerivAt_inverse_pow (2*n+1) hz).const_sub 1).div_const (2*n+1 : ℝ))).const_mul 4
  have he : n + 1 - 2 = n - 1 := by omega
  have he' : n - 1 + 1 = n := by omega
  have hncast : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hi := z_mul_inverse_pow_succ hz n
  have hp : (z⁻¹) ^ (2*n+1+1) = ((z⁻¹) ^ (n+1)) ^ 2 := by
    rw [show 2*n+1+1 = (n+1)*2 by omega, pow_mul]
  convert! h using 1
  · funext x
    simp only [Iformula, exponent, ite_eq_right hne, Nat.reduceMul, Nat.reduceSub,
      Nat.cast_ofNat, he, hncast, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Pi.add_apply, Pi.sub_apply]
    norm_num
  · simp only [Mprime, exponent, ite_eq_right hne]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, Nat.reducePow, pow_one,
      Nat.cast_add, Nat.cast_mul, hncast, he', hp]
    field_simp
    simp only [one_div]
    nlinarith only [hi]

lemma hasDerivAt_Iformula {n : ℕ} (hn : 4 ≤ n) {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (Iformula n) (Mprime n z ^ 2) z := by
  by_cases hne : n = 4
  · subst n; exact hasDerivAt_Iformula_four hz
  · exact hasDerivAt_Iformula_other hn hne hz

lemma Iformula_one (n : ℕ) : Iformula n 1 = 0 := by simp [Iformula]

lemma contDiff_I {n : ℕ} (hn : 4 ≤ n) : ContDiff ℝ 1 (I n) := by
  exact paste_contDiff_one (f' := fun z => Mprime n z ^ 2)
    (fun x hx => hasDerivAt_Iformula hn (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)))
    (Iformula_one n) (by simp [Mprime_one]) ((continuousOn_Mprime n).pow 2)

lemma deriv_G {n : ℕ} (hn : 4 ≤ n) (z : ℝ) :
    deriv (G n) z = if 1 < z then beta n * Mprime n z else 0 :=
  (paste_hasDerivAt (f' := fun z => beta n * Mprime n z)
    (fun x hx => (hasDerivAt_M (by omega) (ne_of_gt (lt_of_lt_of_le zero_lt_one hx))).const_mul _)
    (by simp [M_one]) (by simp [Mprime_one]) z).deriv

lemma deriv_I {n : ℕ} (hn : 4 ≤ n) (z : ℝ) :
    deriv (I n) z = if 1 < z then Mprime n z ^ 2 else 0 :=
  (paste_hasDerivAt (f' := fun z => Mprime n z ^ 2)
    (fun x hx => hasDerivAt_Iformula hn (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)))
    (Iformula_one n) (by simp [Mprime_one]) z).deriv

lemma derivative_relation {n : ℕ} (hn : 4 ≤ n) (z : ℝ) :
    deriv (G n) z ^ 2 = beta n ^ 2 * deriv (I n) z := by
  rw [deriv_G hn, deriv_I hn]
  split_ifs <;> ring

lemma I_nonneg {n : ℕ} (hn : 4 ≤ n) (z : ℝ) : 0 ≤ I n z := by
  by_cases hz : 1 < z
  · have hmono : Monotone (I n) := by
      apply monotone_of_deriv_nonneg ((contDiff_I hn).differentiable (by norm_num))
      intro x
      rw [deriv_I hn]
      split_ifs <;> positivity
    have h := hmono hz.le
    simpa [I] using h
  · simp [I, hz]

end PettyProjection.Scalar
end

noncomputable section
open Set
namespace PettyProjection.Scalar

lemma convex_tangent_bound {f : ℝ → ℝ} {S : Set ℝ} {x y f' : ℝ}
    (hc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f f' x) :
    f x + f' * (y - x) ≤ f y := by
  rcases lt_trichotomy x y with h | rfl | h
  · have hh := hc.le_slope_of_hasDerivAt hx hy h hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hh
    linarith
  · simp
  · have hh := hc.slope_le_of_hasDerivAt hy hx h hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hh
    nlinarith

lemma inverse_pow_tangent (n : ℕ) {z : ℝ} (hz : 0 < z) :
    1 + (n : ℝ) * (1 - z) ≤ (z⁻¹) ^ n := by
  have hc : ConvexOn ℝ (Ioi 0) (fun x : ℝ => (x⁻¹) ^ n) := by
    simpa only [zpow_neg, zpow_natCast, inv_pow] using (convexOn_zpow (-(n : ℤ)) (𝕜 := ℝ))
  have hd : HasDerivAt (fun x : ℝ => (x⁻¹) ^ n) (-(n : ℝ)) 1 := by
    simpa only [inv_one, one_pow, mul_one] using hasDerivAt_inverse_pow n (one_ne_zero : (1 : ℝ) ≠ 0)
  have h := convex_tangent_bound hc (show (1 : ℝ) ∈ Ioi 0 by norm_num) hz hd
  simp only [inv_one, one_pow] at h
  nlinarith only [h]

lemma e_lower {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : 0 < z) : 1 - z ≤ e n z := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [e, le_div_iff₀ hn']
  nlinarith only [inverse_pow_tangent n hz]

lemma M_nonneg {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : 0 < z) : 0 ≤ M n z := by
  have h := e_lower hn hz
  unfold M exponent
  split_ifs <;> norm_num <;> nlinarith [sq_nonneg (z-1)]

lemma G_bounds {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : 0 < z) :
    0 ≤ G n z ∧ G n z ≤ beta n * M n z := by
  have hm := M_nonneg hn hz
  have hb := (beta_pos n).le
  unfold G
  split_ifs <;> constructor <;> nlinarith

end PettyProjection.Scalar
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.NormEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma mean_add {n : ℕ} [NeZero n] {f g : Sphere n → ℝ} (hf : Continuous f) (hg : Continuous g) :
    mean (fun u => f u + g u) = mean f + mean g :=
  integral_add (continuous_integrable hf) (continuous_integrable hg)

lemma mean_sub {n : ℕ} [NeZero n] {f g : Sphere n → ℝ} (hf : Continuous f) (hg : Continuous g) :
    mean (fun u => f u - g u) = mean f - mean g :=
  integral_sub (continuous_integrable hf) (continuous_integrable hg)

lemma mean_const_mul {n : ℕ} (c : ℝ) (f : Sphere n → ℝ) :
    mean (fun u => c * f u) = c * mean f := integral_const_mul c f

lemma mean_div_const {n : ℕ} (c : ℝ) (f : Sphere n → ℝ) :
    mean (fun u => f u / c) = mean f / c := integral_div c f

lemma mean_mono {n : ℕ} [NeZero n] {f g : Sphere n → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ u, f u ≤ g u) : mean f ≤ mean g :=
  integral_mono (continuous_integrable hf) (continuous_integrable hg) h

lemma mean_nonneg {n : ℕ} {f : Sphere n → ℝ} (h : ∀ u, 0 ≤ f u) : 0 ≤ mean f :=
  integral_nonneg h

lemma mean_centered_square {n : ℕ} [NeZero n] (f : C(Sphere n, ℝ)) :
    mean (fun u => (f u - mean f) ^ 2) = variance f := by
  have hi : (fun u => (f u - mean f) ^ 2) =
      (fun u => (f u) ^ 2 - 2 * mean f * f u + (mean f) ^ 2) := by
    funext u; ring
  rw [hi, mean_add (f := fun u => (f u)^2 - 2 * mean f * f u)
      (g := fun _ => (mean f)^2)
      ((f.continuous.pow 2).sub (continuous_const.mul f.continuous)) continuous_const,
    mean_sub (f := fun u => (f u)^2) (g := fun u => 2 * mean f * f u)
      (f.continuous.pow 2) (continuous_const.mul f.continuous),
    mean_const_mul, mean_const, variance]
  ring

lemma norm_Q_le_variance {n : ℕ} [NeZero n] (f : C(Sphere n, ℝ)) :
    ‖Q n (toH n f)‖ ^ 2 ≤ variance f := by
  simpa only [mean_centered_square] using norm_Q_le_centered n f (mean f)

lemma weighted_square_bound {a b w : ℝ} (hw : 0 < w) (hw1 : w < 1) :
    (a+b)^2 ≤ a^2/w + b^2/(1-w) := by
  have h1 : 0 < 1-w := sub_pos.mpr hw1
  apply (mul_le_mul_iff_of_pos_right (mul_pos hw h1)).mp
  have he : (a^2/w + b^2/(1-w)) * (w*(1-w)) = a^2*(1-w)+b^2*w := by
    field_simp
  rw [he]
  nlinarith only [sq_nonneg ((1-w)*a-w*b)]

lemma weighted_norm_bound {E : Type uE} [SeminormedAddCommGroup E] (a b : E)
    {w : ℝ} (hw : 0 < w) (hw1 : w < 1) :
    ‖a+b‖^2 ≤ ‖a‖^2/w + ‖b‖^2/(1-w) :=
  (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (norm_add_le a b) |>.trans (weighted_square_bound hw hw1)

lemma scalar_correction {n : ℕ} (hn : 4 ≤ n) {m t : ℝ}
    (hm : 0 ≤ m) (ht : 0 ≤ t) (htb : t ≤ Scalar.beta n * m) :
    Scalar.coefficient n * ((2*n : ℝ) * t^2 / (Scalar.weight n * (2*n+8)) -
      (m-t)^2/(1-Scalar.weight n)) ≤
      (2*(Scalar.exponent n : ℝ)-1)/(Scalar.exponent n : ℝ)^2 * m^2 := by
  have hb := (Scalar.beta_pos n).le
  have hb1 := (Scalar.beta_lt_one n).le
  have hw := Scalar.weight_pos n
  have hw1 := Scalar.weight_lt_one n
  have hden : 0 < Scalar.weight n * (2*n+8 : ℝ) := mul_pos hw (by positivity)
  have hs1 : t^2 ≤ (Scalar.beta n)^2 * m^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ ht (mul_nonneg hb hm)).mpr htb
  have ht1 : t ≤ m := htb.trans (by nlinarith)
  have hs2 : (1-Scalar.beta n)^2*m^2 ≤ (m-t)^2 := by
    have hle : (1-Scalar.beta n)*m ≤ m-t := by nlinarith
    simpa only [mul_pow] using (sq_le_sq₀ (mul_nonneg (sub_nonneg.mpr hb1) hm)
      (sub_nonneg.mpr ht1)).mpr hle
  have h1 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ (2*n : ℝ))) hden.le
  have h2 := div_le_div_of_nonneg_right hs2 (sub_nonneg.mpr hw1.le)
  have h3 := mul_le_mul_of_nonneg_left (sub_le_sub h1 h2) (Scalar.coefficient_pos n).le
  have h4 := mul_le_mul_of_nonneg_right (Scalar.mean_bound n hn) (sq_nonneg m)
  apply h3.trans
  convert h4 using 1; ring

lemma scalar_curvature {n : ℕ} (hn : 4 ≤ n) [NeZero n] (g : Seminorm ℝ (Space n)) :
    (2 * n : ℝ) * variance (fun u : Sphere n => Scalar.G n (g u)) + (2 * n + 8 : ℝ) *
      ‖Q n (toH n (restrictContinuous (Scalar.G n ∘ g)
        ((Scalar.contDiff_G hn).continuous.comp (seminorm_continuous n g))))‖ ^ 2 ≤
      ((n : ℝ) - 1) * Scalar.beta n ^ 2 *
        mean (fun u : Sphere n => Scalar.I n (g u) * g u) :=
  seminorm_curvature (by omega) g (Scalar.contDiff_G hn) (Scalar.contDiff_I hn)
    (Scalar.I_nonneg hn) (Scalar.derivative_relation hn)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical
open Scalar

lemma continuous_e_comp {n : ℕ} (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u) :
    Continuous (fun u => e n (f u)) :=
  (((f.continuous.inv₀ (fun u => (hf u).ne')).pow n).sub continuous_const).div_const _

lemma continuous_M_comp {n : ℕ} (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u) :
    Continuous (fun u => M n (f u)) :=
  ((f.continuous.pow _).sub continuous_const).add
    (continuous_const.mul (continuous_e_comp f hf))

lemma mean_e_zero {n : ℕ} [NeZero n] (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u)
    (hnorm : mean (fun u => (f u)⁻¹ ^ n) = 1) : mean (fun u => e n (f u)) = 0 := by
  unfold e
  rw [mean_div_const, mean_sub (f := fun u => (f u)⁻¹^n) (g := fun _ => 1) ((f.continuous.inv₀ (fun u => (hf u).ne')).pow n)
    continuous_const, mean_const, hnorm, sub_self, zero_div]

lemma mean_M_of_normalized {n : ℕ} [NeZero n] (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u)
    (hnorm : mean (fun u => (f u)⁻¹ ^ n) = 1) :
    mean (fun u => M n (f u)) = mean (fun u => (f u) ^ exponent n) - 1 := by
  unfold M
  rw [mean_add (f := fun u => (f u)^exponent n - 1)
      (g := fun u => (exponent n : ℝ) * e n (f u))
      ((f.continuous.pow _).sub continuous_const) (continuous_const.mul (continuous_e_comp f hf)),
    mean_sub (f := fun u => (f u)^exponent n) (g := fun _ => 1) (f.continuous.pow _) continuous_const, mean_const, mean_const_mul,
    mean_e_zero f hf hnorm, mul_zero, add_zero]

lemma mean_W_of_normalized {n : ℕ} [NeZero n] (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u)
    (hnorm : mean (fun u => (f u)⁻¹ ^ n) = 1) :
    mean (fun u => W n (f u)) = mean (fun u => (f u)^exponent n) -
      mean (fun u => (f u)^(exponent n-1)) := by
  unfold W
  rw [mean_add (f := fun u => (f u)^exponent n - (f u)^(exponent n-1))
      (g := fun u => e n (f u)) ((f.continuous.pow _).sub (f.continuous.pow _))
      (continuous_e_comp f hf),
    mean_sub (f := fun u => (f u)^exponent n) (g := fun u => (f u)^(exponent n-1)) (f.continuous.pow _) (f.continuous.pow _), mean_e_zero f hf hnorm, add_zero]

lemma mean_first_power_ge_one {n : ℕ} (hn : 0 < n) [NeZero n]
    (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u)
    (hnorm : mean (fun u => (f u)⁻¹ ^ n) = 1) : 1 ≤ mean f := by
  have hi := mean_mono (f := fun u => 1-f u) (g := fun u => e n (f u)) (continuous_const.sub f.continuous) (continuous_e_comp f hf)
    (fun u => e_lower hn (hf u))
  rw [mean_sub (f := fun _ => 1) (g := f) continuous_const f.continuous, mean_const, mean_e_zero f hf hnorm] at hi
  linarith

lemma norm_mean_ranges {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u)
    (hnorm : mean (fun u => (f u)⁻¹ ^ n) = 1) :
    let m := mean (fun u => (f u) ^ exponent n) - 1
    let ell := mean (fun u => (f u) ^ (exponent n - 1)) - 1
    let t := mean (fun u => G n (f u))
    0 ≤ m ∧ 0 ≤ ell ∧ ell ≤ ((exponent n : ℝ) - 1) / exponent n * m ∧
      0 ≤ t ∧ t ≤ beta n * m := by
  dsimp only
  have hm : 0 ≤ mean (fun u => (f u)^exponent n) - 1 := by
    rw [← mean_M_of_normalized f hf hnorm]
    exact mean_nonneg (fun u => M_nonneg (by omega) (hf u))
  have ht : 0 ≤ mean (fun u => G n (f u)) :=
    mean_nonneg (fun u => (G_bounds (by omega) (hf u)).1)
  have htb := mean_mono (f := fun u => G n (f u)) (g := fun u => beta n*M n (f u)) ((contDiff_G hn).continuous.comp f.continuous)
    (continuous_const.mul (continuous_M_comp f hf)) (fun u => (G_bounds (by omega) (hf u)).2)
  rw [mean_const_mul, mean_M_of_normalized f hf hnorm] at htb
  refine ⟨hm, ?_, ?_, ht, htb⟩
  · by_cases hn4 : n = 4
    · simp [exponent, hn4, mean_const]
    · simpa only [exponent, ite_eq_right hn4, Nat.reduceSub, pow_one, sub_nonneg] using
        mean_first_power_ge_one (by omega) f hf hnorm
  · by_cases hn4 : n = 4
    · simp [exponent, hn4, mean_const]
    · simp only [exponent, ite_eq_right hn4, Nat.reduceSub, Nat.cast_ofNat, pow_one]
      have h := mean_mono (f := fun u => 2*f u) (g := fun u => (f u)^2+1)
        (continuous_const.mul f.continuous) ((f.continuous.pow 2).add continuous_const)
        (fun u => by nlinarith only [sq_nonneg (f u - 1)])
      rw [mean_const_mul, mean_add (f := fun u =>(f u)^2) (g := fun _ => 1) (f.continuous.pow 2) continuous_const, mean_const] at h
      linarith

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical
open Scalar

lemma continuous_L {n : ℕ} (hn : 4 ≤ n) : Continuous (L n) :=
  continuous_const.mul (((((continuous_const.mul continuous_id).mul
    (contDiff_I hn).continuous).sub (continuous_const.mul ((contDiff_G hn).continuous.pow 2))).div_const _).add
      (((continuous_D hn).pow 2).div_const _))

lemma continuous_W_comp {n : ℕ} (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u) :
    Continuous (fun u => W n (f u)) :=
  ((f.continuous.pow _).sub (f.continuous.pow _)).add (continuous_e_comp f hf)

lemma mean_D {n : ℕ} (hn : 4 ≤ n) [NeZero n] (f : C(Sphere n, ℝ)) :
    mean (fun u => D n (f u)) = mean (fun u => (f u)^exponent n) - 1 -
      mean (fun u => G n (f u)) := by
  unfold D
  rw [mean_sub (f := fun u => (f u)^exponent n - 1) (g := fun u => G n (f u))
    ((f.continuous.pow _).sub continuous_const) ((contDiff_G hn).continuous.comp f.continuous),
    mean_sub (f := fun u => (f u)^exponent n) (g := fun _ => 1)
      (f.continuous.pow _) continuous_const, mean_const]

lemma mean_L {n : ℕ} (hn : 4 ≤ n) [NeZero n] (f : C(Sphere n, ℝ)) :
    mean (fun u => L n (f u)) = coefficient n *
      ((((n : ℝ)-1)*beta n^2 * mean (fun u => I n (f u)*f u) -
        2*n*mean (fun u => (G n (f u))^2))/(weight n*(2*n+8)) +
          mean (fun u => (D n (f u))^2)/(1-weight n)) := by
  have hG := (contDiff_G hn).continuous.comp f.continuous
  have hI := (contDiff_I hn).continuous.comp f.continuous
  have hD := (continuous_D hn).comp f.continuous
  unfold L
  rw [mean_const_mul,
    mean_add (f := fun u => (((n : ℝ)-1)*beta n^2*f u*I n (f u)-2*n*(G n (f u))^2)/(weight n*(2*n+8)))
      (g := fun u => (D n (f u))^2/(1-weight n))
      (((continuous_const.mul f.continuous).mul hI |>.sub (continuous_const.mul (hG.pow 2))).div_const _)
      ((hD.pow 2).div_const _),
    mean_div_const, mean_div_const,
    mean_sub (f := fun u => ((n : ℝ)-1)*beta n^2*f u*I n (f u))
      (g := fun u => 2*n*(G n (f u))^2)
      ((continuous_const.mul f.continuous).mul hI) (continuous_const.mul (hG.pow 2)),
    mean_const_mul]
  congr 2
  congr 1
  have he : (fun u : Sphere n => ((n : ℝ)-1)*beta n^2*f u*I n (f u)) =
      (fun u => ((n : ℝ)-1)*beta n^2*(I n (f u)*f u)) := by funext u; ring
  rw [he, mean_const_mul]

lemma Q_power_split {n : ℕ} (hn : 4 ≤ n) [NeZero n] (f : C(Sphere n, ℝ)) :
    Q n (toH n ⟨fun u => (f u)^exponent n, f.continuous.pow _⟩) =
      Q n (toH n ⟨fun u => G n (f u), (contDiff_G hn).continuous.comp f.continuous⟩) +
      Q n (toH n ⟨fun u => D n (f u), (continuous_D hn).comp f.continuous⟩) := by
  have he : (⟨fun u => (f u)^exponent n, f.continuous.pow _⟩ : C(Sphere n, ℝ)) =
      ContinuousMap.const (Sphere n) 1 +
      (⟨fun u => G n (f u), (contDiff_G hn).continuous.comp f.continuous⟩ : C(Sphere n, ℝ)) +
      ⟨fun u => D n (f u), (continuous_D hn).comp f.continuous⟩ := by
    ext u; simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, ContinuousMap.coe_mk, D]; ring
  rw [he, map_add, map_add, map_add, map_add, Q_constant, zero_add]

/-- Exact expectation reduction in the proof of the norm theorem. -/
lemma norm_reduction {n : ℕ} (hn : 4 ≤ n) [NeZero n] (g : Seminorm ℝ (Space n)) :
    coefficient n * ‖Q n (toH n (restrictContinuous (fun x => g x ^ exponent n)
      ((seminorm_continuous n g).pow _)))‖^2 ≤
      mean (fun u : Sphere n => L n (g u)) + coefficient n *
        (2*n*(mean (fun u : Sphere n => G n (g u)))^2/(weight n*(2*n+8)) -
          (mean (fun u : Sphere n => D n (g u)))^2/(1-weight n)) := by
  let f := restrictContinuous g (seminorm_continuous n g)
  let F : C(Sphere n, ℝ) := ⟨fun u => (f u)^exponent n, f.continuous.pow _⟩
  let GG : C(Sphere n, ℝ) := ⟨fun u => G n (f u), (contDiff_G hn).continuous.comp f.continuous⟩
  let DD : C(Sphere n, ℝ) := ⟨fun u => D n (f u), (continuous_D hn).comp f.continuous⟩
  have hs : Q n (toH n F) = Q n (toH n GG) + Q n (toH n DD) := Q_power_split hn f
  have hq := weighted_norm_bound (Q n (toH n GG)) (Q n (toH n DD))
    (weight_pos n) (weight_lt_one n)
  rw [← hs] at hq
  have hd := norm_Q_le_variance DD
  have hc := scalar_curvature hn g
  change (2*n : ℝ)*variance GG + (2*n+8 : ℝ)*‖Q n (toH n GG)‖^2 ≤
    ((n : ℝ)-1)*beta n^2 * mean (fun u => I n (f u)*f u) at hc
  have hp : 0 < (2*n+8 : ℝ) := by positivity
  have hcg : ‖Q n (toH n GG)‖^2 ≤
      (((n : ℝ)-1)*beta n^2 * mean (fun u => I n (f u)*f u) -
        (2*n : ℝ)*variance GG)/(2*n+8) := (le_div_iff₀ hp).mpr (by linarith)
  have hbound := hq.trans (add_le_add (div_le_div_of_nonneg_right hcg (weight_pos n).le)
    (div_le_div_of_nonneg_right hd (sub_nonneg.mpr (weight_lt_one n).le)))
  have hbound' := mul_le_mul_of_nonneg_left hbound (coefficient_pos n).le
  change coefficient n * ‖Q n (toH n F)‖^2 ≤ _
  refine hbound'.trans_eq ?_
  rw [show mean (fun u : Sphere n => L n (g u)) = mean (fun u => L n (f u)) from rfl,
    mean_L hn f]
  change coefficient n *
      (((((n : ℝ)-1)*beta n^2 * mean (fun u => I n (f u)*f u) -
        (2*n : ℝ)*(mean (fun u => (G n (f u))^2) - (mean (fun u => G n (f u)))^2)) /
        (2*n+8))/weight n +
      (mean (fun u => (D n (f u))^2) - (mean (fun u => D n (f u)))^2)/(1-weight n)) = _
  dsimp only [f, restrictContinuous, ContinuousMap.coe_mk]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma mean_square_remainder {k : ℝ} (hk : 0 < k) {m ell : ℝ}
    (hm : 0 ≤ m) (hl : 0 ≤ ell) (hkm : 0 ≤ k-1) (h : ell ≤ (k-1)/k*m) :
    (2*k-1)/k^2*m^2 ≤ m^2-ell^2 := by
  have hs : ell^2 ≤ ((k-1)/k*m)^2 :=
    (sq_le_sq₀ hl (mul_nonneg (div_nonneg hkm hk.le) hm)).mpr h
  have he : (2*k-1)/k^2*m^2 = m^2-((k-1)/k*m)^2 := by field_simp; ring
  rw [he]; linarith

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical
open Scalar

lemma scalar_expectation {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (f : C(Sphere n, ℝ)) (hf : ∀ u, 0 < f u) :
    mean (fun u => L n (f u)) ≤ 2*mean (fun u => W n (f u)) ∧
      (mean (fun u => L n (f u)) = 2*mean (fun u => W n (f u)) ↔ ∀ u, f u = 1) := by
  have hL := (continuous_L hn).comp f.continuous
  have hW : Continuous (fun u => 2*W n (f u)) := continuous_const.mul (continuous_W_comp f hf)
  have hp : ∀ u, L n (f u) ≤ 2*W n (f u) := fun u => (pointwise n hn (hf u)).1
  have hm := mean_mono (f := fun u => L n (f u)) (g := fun u => 2*W n (f u)) hL hW hp
  rw [mean_const_mul] at hm
  refine ⟨hm, ?_, ?_⟩
  · intro he
    have hae : (fun u => L n (f u)) =ᵐ[sigma n] (fun u => 2*W n (f u)) := by
      apply (integral_eq_iff_of_ae_le (continuous_integrable hL) (continuous_integrable hW)
        (Eventually.of_forall hp)).mp
      change mean (fun u => L n (f u)) = mean (fun u => 2*W n (f u))
      rw [mean_const_mul]; exact he
    have heq := (hL.ae_eq_iff_eq (sigma n) hW).mp hae
    intro u
    exact (pointwise n hn (hf u)).2.mp (congrFun heq u)
  · intro he
    have heq : (fun u => L n (f u)) = (fun u => 2*W n (f u)) := by
      funext u; exact (pointwise n hn (hf u)).2.mpr (he u)
    rw [heq, mean_const_mul]

/-- The full arbitrary-norm estimate, including strictness.
It uses the actual spherical measure and the actual quadratic-removing Q. -/
theorem norm_estimate_oai {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (g : Seminorm ℝ (Space n)) (hg : ∀ u : Sphere n, 0 < g u)
    (hnorm : mean (fun u : Sphere n => (g u)⁻¹^n) = 1) :
    coefficient n * ‖Q n (toH n (restrictContinuous (fun x => g x ^ exponent n)
      ((seminorm_continuous n g).pow _)))‖^2 ≤
      (mean (fun u : Sphere n => (g u)^exponent n))^2 -
        (mean (fun u : Sphere n => (g u)^(exponent n-1)))^2 ∧
    (coefficient n * ‖Q n (toH n (restrictContinuous (fun x => g x ^ exponent n)
      ((seminorm_continuous n g).pow _)))‖^2 =
      (mean (fun u : Sphere n => (g u)^exponent n))^2 -
        (mean (fun u : Sphere n => (g u)^(exponent n-1)))^2 ↔ ∀ u : Sphere n, g u = 1) := by
  let f := restrictContinuous g (seminorm_continuous n g)
  let m := mean (fun u => (f u)^exponent n)-1
  let ell := mean (fun u => (f u)^(exponent n-1))-1
  let t := mean (fun u => G n (f u))
  obtain ⟨hm, hl, hlm, ht, htb⟩ := norm_mean_ranges hn f hg hnorm
  have hcorr := scalar_correction hn hm ht htb
  have hk : 0 < (exponent n : ℝ) := by unfold exponent; split_ifs <;> norm_num
  have hkm : 0 ≤ (exponent n : ℝ)-1 := by unfold exponent; split_ifs <;> norm_num
  have hrem := mean_square_remainder hk hm hl hkm hlm
  have hred := norm_reduction hn g
  have hred' : coefficient n * ‖Q n (toH n (restrictContinuous (fun x => g x^exponent n)
      ((seminorm_continuous n g).pow _)))‖^2 ≤
      mean (fun u => L n (f u)) + m^2-ell^2 := by
    have hd : mean (fun u : Sphere n => D n (g u)) = m-t := mean_D hn f
    rw [hd] at hred
    exact hred.trans (by dsimp only [m, ell, t, f, restrictContinuous, ContinuousMap.coe_mk] at *; linarith)
  obtain ⟨hsc, hsce⟩ := scalar_expectation hn f hg
  have hw : mean (fun u => W n (f u)) = m-ell := by
    rw [mean_W_of_normalized f hg hnorm]
    dsimp only [m, ell]; ring
  have hend : 2*(m-ell)+m^2-ell^2 =
      (mean (fun u : Sphere n => (g u)^exponent n))^2 -
        (mean (fun u : Sphere n => (g u)^(exponent n-1)))^2 := by
    dsimp only [m, ell, f, restrictContinuous, ContinuousMap.coe_mk]; ring
  have hfinal : coefficient n * ‖Q n (toH n (restrictContinuous (fun x => g x^exponent n)
      ((seminorm_continuous n g).pow _)))‖^2 ≤
      (mean (fun u : Sphere n => (g u)^exponent n))^2 -
        (mean (fun u : Sphere n => (g u)^(exponent n-1)))^2 :=
    hred'.trans (by rw [← hend]; rw [hw] at hsc; linarith)
  refine ⟨hfinal, ?_, ?_⟩
  · intro he
    apply hsce.mp
    rw [hw]
    rw [← hend] at he
    linarith
  · intro he
    have hpow : restrictContinuous (fun x => g x^exponent n) ((seminorm_continuous n g).pow _) =
        ContinuousMap.const (Sphere n) 1 := by ext u; simp [restrictContinuous, he u]
    rw [hpow, Q_constant, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    have hem : (fun u : Sphere n => (g u)^exponent n) = (fun _ => (1 : ℝ)) := by
      funext u; simp [he u]
    have hel : (fun u : Sphere n => (g u)^(exponent n-1)) = (fun _ => (1 : ℝ)) := by
      funext u; simp [he u]
    rw [hem, hel, sub_self]

end PettyProjection.Spherical
end

end OAI
end

theorem solution : type_of% @OAI.PettyProjection.Spherical.norm_estimate_oai := @OAI.PettyProjection.Spherical.norm_estimate_oai
