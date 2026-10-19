-- Prove2me | solution 1 for OAI.PettyProjection.Spherical.norm_sign_form
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:11:36.018019+00:00
-- url     : https://prove2.me/submissions/d3e776fc-5797-4fd9-91c0-893fecbab2fc

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

lemma inner_toH (n : ℕ) [NeZero n] (f g : C(Sphere n, ℝ)) :
    ⟪toH n f, toH n g⟫ = mean (fun u => f u * g u) := by
  simpa [toH, mean, mul_comm] using ContinuousMap.inner_toLp (sigma n) f g

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

lemma hilbertSum_hasSum_projection (h : IsHilbertSum ℝ (fun i => F i) (fun i => (F i).subtypeₗᵢ))
    (x : E) : HasSum (fun i => (F i).starProjection x) x := by
  have hh := h.hasSum_linearIsometryEquiv_symm (h.linearIsometryEquiv x)
  rw [LinearIsometryEquiv.symm_apply_apply] at hh
  simpa only [hilbertSum_component h, Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype] using hh

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

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection.Spherical

lemma seminorm_ae_differentiable_sphere {n : ℕ} (g : Seminorm ℝ (Space n)) :
    ∀ᵐ (u : Sphere n) ∂sigma n, DifferentiableAt ℝ (g : Space n → ℝ) (u : Space n) := by
  obtain ⟨C, hC⟩ := seminorm_lipschitz n g
  apply sphere_ae_of_radial hC.ae_differentiableAt
  intro u r hr hd
  have hc := (hd.comp (u : Space n) (differentiableAt_id.const_smul r)).const_smul r⁻¹
  have he : (r⁻¹ • ((g : Space n → ℝ) ∘ (r • id))) = (g : Space n → ℝ) := by
    ext x
    simp only [Pi.smul_apply, Function.comp_apply, id_eq, map_smul_eq_mul,
      Real.norm_eq_abs, abs_of_pos hr, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  change DifferentiableAt ℝ (r⁻¹ • ((g : Space n → ℝ) ∘ (r • id))) (u : Space n) at hc
  rw [he] at hc
  exact hc

lemma normSmooth_lipschitz {n : ℕ} (g : Seminorm ℝ (Space n))
    (φ : ContDiffBump (0 : Space n)) {C : ℝ≥0} (hC : LipschitzWith C g) :
    LipschitzWith C (normSmooth g φ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖(∫ z, φ.normed volume z * g (x - z)) -
    (∫ z, φ.normed volume z * g (y - z))‖ ≤ _
  rw [← integral_sub (normSmooth_integrable g φ x) (normSmooth_integrable g φ y)]
  calc
    _ ≤ ∫ z, ‖φ.normed volume z * g (x - z) - φ.normed volume z * g (y - z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, φ.normed volume z * (C * dist x y) := by
      apply integral_mono
        ((normSmooth_integrable g φ x).sub (normSmooth_integrable g φ y)).norm
        (φ.integrable_normed.mul_const _)
      intro z
      change ‖φ.normed volume z * g (x-z) - φ.normed volume z * g (y-z)‖ ≤ _
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (φ.nonneg_normed z)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed z)
      simpa [dist_eq_norm] using hC.dist_le_mul (x-z) (y-z)
    _ = C * dist x y := by rw [integral_mul_const, φ.integral_normed, one_mul]

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

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.CosineCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology Function
namespace PettyProjection.Spherical

lemma posPower_hasDerivAt {r : ℕ} (hr : 2 ≤ r) (x : ℝ) :
    HasDerivAt (posPower r) ((r : ℝ)*posPower (r-1) x) x := by
  have hd (z : ℝ) : HasDerivAt (fun a : ℝ => (a-1)^r) ((r : ℝ)*(z-1)^(r-1)) z := by
    convert! ((hasDerivAt_id z).sub_const 1).pow r using 1
    simp
  have hp := Scalar.paste_hasDerivAt (fun z _ => hd z)
    (by simp [show r ≠ 0 by omega]) (by simp [show r-1 ≠ 0 by omega]) (x+1)
  have h := hp.comp x ((hasDerivAt_id x).add_const 1)
  convert! h using 1
  · funext z; simp [posPower]
  · simp [posPower, mul_ite]

lemma posPower_contDiff_one {r : ℕ} (hr : 2 ≤ r) : ContDiff ℝ 1 (posPower r) := by
  have hd (z : ℝ) : HasDerivAt (fun a : ℝ => (a-1)^r) ((r : ℝ)*(z-1)^(r-1)) z := by
    convert! ((hasDerivAt_id z).sub_const 1).pow r using 1
    simp
  have h := Scalar.paste_contDiff_one (fun z _ => hd z)
    (by simp [show r ≠ 0 by omega]) (by simp [show r-1 ≠ 0 by omega])
    (by fun_prop)
  have hc := h.comp (contDiff_id.add contDiff_const : ContDiff ℝ 1 (fun x : ℝ => x+1))
  convert! hc using 1
  ext x
  simp [posPower]

lemma posPower_contDiff_two {r : ℕ} (hr : 3 ≤ r) : ContDiff ℝ 2 (posPower r) := by
  have he : deriv (posPower r) = fun x => (r : ℝ)*posPower (r-1) x :=
    funext fun x => (posPower_hasDerivAt (by omega) x).deriv
  change ContDiff ℝ (1+1) (posPower r)
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun x => (posPower_hasDerivAt (by omega) x).differentiableAt, ?_, ?_⟩
  · simp
  · rw [he]
    exact contDiff_const.mul (posPower_contDiff_one (by omega))

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma inner_generator {n : ℕ} (u x : Space n) (i j : Fin n) :
    ⟪u, generator n i j x⟫ = x i*u j-x j*u i := by
  simp [generator_apply, inner_sub_right, inner_smul_right,
    EuclideanSpace.inner_single_right]

lemma sum_inner_generator_sq {n : ℕ} (u x : Space n) :
    ∑ i : Fin n, ∑ j : Fin n, ⟪u, generator n i j x⟫^2 =
      2*(‖u‖^2*‖x‖^2-⟪u,x⟫^2) := by
  simp_rw [inner_generator]
  have he (i j : Fin n) : (x i*u j-x j*u i)^2 =
      x i^2*u j^2+x j^2*u i^2-2*(x i*u i)*(x j*u j) := by ring
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq]
  simp only [← Finset.mul_sum]
  rw [← EuclideanSpace.real_norm_sq_eq]
  have hi : ⟪u,x⟫ = ∑ i, x i*u i := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  rw [hi]
  ring

lemma rotDeriv_scalar_linear {n : ℕ} (T : Space n →L[ℝ] Space n)
    (L : Space n →L[ℝ] ℝ) {f f' : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (x : Space n) :
    rotDeriv T (f ∘ L) x = f' (L x)*L (T x) := by
  have h := (hf (L x)).comp_hasFDerivAt x L.hasFDerivAt
  simp only [rotDeriv, h.fderiv, smul_apply, smul_eq_mul]

lemma rotDeriv_scalar_linear_twice {n : ℕ} (T : Space n →L[ℝ] Space n)
    (L : Space n →L[ℝ] ℝ) {f f' f'' : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (x : Space n) :
    rotDeriv T (rotDeriv T (f ∘ L)) x =
      f'' (L x)*(L (T x))^2+f' (L x)*L (T (T x)) := by
  have he : rotDeriv T (f ∘ L) = fun y => f' (L y)*L (T y) :=
    funext (rotDeriv_scalar_linear T L hf)
  rw [he]
  have hd := ((hf' (L x)).comp_hasFDerivAt x L.hasFDerivAt).mul
    (L.comp T).hasFDerivAt
  change fderiv ℝ ((f' ∘ L) * (fun y => (L.comp T) y)) x (T x) = _
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, comp_apply]
  ring

lemma casimir_scalar_inner {n : ℕ} (u x : Space n) {f f' f'' : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) :
    casimir (fun y => f ⟪u,y⟫) x =
      f'' ⟪u,x⟫*(‖u‖^2*‖x‖^2-⟪u,x⟫^2)-
        ((n : ℝ)-1)*f' ⟪u,x⟫*⟪u,x⟫ := by
  change casimir (f ∘ (innerSL ℝ u)) x = _
  unfold casimir
  simp_rw [rotDeriv_scalar_linear_twice _ (innerSL ℝ u) hf hf',
    innerSL_apply_apply, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_inner_generator_sq]
  simp_rw [← inner_sum, sum_generator_square, inner_smul_right]
  ring

lemma posPower_mul {r : ℕ} (x : ℝ) :
    posPower r x*x = posPower (r+1) x := by
  by_cases hx : 0 < x <;> simp [posPower, hx, pow_succ]

lemma posPower_mul_sq {r : ℕ} (x : ℝ) :
    posPower r x*x^2 = posPower (r+2) x := by
  rw [pow_two, ← mul_assoc, posPower_mul, posPower_mul]

lemma casimir_posPower_inner {n r : ℕ} (hr : 3 ≤ r) (u x : Sphere n) :
    casimir (fun y => posPower r ⟪(u : Space n),y⟫) x =
      (r : ℝ)*((r : ℝ)-1)*posPower (r-2) ⟪(u : Space n),(x : Space n)⟫ -
      eigenvalue n r*posPower r ⟪(u : Space n),(x : Space n)⟫ := by
  have hd (t : ℝ) : HasDerivAt (fun z => (r : ℝ)*posPower (r-1) z)
      ((r : ℝ)*((r : ℝ)-1)*posPower (r-2) t) t := by
    convert! (posPower_hasDerivAt (show 2 ≤ r-1 by omega) t).const_mul (r : ℝ) using 1
    rw [show r-1-1 = r-2 by omega, Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rw [casimir_scalar_inner _ _ (posPower_hasDerivAt (by omega)) hd,
    norm_coe, norm_coe]
  simp only [one_pow, mul_one]
  have h₁ := posPower_mul (r := r-1) ⟪(u : Space n),(x : Space n)⟫
  have h₂ := posPower_mul_sq (r := r-2) ⟪(u : Space n),(x : Space n)⟫
  rw [show r-1+1 = r by omega] at h₁
  rw [show r-2+2 = r by omega] at h₂
  unfold eigenvalue
  calc
    _ = (r : ℝ)*((r : ℝ)-1)*posPower (r-2) ⟪(u : Space n),(x : Space n)⟫ -
      (r : ℝ)*((r : ℝ)-1)*(posPower (r-2) ⟪(u : Space n),(x : Space n)⟫ * ⟪(u : Space n),(x : Space n)⟫^2) -
      ((n : ℝ)-1)*(r : ℝ)*(posPower (r-1) ⟪(u : Space n),(x : Space n)⟫ * ⟪(u : Space n),(x : Space n)⟫) := by ring
    _ = _ := by rw [h₁, h₂]; ring

lemma mean_casimir_comm {n : ℕ} [NeZero n] {f g : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    mean (fun u : Sphere n => f u*casimir g u) =
      mean (fun u : Sphere n => g u*casimir f u) := by
  rw [mean_casimir (hf.of_le (by norm_num)) hg,
    mean_casimir (hg.of_le (by norm_num)) hf, energy_symm]

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma sum_inner_generator_mul {n : ℕ} (u w x : Space n) :
    ∑ i : Fin n, ∑ j : Fin n, ⟪u,generator n i j x⟫*⟪w,generator n i j x⟫ =
      2*(‖x‖^2*⟪u,w⟫-⟪u,x⟫*⟪w,x⟫) := by
  simp_rw [inner_generator]
  have he (i j : Fin n) : (x i*u j-x j*u i)*(x i*w j-x j*w i) =
      x i^2*(u j*w j)+x j^2*(u i*w i)-(x i*w i)*(x j*u j)-(x i*u i)*(x j*w j) := by ring
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  have hi (a b : Space n) : ⟪a,b⟫ = ∑ i, a i*b i := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  rw [hi u w, hi u x, hi w x, EuclideanSpace.real_norm_sq_eq]
  simp_rw [mul_comm (u _) (x _), mul_comm (w _) (x _)]
  simp only [← Finset.mul_sum]
  ring

lemma continuous_gradient_of_contDiff {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f) :=
  (InnerProductSpace.toDual ℝ (Space n)).symm.continuous.comp (hf.continuous_fderiv (by norm_num))

lemma sphereGradient_continuous {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (sphereGradient f) := by
  exact (continuous_gradient_of_contDiff hf).sub
    (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_id).smul continuous_id)

lemma sphereGradient_inner {n : ℕ} (f : Space n → ℝ) (x w : Space n) :
    ⟪sphereGradient f x,w⟫ = fderiv ℝ f x w - fderiv ℝ f x x*⟪x,w⟫ := by
  simp only [sphereGradient, inner_sub_left, inner_smul_left, inner_gradient_left, starRingEnd_apply, star_trivial]

lemma sphereGradient_tangent {n : ℕ} (f : Space n → ℝ) (x : Sphere n) :
    ⟪sphereGradient f x,(x : Space n)⟫ = 0 := by
  rw [sphereGradient_inner, real_inner_self_eq_norm_sq, norm_coe]
  simp

lemma sum_rotDeriv_inner {n : ℕ} (f : Space n → ℝ) (x : Sphere n) (w : Space n) :
    (1/2 : ℝ)*(∑ i : Fin n, ∑ j : Fin n,
      rotDeriv (generator n i j) f x*⟪w,generator n i j x⟫) = ⟪sphereGradient f x,w⟫ := by
  simp only [rotDeriv, ← inner_gradient_left]
  rw [sum_inner_generator_mul, norm_coe, sphereGradient_inner,
    inner_gradient_left, inner_gradient_left, real_inner_comm w (x : Space n)]
  ring

lemma mean_gradient_casimir {n : ℕ} [NeZero n] {f g : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g) :
    mean (fun x : Sphere n => ⟪sphereGradient f x,sphereGradient g x⟫) =
      -mean (fun x : Sphere n => f x*casimir g x) := by
  rw [mean_casimir hf hg, neg_neg]
  have hs (x : Sphere n) : ⟪sphereGradient f x,sphereGradient g x⟫ =
      (1/2 : ℝ)*∑ i : Fin n, ∑ j : Fin n,
        rotDeriv (generator n i j) f x*rotDeriv (generator n i j) g x := by
    have h := sum_rotDeriv_inner f x (∇ g x)
    simp only [inner_gradient_left] at h
    change ⟪sphereGradient f x, ∇ g x - (fderiv ℝ g x x) • (x : Space n)⟫ = _
    rw [inner_sub_right, inner_smul_right, sphereGradient_tangent, mul_zero, sub_zero]
    exact h.symm
  simp_rw [hs]
  rw [mean, integral_const_mul]
  congr 1
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ => continuous_integrable
      (((continuous_rotDeriv _ hf).comp continuous_subtype_val).mul
        ((continuous_rotDeriv _ (hg.of_le (by norm_num))).comp continuous_subtype_val)))
  · intro i _
    apply continuous_integrable
    exact continuous_finsetSum _ fun j _ =>
      ((continuous_rotDeriv _ hf).comp continuous_subtype_val).mul
        ((continuous_rotDeriv _ (hg.of_le (by norm_num))).comp continuous_subtype_val)

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.SupportMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma convex_deriv_limit {ι : Type uι} {l : Filter ι} {f : ι → ℝ → ℝ}
    {g : ℝ → ℝ} {d : ι → ℝ} {a : ℝ}
    (hf : ∀ j, ConvexOn ℝ univ (f j))
    (hd : ∀ j, HasDerivAt (f j) (d j) 0)
    (hg : HasDerivAt g a 0)
    (hlim : ∀ t, Tendsto (fun j => f j t) l (𝓝 (g t))) :
    Tendsto d l (𝓝 a) := by
  have hs (t : ℝ) : Tendsto (fun j => slope (f j) 0 t) l (𝓝 (slope g 0 t)) := by
    simpa only [slope, vsub_eq_sub, smul_eq_mul] using
      ((hlim t).sub (hlim 0)).const_mul (t - 0)⁻¹
  rw [tendsto_order]
  constructor
  · intro b hb
    have hh : ∀ᶠ t in 𝓝[<] (0 : ℝ), b < slope g 0 t :=
      (hg.tendsto_slope.mono_left (nhdsWithin_mono _ (by grind : Iio (0 : ℝ) ⊆ {0}ᶜ))).eventually
        (eventually_gt_nhds hb)
    have ht : ∀ᶠ t in 𝓝[<] (0 : ℝ), t < 0 := self_mem_nhdsWithin
    obtain ⟨t, ht, hbt⟩ := (ht.and hh).exists
    filter_upwards [(hs t).eventually (eventually_gt_nhds hbt)] with j hj
    have hj' := (hf j).slope_le_of_hasDerivAt (mem_univ t) (mem_univ 0) ht (hd j)
    rw [slope_comm] at hj'
    exact hj.trans_le hj'
  · intro b hb
    have hh : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope g 0 t < b :=
      (hg.tendsto_slope.mono_left (nhdsWithin_mono _ (by grind : Ioi (0 : ℝ) ⊆ {0}ᶜ))).eventually
        (eventually_lt_nhds hb)
    have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ht, hbt⟩ := (ht.and hh).exists
    filter_upwards [(hs t).eventually (eventually_lt_nhds hbt)] with j hj
    exact ((hf j).le_slope_of_hasDerivAt (mem_univ 0) (mem_univ t) ht (hd j)).trans_lt hj

lemma convex_fderiv_apply_limit {n : ℕ} {ι : Type uι} {l : Filter ι}
    {f : ι → Space n → ℝ} {g : Space n → ℝ} {x : Space n}
    (hf : ∀ j, ConvexOn ℝ univ (f j)) (hd : ∀ j, DifferentiableAt ℝ (f j) x)
    (hg : DifferentiableAt ℝ g x)
    (hlim : ∀ y, Tendsto (fun j => f j y) l (𝓝 (g y))) (w : Space n) :
    Tendsto (fun j => fderiv ℝ (f j) x w) l (𝓝 (fderiv ℝ g x w)) := by
  apply convex_deriv_limit (fun j => line_convex (hf j) x w)
  · intro j
    have h : HasFDerivAt (f j) (fderiv ℝ (f j) x) (x + (0 : ℝ) • w) := by
      simpa only [zero_smul, add_zero] using (hd j).hasFDerivAt
    exact h.comp_hasDerivAt 0 (line_hasDerivAt x w 0)
  · have h : HasFDerivAt g (fderiv ℝ g x) (x + (0 : ℝ) • w) := by
      simpa only [zero_smul, add_zero] using hg.hasFDerivAt
    exact h.comp_hasDerivAt 0 (line_hasDerivAt x w 0)
  · intro t
    exact hlim (x + t • w)

lemma convex_gradient_limit {n : ℕ} {ι : Type uι} {l : Filter ι}
    {f : ι → Space n → ℝ} {g : Space n → ℝ} {x : Space n}
    (hf : ∀ j, ConvexOn ℝ univ (f j)) (hd : ∀ j, DifferentiableAt ℝ (f j) x)
    (hg : DifferentiableAt ℝ g x)
    (hlim : ∀ y, Tendsto (fun j => f j y) l (𝓝 (g y))) :
    Tendsto (fun j => ∇ (f j) x) l (𝓝 (∇ g x)) := by
  have hp : Tendsto (fun j i => (∇ (f j) x) i) l (𝓝 (fun i => (∇ g x) i)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have h := convex_fderiv_apply_limit hf hd hg hlim (EuclideanSpace.single i 1)
    simpa only [← inner_gradient_left, EuclideanSpace.inner_single_right, one_mul, conj_trivial] using h
  exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).continuousAt.tendsto.comp hp

lemma normSmooth_tendsto {n : ℕ} (g : Seminorm ℝ (Space n)) (x : Space n) :
    Tendsto (fun j => normSmooth g (shrinkingBump n j) x) atTop (𝓝 (g x)) := by
  obtain ⟨C, hC⟩ := seminorm_lipschitz n g
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg) (fun j => normSmooth_dist_le g _ hC x)
    (by simpa only [mul_zero, shrinkingBump] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (C : ℝ))

lemma normSmooth_gradient_tendsto {n : ℕ} (g : Seminorm ℝ (Space n)) {x : Space n}
    (hx : DifferentiableAt ℝ (g : Space n → ℝ) x) :
    Tendsto (fun j => ∇ (normSmooth g (shrinkingBump n j)) x) atTop (𝓝 (∇ (g : Space n → ℝ) x)) :=
  convex_gradient_limit (fun j => normSmooth_convex g _)
    (fun j => (normSmooth_contDiff g _).differentiable (by norm_num) x) hx (normSmooth_tendsto g)

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.SignCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology
namespace PettyProjection.Spherical

lemma softAbs_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 < softAbs ε t :=
  Real.sqrt_pos.mpr (by positivity)

lemma softAbs_sq {ε : ℝ} (hε : 0 < ε) (t : ℝ) : (softAbs ε t)^2 = t^2+ε :=
  Real.sq_sqrt (by positivity)

lemma softAbs_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ⊤ (softAbs ε) := by
  exact ((contDiff_id.pow 2).add contDiff_const).sqrt (fun t => ne_of_gt (by positivity))

lemma softSign_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ⊤ (softSign ε) :=
  contDiff_id.div (softAbs_contDiff hε) (fun t => (softAbs_pos hε t).ne')

lemma softAbs_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (softAbs ε) (softSign ε t) t := by
  have h := ((hasDerivAt_pow 2 t).add_const ε).sqrt (by positivity : t^2+ε ≠ 0)
  convert! h using 1
  simp only [softSign, softAbs, Nat.cast_ofNat]
  ring

lemma softSign_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (softSign ε) (softSlope ε t) t := by
  have h := (hasDerivAt_id t).div (softAbs_hasDerivAt hε t) (softAbs_pos hε t).ne'
  convert! h using 1
  dsimp [softSlope, softSign]
  field_simp [(softAbs_pos hε t).ne']
  nlinarith [softAbs_sq hε t]

lemma abs_le_softAbs {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |t| ≤ softAbs ε t := by
  have hs := softAbs_sq hε t
  have hp := (softAbs_pos hε t).le
  nlinarith [sq_abs t, abs_nonneg t]

lemma softAbs_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) : softAbs ε t ≤ |t|+Real.sqrt ε := by
  have hs := softAbs_sq hε t
  have hp := (softAbs_pos hε t).le
  have he := Real.sq_sqrt hε.le
  have hn := mul_nonneg (abs_nonneg t) (Real.sqrt_nonneg ε)
  nlinarith [sq_abs t, abs_nonneg t, Real.sqrt_nonneg ε]

lemma abs_softSign_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |softSign ε t| ≤ 1 := by
  rw [softSign, abs_div, abs_of_pos (softAbs_pos hε t), div_le_one (softAbs_pos hε t)]
  exact abs_le_softAbs hε t

lemma abs_softCorrection_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |t*softSlope ε t| ≤ 1 := by
  have hp := softAbs_pos hε t
  have hs : ε ≤ (softAbs ε t)^2 := by nlinarith [softAbs_sq hε t, sq_nonneg t]
  have hm := mul_le_mul (abs_le_softAbs hε t) hs hε.le hp.le
  rw [softSlope, ← mul_div_assoc, abs_div, abs_of_pos (pow_pos hp _),
    abs_mul, abs_of_pos hε, div_le_one (pow_pos hp _)]
  nlinarith

lemma real_sign_eq (t : ℝ) : Real.sign t = t/|t| := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [Real.sign_of_neg ht, abs_of_neg ht]
    field_simp [ht.ne]
  · simp
  · rw [Real.sign_of_pos ht, abs_of_pos ht, div_self ht.ne']

lemma softAbs_tendsto (t : ℝ) :
    Tendsto (fun m : ℕ => softAbs (1/((m : ℝ)+1)) t) atTop (𝓝 |t|) := by
  have h : Tendsto (fun m : ℕ => t^2 + 1/((m : ℝ)+1)) atTop (𝓝 (t^2+0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  simp only [add_zero] at h
  simpa only [softAbs, Function.comp_def, Real.sqrt_sq_eq_abs] using
    (Real.continuous_sqrt.tendsto (t^2)).comp h

lemma softSign_tendsto (t : ℝ) :
    Tendsto (fun m : ℕ => softSign (1/((m : ℝ)+1)) t) atTop (𝓝 (Real.sign t)) := by
  by_cases ht : t = 0
  · subst t
    simpa only [softSign, zero_div, Real.sign_zero] using tendsto_const_nhds
  · rw [real_sign_eq]
    exact tendsto_const_nhds.div (softAbs_tendsto t) (abs_ne_zero.mpr ht)

lemma softCorrection_tendsto (t : ℝ) :
    Tendsto (fun m : ℕ => t*softSlope (1/((m : ℝ)+1)) t) atTop (𝓝 0) := by
  by_cases ht : t = 0
  · subst t
    simp only [zero_mul]
    exact tendsto_const_nhds
  · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div
      ((softAbs_tendsto t).pow 3) (pow_ne_zero 3 (abs_ne_zero.mpr ht))
    simpa only [softSlope, Pi.div_apply, zero_div, mul_zero] using h.const_mul t

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma casimir_linear {n : ℕ} (w x : Space n) :
    casimir (fun y => ⟪w,y⟫) x = -((n : ℝ)-1)*⟪w,x⟫ := by
  simpa only [id_eq, zero_mul, mul_one, zero_sub, neg_mul] using
    casimir_scalar_inner w x (fun t => hasDerivAt_id t)
      (fun t => hasDerivAt_const t (1 : ℝ))

lemma sphereGradient_linear_inner {n : ℕ} (w : Space n) (x : Sphere n) (v : Space n) :
    ⟪sphereGradient (fun y => ⟪w,y⟫) x,v⟫ = ⟪w,v⟫-⟪w,(x : Space n)⟫*⟪(x : Space n),v⟫ := by
  rw [sphereGradient_inner]
  change (fderiv ℝ (innerSL ℝ w) x) v - (fderiv ℝ (innerSL ℝ w) x) x * _ = _
  rw [(innerSL ℝ w).fderiv]
  rfl

lemma mean_sphereGradient_inner {n : ℕ} [NeZero n] {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (w : Space n) :
    mean (fun x : Sphere n => ⟪sphereGradient f x,w⟫) =
      ((n : ℝ)-1)*mean (fun x : Sphere n => f x*⟪(x : Space n),w⟫) := by
  have h := mean_gradient_casimir hf ((innerSL ℝ w).contDiff (n := 2))
  change mean (fun x : Sphere n => ⟪sphereGradient f x,sphereGradient (fun y => ⟪w,y⟫) x⟫) =
    -mean (fun x : Sphere n => f x*casimir (fun y => ⟪w,y⟫) x) at h
  have hg (x : Sphere n) : ⟪sphereGradient f x,sphereGradient (fun y => ⟪w,y⟫) x⟫ =
      ⟪sphereGradient f x,w⟫ := by
    have ht : ⟪(x : Space n),sphereGradient f x⟫ = 0 := by
      rw [real_inner_comm, sphereGradient_tangent]
    rw [real_inner_comm, sphereGradient_linear_inner, ht, mul_zero, sub_zero, real_inner_comm]
  simp_rw [hg, casimir_linear] at h
  rw [h]
  simp_rw [real_inner_comm w]
  rw [mean, mean, ← integral_const_mul, ← integral_neg]
  congr 1
  funext x
  ring

lemma sphereGradient_product_scalar_inner {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) {ρ ρ' : ℝ → ℝ}
    (hρ : ∀ t, HasDerivAt ρ (ρ' t) t) (v x w : Space n) :
    ⟪sphereGradient (fun y => f y*ρ ⟪v,y⟫) x,w⟫ =
      ρ ⟪v,x⟫*⟪sphereGradient f x,w⟫+
      f x*ρ' ⟪v,x⟫*(⟪v,w⟫-⟪v,x⟫*⟪x,w⟫) := by
  rw [sphereGradient_inner, sphereGradient_inner]
  have hd := (hf.differentiable (by norm_num) x).hasFDerivAt.mul
    ((hρ ⟪v,x⟫).comp_hasFDerivAt x (innerSL ℝ v).hasFDerivAt)
  change HasFDerivAt (fun y => f y*ρ ⟪v,y⟫) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply, comp_apply]
  ring

lemma mean_weighted_gradient {n : ℕ} [NeZero n] {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) {ρ ρ' : ℝ → ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hρ' : Continuous ρ') (hd : ∀ t, HasDerivAt ρ (ρ' t) t)
    (v w : Space n) :
    mean (fun x : Sphere n => ρ ⟪v,(x : Space n)⟫*⟪sphereGradient f x,w⟫) =
      ((n : ℝ)-1)*mean (fun x : Sphere n => ρ ⟪v,(x : Space n)⟫*f x*⟪(x : Space n),w⟫) -
      mean (fun x : Sphere n => f x*ρ' ⟪v,(x : Space n)⟫*
        (⟪v,w⟫-⟪v,(x : Space n)⟫*⟪(x : Space n),w⟫)) := by
  have h := mean_sphereGradient_inner (hf.mul (hρ.comp (innerSL ℝ v).contDiff)) w
  change mean (fun x : Sphere n => ⟪sphereGradient (fun y => f y*ρ ⟪v,y⟫) x,w⟫) =
    ((n : ℝ)-1)*mean (fun x : Sphere n => (f x*ρ ⟪v,(x : Space n)⟫)*⟪(x : Space n),w⟫) at h
  simp_rw [sphereGradient_product_scalar_inner hf hd] at h
  have h₁ : Continuous (fun x : Sphere n => ρ ⟪v,(x : Space n)⟫*⟪sphereGradient f x,w⟫) :=
    (hρ.continuous.comp (continuous_const.inner continuous_subtype_val)).mul
      (((sphereGradient_continuous hf).comp continuous_subtype_val).inner continuous_const)
  have h₂ : Continuous (fun x : Sphere n => f x*ρ' ⟪v,(x : Space n)⟫*
      (⟪v,w⟫-⟪v,(x : Space n)⟫*⟪(x : Space n),w⟫)) := by fun_prop
  rw [mean, integral_add (continuous_integrable h₁) (continuous_integrable h₂)] at h
  change mean _ + mean _ = _ at h
  have he : (fun x : Sphere n => (f x*ρ ⟪v,(x : Space n)⟫)*⟪(x : Space n),w⟫) =
      (fun x : Sphere n => ρ ⟪v,(x : Space n)⟫*f x*⟪(x : Space n),w⟫) := by
    funext x; ring
  rw [he] at h
  linarith

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma sign_measurable : Measurable Real.sign := by
  have he : Real.sign = fun t : ℝ => t/|t| := funext real_sign_eq
  rw [he]
  exact measurable_id.div measurable_id.abs

lemma abs_sign_le (t : ℝ) : |Real.sign t| ≤ 1 := by
  rw [real_sign_eq, abs_div, abs_abs]
  by_cases ht : t = 0
  · simp [ht]
  · rw [div_self (abs_ne_zero.mpr ht)]

lemma sign_mul_self (t : ℝ) : Real.sign t*t = |t| := by
  rw [real_sign_eq]
  by_cases ht : t = 0
  · simp [ht]
  · field_simp [abs_ne_zero.mpr ht]
    exact (sq_abs t).symm

lemma mean_softSign_tendsto {n : ℕ} [NeZero n] (t f : Sphere n → ℝ)
    (ht : Continuous t) (hf : Continuous f) :
    Tendsto (fun m : ℕ => mean (fun x => softSign (1/((m : ℝ)+1)) (t x)*f x)) atTop
      (𝓝 (mean (fun x => Real.sign (t x)*f x))) := by
  apply tendsto_integral_of_dominated_convergence (fun x => |f x|)
  · intro m
    exact (((softSign_contDiff (by positivity : 0 < 1/((m : ℝ)+1))).continuous.comp ht).mul hf).aestronglyMeasurable
  · exact continuous_integrable hf.abs
  · intro m
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (abs_softSign_le (by positivity : 0 < 1/((m : ℝ)+1)) (t x)) (abs_nonneg (f x))
  · filter_upwards with x
    exact (softSign_tendsto (t x)).mul_const (f x)

lemma mean_softCorrection_tendsto {n : ℕ} [NeZero n] (t f : Sphere n → ℝ)
    (ht : Continuous t) (hf : Continuous f) :
    Tendsto (fun m : ℕ => mean (fun x => (t x*softSlope (1/((m : ℝ)+1)) (t x))*f x)) atTop
      (𝓝 0) := by
  have h : Tendsto (fun m : ℕ => mean (fun x => (t x*softSlope (1/((m : ℝ)+1)) (t x))*f x)) atTop
      (𝓝 (mean (fun _ : Sphere n => 0))) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |f x|)
    · intro m
      have hc : Continuous (softSlope (1/((m : ℝ)+1))) :=
        continuous_const.div ((softAbs_contDiff (by positivity)).continuous.pow 3)
          (fun y => pow_ne_zero _ (softAbs_pos (by positivity) y).ne')
      exact ((ht.mul (hc.comp ht)).mul hf).aestronglyMeasurable
    · exact continuous_integrable hf.abs
    · intro m
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (abs_softCorrection_le (by positivity : 0 < 1/((m : ℝ)+1)) (t x)) (abs_nonneg (f x))
    · filter_upwards with x
      simpa only [zero_mul] using (softCorrection_tendsto (t x)).mul_const (f x)
  simpa only [mean, integral_zero] using h

lemma mean_softAbs_tendsto {n : ℕ} [NeZero n] (t f : Sphere n → ℝ)
    (ht : Continuous t) (hf : Continuous f) :
    Tendsto (fun m : ℕ => mean (fun x => softAbs (1/((m : ℝ)+1)) (t x)*f x)) atTop
      (𝓝 (mean (fun x => |t x| *f x))) := by
  apply tendsto_integral_of_dominated_convergence (fun x => (|t x|+1)*|f x|)
  · intro m
    exact (((softAbs_contDiff (by positivity : 0 < 1/((m : ℝ)+1))).continuous.comp ht).mul hf).aestronglyMeasurable
  · exact continuous_integrable ((ht.abs.add continuous_const).mul hf.abs)
  · intro m
    filter_upwards with x
    have hε : Real.sqrt (1/((m : ℝ)+1)) ≤ 1 := by
      apply (Real.sqrt_le_one).mpr
      apply (div_le_one (by positivity : 0 < (m : ℝ)+1)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) m]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (softAbs_pos (by positivity) (t x))]
    exact mul_le_mul_of_nonneg_right ((softAbs_le (by positivity) (t x)).trans (by linarith)) (abs_nonneg (f x))
  · filter_upwards with x
    exact (softAbs_tendsto (t x)).mul_const (f x)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma mean_sign_gradient_tangent {n : ℕ} [NeZero n] {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (v w : Space n) (hvw : ⟪v,w⟫ = 0) :
    mean (fun x : Sphere n => Real.sign ⟪v,(x : Space n)⟫*⟪sphereGradient f x,w⟫) =
      ((n : ℝ)-1)*mean (fun x : Sphere n => Real.sign ⟪v,(x : Space n)⟫*f x*⟪(x : Space n),w⟫) := by
  let t : Sphere n → ℝ := fun x => ⟪v,(x : Space n)⟫
  have ht : Continuous t := continuous_const.inner continuous_subtype_val
  have hF : Continuous (fun x : Sphere n => ⟪sphereGradient f x,w⟫) :=
    ((sphereGradient_continuous hf).comp continuous_subtype_val).inner continuous_const
  have hG : Continuous (fun x : Sphere n => f x*⟪(x : Space n),w⟫) := by fun_prop
  have he (m : ℕ) :
      mean (fun x : Sphere n => softSign (1/((m : ℝ)+1)) (t x)*⟪sphereGradient f x,w⟫) =
      ((n : ℝ)-1)*mean (fun x : Sphere n => softSign (1/((m : ℝ)+1)) (t x)*(f x*⟪(x : Space n),w⟫)) +
        mean (fun x : Sphere n => (t x*softSlope (1/((m : ℝ)+1)) (t x))*(f x*⟪(x : Space n),w⟫)) := by
    have hp : 0 < 1/((m : ℝ)+1) := by positivity
    have hc : Continuous (softSlope (1/((m : ℝ)+1))) :=
      continuous_const.div ((softAbs_contDiff hp).continuous.pow 3)
        (fun y => pow_ne_zero _ (softAbs_pos hp y).ne')
    have h := mean_weighted_gradient hf ((softSign_contDiff hp).of_le (by norm_num)) hc
      (softSign_hasDerivAt hp) v w
    rw [h]
    simp only [hvw, zero_sub]
    rw [mean, mean, mean, mean, sub_eq_add_neg, ← integral_neg]
    congr 1
    · congr 1
      apply integral_congr_ae
      filter_upwards with x
      dsimp [t]; ring
    · apply integral_congr_ae
      filter_upwards with x
      dsimp [t]; ring
  have h₁ := mean_softSign_tendsto t _ ht hF
  have h₂ := ((mean_softSign_tendsto t _ ht hG).const_mul ((n : ℝ)-1)).add
    (mean_softCorrection_tendsto t _ ht hG)
  have heq := tendsto_nhds_unique h₁ (h₂.congr' (Filter.Eventually.of_forall (fun m => (he m).symm)))
  simpa only [add_zero, t, mul_assoc] using heq

lemma sphereGradient_scalar_inner {n : ℕ} {ρ ρ' : ℝ → ℝ}
    (hρ : ∀ t, HasDerivAt ρ (ρ' t) t) (v x w : Space n) :
    ⟪sphereGradient (fun y => ρ ⟪v,y⟫) x,w⟫ =
      ρ' ⟪v,x⟫*(⟪v,w⟫-⟪v,x⟫*⟪x,w⟫) := by
  have hd := (hρ ⟪v,x⟫).comp_hasFDerivAt x (innerSL ℝ v).hasFDerivAt
  change HasFDerivAt (fun y => ρ ⟪v,y⟫) _ x at hd
  rw [sphereGradient_inner, hd.fderiv]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  ring

lemma mean_sign_gradient_radial {n : ℕ} [NeZero n] {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (v : Space n) :
    mean (fun x : Sphere n => Real.sign ⟪v,(x : Space n)⟫*⟪sphereGradient f x,v⟫) =
      -mean (fun x : Sphere n => |⟪v,(x : Space n)⟫| * casimir f x) := by
  let t : Sphere n → ℝ := fun x => ⟪v,(x : Space n)⟫
  have ht : Continuous t := continuous_const.inner continuous_subtype_val
  have hF : Continuous (fun x : Sphere n => ⟪sphereGradient f x,v⟫) :=
    ((sphereGradient_continuous (hf.of_le (by norm_num))).comp continuous_subtype_val).inner continuous_const
  have hG : Continuous (fun x : Sphere n => casimir f x) :=
    by
      unfold casimir
      exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
        continuous_finsetSum _ fun j _ =>
          (continuous_rotDeriv _ (contDiff_rotDeriv _ hf)).comp continuous_subtype_val)
  have he (m : ℕ) :
      mean (fun x : Sphere n => softSign (1/((m : ℝ)+1)) (t x)*⟪sphereGradient f x,v⟫) =
      -mean (fun x : Sphere n => softAbs (1/((m : ℝ)+1)) (t x)*casimir f x) := by
    have hp : 0 < 1/((m : ℝ)+1) := by positivity
    have h := mean_gradient_casimir
      ((show ContDiff ℝ 1 (softAbs (1/((m : ℝ)+1))) from (softAbs_contDiff hp).of_le le_top).comp (innerSL ℝ v).contDiff) hf
    change mean (fun x : Sphere n => ⟪sphereGradient (fun y => softAbs (1/((m : ℝ)+1)) ⟪v,y⟫) x,sphereGradient f x⟫) = _ at h
    have hg (x : Sphere n) :
        ⟪sphereGradient (fun y => softAbs (1/((m : ℝ)+1)) ⟪v,y⟫) x,sphereGradient f x⟫ =
          softSign (1/((m : ℝ)+1)) (t x)*⟪sphereGradient f x,v⟫ := by
      rw [sphereGradient_scalar_inner (softAbs_hasDerivAt hp)]
      have hx : ⟪(x : Space n),sphereGradient f x⟫ = 0 := by rw [real_inner_comm, sphereGradient_tangent]
      rw [hx, mul_zero, sub_zero, real_inner_comm v]
    simp_rw [hg] at h
    exact h
  have h₁ := mean_softSign_tendsto t _ ht hF
  have h₂ := (mean_softAbs_tendsto t _ ht hG).neg
  exact tendsto_nhds_unique h₁ (h₂.congr' (Filter.Eventually.of_forall (fun m => (he m).symm)))

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma signedPair_integrable {n : ℕ} [NeZero n] {F G : Sphere n → Space n}
    (hF : Continuous F) (hG : Continuous G) :
    Integrable (fun z : Sphere n × Sphere n => Real.sign ⟪(z.1 : Space n),(z.2 : Space n)⟫ *
      ⟪F z.1,G z.2⟫) ((sigma n).prod (sigma n)) := by
  have hi : Integrable (fun z : Sphere n × Sphere n => ⟪F z.1,G z.2⟫)
      ((sigma n).prod (sigma n)) :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply hi.bdd_mul (sign_measurable.comp (by fun_prop : Continuous
    (fun z : Sphere n × Sphere n => ⟪(z.1 : Space n),(z.2 : Space n)⟫)).measurable).aestronglyMeasurable
  filter_upwards with z
  exact abs_sign_le _

lemma signedPair_eq {n : ℕ} [NeZero n] {F G : Sphere n → Space n}
    (hF : Continuous F) (hG : Continuous G) :
    signedPair F G = mean (fun u => mean (fun v =>
      Real.sign ⟪(u : Space n),(v : Space n)⟫ * ⟪F u,G v⟫)) :=
  integral_prod _ (signedPair_integrable hF hG)

lemma signedPair_eq_swap {n : ℕ} [NeZero n] {F G : Sphere n → Space n}
    (hF : Continuous F) (hG : Continuous G) :
    signedPair F G = mean (fun v => mean (fun u =>
      Real.sign ⟪(u : Space n),(v : Space n)⟫ * ⟪F u,G v⟫)) := by
  rw [signedPair_eq hF hG]
  exact integral_integral_swap (signedPair_integrable hF hG)

lemma signedPair_symm {n : ℕ} [NeZero n] {F G : Sphere n → Space n}
    (hF : Continuous F) (hG : Continuous G) : signedPair F G = signedPair G F := by
  rw [signedPair_eq hF hG, signedPair_eq_swap hG hF]
  congr 1
  funext u
  congr 1
  funext v
  rw [real_inner_comm (u : Space n) (v : Space n), real_inner_comm (F u) (G v)]

lemma signedPair_add_left {n : ℕ} [NeZero n] {F G J : Sphere n → Space n}
    (hF : Continuous F) (hG : Continuous G) (hJ : Continuous J) :
    signedPair (fun u => F u+G u) J = signedPair F J+signedPair G J := by
  unfold signedPair
  simp_rw [inner_add_left, mul_add]
  exact integral_add (signedPair_integrable hF hJ) (signedPair_integrable hG hJ)

lemma signedPair_add_right {n : ℕ} [NeZero n] {F G J : Sphere n → Space n}
    (hF : Continuous F) (hG : Continuous G) (hJ : Continuous J) :
    signedPair F (fun u => G u+J u) = signedPair F G+signedPair F J := by
  unfold signedPair
  simp_rw [inner_add_right, mul_add]
  exact integral_add (signedPair_integrable hF hG) (signedPair_integrable hF hJ)

lemma signedPair_smul_left {n : ℕ} (F G : Sphere n → Space n) (c : ℝ) :
    signedPair (fun u => c • F u) G = c*signedPair F G := by
  unfold signedPair
  simp_rw [real_inner_smul_left, mul_left_comm _ c]
  exact integral_const_mul c _

lemma signedPair_smul_right {n : ℕ} (F G : Sphere n → Space n) (c : ℝ) :
    signedPair F (fun u => c • G u) = c*signedPair F G := by
  unfold signedPair
  simp_rw [real_inner_smul_right, mul_left_comm _ c]
  exact integral_const_mul c _

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.CosineSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma posPower_eq_max_pow {r : ℕ} (hr : 0 < r) (x : ℝ) :
    posPower r x = max x 0 ^ r := by
  by_cases hx : 0 < x
  · simp [posPower, hx, max_eq_left hx.le]
  · simp [posPower, hx, max_eq_right (not_lt.mp hx), hr.ne']

lemma higherKernel_const_pos {n : ℕ} [NeZero n] (r : ℕ) (u : Sphere n) :
    0 < higherKernel r u (fun _ => 1) := by
  have hc : Continuous (fun x : Sphere n => max ⟪(u : Space n),(x : Space n)⟫ 0 ^ r) := by
    fun_prop
  simp only [higherKernel, mul_one, mean]
  exact integral_pos_of_integrable_nonneg_nonzero hc (continuous_integrable hc)
    (fun x => pow_nonneg (le_max_right _ _) _) (x := u)
    (by rw [real_inner_self_eq_norm_sq, norm_coe]; norm_num)

lemma higherKernel_recurrence {n r d : ℕ} [NeZero n] (hr : 3 ≤ r)
    (u : Sphere n) {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (heig : ∀ x : Sphere n, casimir f x = -eigenvalue n d*f x) :
    (eigenvalue n r-eigenvalue n d)*higherKernel r u (fun x => f x) =
      (r : ℝ)*((r : ℝ)-1)*higherKernel (r-2) u (fun x => f x) := by
  let g : Space n → ℝ := fun y => posPower r ⟪(u : Space n),y⟫
  have hg : ContDiff ℝ 2 g := (posPower_contDiff_two hr).comp (innerSL ℝ (u : Space n)).contDiff
  have h := mean_casimir_comm hf hg
  have he (x : Sphere n) : f x*casimir g x =
      (r : ℝ)*((r : ℝ)-1)*((max ⟪(u : Space n),(x : Space n)⟫ 0)^(r-2)*f x) -
      eigenvalue n r*((max ⟪(u : Space n),(x : Space n)⟫ 0)^r*f x) := by
    rw [show casimir g x = _ from casimir_posPower_inner hr u x,
      posPower_eq_max_pow (show 0 < r-2 by omega), posPower_eq_max_pow (show 0 < r by omega)]
    ring
  simp_rw [he, heig, g, posPower_eq_max_pow (show 0 < r by omega)] at h
  have hct (r : ℕ) : Continuous (fun x : Sphere n => max ⟪(u : Space n),(x : Space n)⟫ 0 ^ r * f x) := by
    exact ((continuous_const.inner continuous_subtype_val).max continuous_const |>.pow r).mul
      (hf.continuous.comp continuous_subtype_val)
  have hh : (fun x : Sphere n => max ⟪(u : Space n),(x : Space n)⟫ 0 ^ r *
      (-eigenvalue n d*f x)) = fun x : Sphere n => -eigenvalue n d*
      (max ⟪(u : Space n),(x : Space n)⟫ 0 ^ r*f x) := by funext x; ring
  rw [hh, mean, integral_sub
    ((continuous_integrable (hct (r-2))).const_mul _) ((continuous_integrable (hct r)).const_mul _),
    integral_const_mul, integral_const_mul, mean, integral_const_mul] at h
  change (r : ℝ)*((r : ℝ)-1)*higherKernel (r-2) u (fun x => f x) -
    eigenvalue n r*higherKernel r u (fun x => f x) =
    -eigenvalue n d*higherKernel r u (fun x => f x) at h
  linarith

lemma higherKernel_const_recurrence {n r : ℕ} [NeZero n] (hr : 3 ≤ r) (u : Sphere n) :
    eigenvalue n r*higherKernel r u (fun _ => 1) =
      (r : ℝ)*((r : ℝ)-1)*higherKernel (r-2) u (fun _ => 1) := by
  have he (x : Sphere n) : casimir (fun _ : Space n => (1 : ℝ)) x = -eigenvalue n 0*1 := by
    have hc (T : Space n →L[ℝ] Space n) : rotDeriv T (fun _ : Space n => (1 : ℝ)) = fun _ => 0 :=
      funext (rotDeriv_const T 1)
    simp [casimir, hc, rotDeriv_const, eigenvalue]
  simpa [eigenvalue] using higherKernel_recurrence hr u contDiff_const he

lemma higherKernel_peak {n : ℕ} [NeZero n] (u : Sphere n) {f : Sphere n → ℝ}
    (hf : Continuous f) :
    Tendsto (fun r : ℕ => higherKernel r u f / higherKernel r u (fun _ => 1))
      atTop (𝓝 (f u)) := by
  have hc : Continuous (fun x : Sphere n => max ⟪(u : Space n),(x : Space n)⟫ 0) := by fun_prop
  have hmax (x : Sphere n) (_ : x ∈ (univ : Set (Sphere n))) (hne : x ≠ u) :
      max ⟪(u : Space n),(x : Space n)⟫ 0 < max ⟪(u : Space n),(u : Space n)⟫ 0 := by
    rw [real_inner_self_eq_norm_sq, norm_coe]
    norm_num only [one_pow, max_eq_left zero_le_one]
    apply max_lt
    · exact (inner_lt_one_iff_real_of_norm_eq_one (norm_coe u) (norm_coe x)).mpr
        (by intro h; exact hne (Subtype.ext h.symm))
    · norm_num
  have h := tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
    (μ := sigma n) isCompact_univ hc.continuousOn hmax
    (fun x _ => le_max_right _ _) (by rw [real_inner_self_eq_norm_sq, norm_coe]; norm_num)
    (by simp) hf.continuousOn
  simpa [smul_eq_mul, div_eq_mul_inv, higherKernel, mean, mul_comm] using h

end PettyProjection.Spherical
end

noncomputable section
open Filter Topology
namespace PettyProjection.Spherical

lemma higherFactor_zero (n : ℕ) (s : ℝ) : higherFactor n 0 s = 1 := by
  simp [higherFactor]

lemma higherFactor_succ (n j : ℕ) (s : ℝ) :
    higherFactor n (j+1) s = higherFactor n j s*((s-2*j)/(s+n+2*j)) := by
  simp only [higherFactor, Finset.prod_range_succ]

lemma higherFactor_step {n : ℕ} (hn : 2 ≤ n) (j : ℕ) {s : ℝ} (hs : 3 ≤ s) :
    (s-2*j)*(s+2*j+n-2)*higherFactor n j s =
      s*(s+n-2)*higherFactor n j (s-2) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  induction j with
  | zero => simp [higherFactor]
  | succ j ih =>
    rw [higherFactor_succ, higherFactor_succ]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have h₁ : s+n+2*j ≠ 0 := by linarith
    have h₂ : s-2+n+2*j ≠ 0 := by linarith
    push_cast
    field_simp
    linear_combination (s-2*j-2)*(s+n+2*j)*ih

lemma higherFactor_tendsto (n j : ℕ) :
    Tendsto (fun m : ℕ => higherFactor n j (2*m+1)) atTop (𝓝 1) := by
  induction j with
  | zero => simpa only [higherFactor_zero] using tendsto_const_nhds
  | succ j ih =>
    have h : Tendsto (fun m : ℕ => ((2*(m : ℝ)+1)-2*j)/((2*(m : ℝ)+1)+n+2*j)) atTop (𝓝 1) := by
      have h := tendsto_add_mul_div_add_mul_atTop_nhds (1-2*(j : ℝ))
        (1+n+2*(j : ℝ)) (2 : ℝ) (show (2 : ℝ) ≠ 0 by norm_num)
      convert! h using 1
      · funext m; congr 1 <;> ring
      · norm_num
    simpa only [higherFactor_succ, mul_one] using ih.mul h

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma eigenvalue_sub_even {n j : ℕ} (s : ℕ) :
    eigenvalue n s-eigenvalue n (2*j) =
      ((s : ℝ)-2*j)*((s : ℝ)+2*j+n-2) := by
  simp only [eigenvalue, Nat.cast_mul, Nat.cast_ofNat]
  ring

lemma eigenvalue_odd_sub_even_ne_zero {n : ℕ} (hn : 2 ≤ n) (m j : ℕ) :
    eigenvalue n (2*m+1)-eigenvalue n (2*j) ≠ 0 := by
  rw [eigenvalue_sub_even]
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    have h : (2*m+1 : ℕ) ≠ 2*j := by omega
    exact_mod_cast h
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    push_cast
    linarith

lemma higherKernel_normalized_recurrence {n r d : ℕ} [NeZero n] (hr : 3 ≤ r)
    (u : Sphere n) {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (heig : ∀ x : Sphere n, casimir f x = -eigenvalue n d*f x) :
    (eigenvalue n r-eigenvalue n d)*(higherKernel r u (fun x => f x)/higherKernel r u (fun _ => 1)) =
      eigenvalue n r*(higherKernel (r-2) u (fun x => f x)/higherKernel (r-2) u (fun _ => 1)) := by
  have h := higherKernel_recurrence hr u hf heig
  have hz := higherKernel_const_recurrence hr u
  have h₁ := (higherKernel_const_pos r u).ne'
  have h₂ := (higherKernel_const_pos (r-2) u).ne'
  field_simp
  linear_combination higherKernel (r-2) u (fun _ => 1)*h -
    higherKernel (r-2) u (fun x => f x)*hz

lemma higherKernel_eigenfunction {n j : ℕ} (hn : 2 ≤ n) [NeZero n]
    (u : Sphere n) {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (heig : ∀ x : Sphere n, casimir f x = -eigenvalue n (2*j)*f x) :
    higherKernel 1 u (fun x => f x)/higherKernel 1 u (fun _ => 1) =
      higherFactor n j 1*f u := by
  let A (m : ℕ) := higherKernel (2*m+1) u (fun x => f x)/higherKernel (2*m+1) u (fun _ => 1)
  let F (m : ℕ) := higherFactor n j (2*m+1)
  have hinv (m : ℕ) : A m*F 0 = A 0*F m := by
    induction m with
    | zero => rfl
    | succ m ih =>
      have hc := eigenvalue_odd_sub_even_ne_zero hn (m+1) j
      have hA := higherKernel_normalized_recurrence (show 3 ≤ 2*(m+1)+1 by omega) u hf heig
      rw [show 2*(m+1)+1-2 = 2*m+1 by omega] at hA
      change (eigenvalue n (2*(m+1)+1)-eigenvalue n (2*j))*A (m+1) =
        eigenvalue n (2*(m+1)+1)*A m at hA
      have hF : (eigenvalue n (2*(m+1)+1)-eigenvalue n (2*j))*F (m+1) =
          eigenvalue n (2*(m+1)+1)*F m := by
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
        have h := higherFactor_step hn j (s := 2*(m+1)+1) (by linarith)
        have he : (2*((m : ℝ)+1)+1)-2 = 2*m+1 := by ring
        rw [he] at h
        rw [eigenvalue_sub_even]
        simpa only [F, eigenvalue, Nat.cast_add,
          Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using h
      apply mul_left_cancel₀ hc
      calc
        _ = ((eigenvalue n (2*(m+1)+1)-eigenvalue n (2*j))*A (m+1))*F 0 := by ring
        _ = eigenvalue n (2*(m+1)+1)*(A m*F 0) := by rw [hA]; ring
        _ = eigenvalue n (2*(m+1)+1)*(A 0*F m) := by rw [ih]
        _ = A 0*((eigenvalue n (2*(m+1)+1)-eigenvalue n (2*j))*F (m+1)) := by rw [hF]; ring
        _ = _ := by ring
  have ht : Tendsto (fun m : ℕ => 2*m+1) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  have hA : Tendsto A atTop (𝓝 (f u)) :=
    (higherKernel_peak u (hf.continuous.comp continuous_subtype_val)).comp ht
  have hF : Tendsto F atTop (𝓝 1) := higherFactor_tendsto n j
  have hlim₁ := hA.mul (tendsto_const_nhds (x := F 0))
  have hlim₂ := (tendsto_const_nhds (x := A 0)).mul hF
  have heq : (fun m => A m*F 0) = (fun m => A 0*F m) := funext hinv
  rw [heq] at hlim₁
  have h := tendsto_nhds_unique hlim₁ hlim₂
  simpa [A, F, mul_comm] using h.symm

lemma higherKernel_harmonic {n j : ℕ} (hn : 2 ≤ n) [NeZero n]
    (u : Sphere n) {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous (2*j))
    (hΔ : laplacePolynomial p = 0) :
    higherKernel 1 u (fun x => polynomialFunction p x)/higherKernel 1 u (fun _ => 1) =
      higherFactor n j 1*polynomialFunction p u := by
  exact higherKernel_eigenfunction hn u ((polynomialFunction_contDiff p).of_le (by norm_num))
    (fun x => casimir_harmonic hp hΔ x)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma higherKernel_const_rotation {n : ℕ} (r : ℕ) (u : Sphere n)
    (U : Space n ≃ₗᵢ[ℝ] Space n) :
    higherKernel r (sphereMap U u) (fun _ => 1) = higherKernel r u (fun _ => 1) := by
  have h := mean_rotation U (fun x : Sphere n => max ⟪U (u : Space n),(x : Space n)⟫ 0 ^ r)
  change mean (fun x : Sphere n => max ⟪U (u : Space n),U (x : Space n)⟫ 0 ^ r) = _ at h
  simp only [U.inner_map_map] at h
  simp only [higherKernel, mul_one]
  change mean (fun x : Sphere n => max ⟪U (u : Space n),(x : Space n)⟫ 0 ^ r) = _
  exact h.symm

lemma higherKernel_const_independent {n : ℕ} (r : ℕ) (u v : Sphere n) :
    higherKernel r u (fun _ => 1) = higherKernel r v (fun _ => 1) := by
  let U := (ℝ ∙ ((u : Space n)-(v : Space n)))ᗮ.reflection
  have h : sphereMap U u = v := by
    apply Subtype.ext
    exact Submodule.reflection_sub ((norm_coe u).trans (norm_coe v).symm)
  rw [← h, higherKernel_const_rotation]

lemma cosineConstant_pos (n : ℕ) [NeZero n] : 0 < cosineConstant n :=
  mul_pos (by norm_num) (higherKernel_const_pos 1 (pole n))

lemma mean_pos_inner_even {n : ℕ} [NeZero n] (u : Sphere n) {f : Space n → ℝ}
    (heven : Function.Even f) (hf : Continuous f) :
    mean (fun x : Sphere n => |⟪(u : Space n),(x : Space n)⟫| *f x) =
      2*higherKernel 1 u (fun x => f x) := by
  have h := mean_rotation (LinearIsometryEquiv.neg ℝ : Space n ≃ₗᵢ[ℝ] Space n)
    (fun x : Sphere n => max ⟪(u : Space n),(x : Space n)⟫ 0*f x)
  have he : (fun x : Sphere n => max ⟪(u : Space n),((sphereMap (LinearIsometryEquiv.neg ℝ)) x : Space n)⟫ 0 *
      f (sphereMap (LinearIsometryEquiv.neg ℝ) x)) =
      (fun x : Sphere n => max (-⟪(u : Space n),(x : Space n)⟫) 0*f x) := by
    funext x
    change max ⟪(u : Space n),-(x : Space n)⟫ 0*f (-(x : Space n)) = _
    rw [inner_neg_right, heven]
  rw [he] at h
  have hk (t : ℝ) : |t| = max t 0+max (-t) 0 := by
    rcases le_total 0 t with ht | ht <;> simp [abs_of_nonneg, abs_of_nonpos, ht]
  simp only [higherKernel, pow_one]
  simp_rw [hk, add_mul]
  rw [mean, integral_add]
  · change mean (fun x : Sphere n => max ⟪(u : Space n),(x : Space n)⟫ 0*f x) +
      mean (fun x : Sphere n => max (-⟪(u : Space n),(x : Space n)⟫) 0*f x) = _
    rw [h]
    ring
  · exact continuous_integrable (by fun_prop)
  · exact continuous_integrable (by fun_prop)

lemma mean_abs_inner {n : ℕ} [NeZero n] (u : Sphere n) :
    mean (fun x : Sphere n => |⟪(u : Space n),(x : Space n)⟫|) = cosineConstant n := by
  have h := mean_pos_inner_even u (f := fun _ => 1) (fun _ => rfl) continuous_const
  simpa only [mul_one, higherKernel_const_independent 1 u (pole n), cosineConstant] using h

lemma cosine_const {n : ℕ} [NeZero n] (c : ℝ) : cosine (fun _ : Sphere n => c) = fun _ => c := by
  funext u
  rw [cosine, mean, integral_mul_const]
  change mean (fun x : Sphere n => |⟪(u : Space n),(x : Space n)⟫|)*c/cosineConstant n = c
  rw [mean_abs_inner]
  field_simp [(cosineConstant_pos n).ne']

lemma polynomialFunction_even {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (hd : Even d) : Function.Even (polynomialFunction p) := by
  intro x
  simpa only [neg_one_smul, hd.neg_one_pow, one_mul] using
    polynomialFunction_smul_argument hp (-1) x

lemma cosine_harmonic {n j : ℕ} (hn : 2 ≤ n) [NeZero n]
    {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous (2*j))
    (hΔ : laplacePolynomial p = 0) (u : Sphere n) :
    cosine (fun x => polynomialFunction p x) u = higherFactor n j 1*polynomialFunction p u := by
  rw [cosine, mean_pos_inner_even u (polynomialFunction_even hp (even_two_mul j))
    (polynomialFunction_contDiff p).continuous, cosineConstant,
    ← higherKernel_const_independent 1 u (pole n), mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
  exact higherKernel_harmonic hn u hp hΔ

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma cosine_selfadj {n : ℕ} [NeZero n] {f g : Sphere n → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    mean (fun u => f u*cosine g u) = mean (fun u => cosine f u*g u) := by
  have hi : Integrable (fun z : Sphere n × Sphere n =>
      f z.1 * (|⟪(z.1 : Space n),(z.2 : Space n)⟫| * g z.2)) ((sigma n).prod (sigma n)) :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_integral_swap (f := fun u v : Sphere n => f u*(|⟪(u : Space n),(v : Space n)⟫| * g v)) hi
  simp only [cosine, mean, ← mul_div_assoc, div_mul_eq_mul_div, integral_div, ← integral_const_mul]
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with v
  rw [real_inner_comm (u : Space n) (v : Space n)]
  ring

lemma mean_cosine {n : ℕ} [NeZero n] {f : Sphere n → ℝ} (hf : Continuous f) :
    mean (cosine f) = mean f := by
  have h := cosine_selfadj (f := fun _ => 1) continuous_const hf
  simpa only [one_mul, cosine_const] using h

lemma cosine_neg {n : ℕ} [NeZero n] (f : Sphere n → ℝ) (u : Sphere n) :
    cosine f (sphereMap (LinearIsometryEquiv.neg ℝ) u) = cosine f u := by
  unfold cosine
  congr 1
  congr 1
  funext x
  change |⟪-(u : Space n),(x : Space n)⟫| * f x = _
  rw [inner_neg_left, abs_neg]

lemma mean_sphere_even_mul_odd {n d : ℕ} {f : Sphere n → ℝ}
    (heven : ∀ u, f (sphereMap (LinearIsometryEquiv.neg ℝ) u) = f u)
    {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous d) (hd : Odd d) :
    mean (fun u : Sphere n => f u*polynomialFunction p u) = 0 := by
  have h := mean_rotation (LinearIsometryEquiv.neg ℝ : Space n ≃ₗᵢ[ℝ] Space n)
    (fun u : Sphere n => f u*polynomialFunction p u)
  have he : (fun u : Sphere n => f (sphereMap (LinearIsometryEquiv.neg ℝ) u)*
      polynomialFunction p (sphereMap (LinearIsometryEquiv.neg ℝ) u)) =
      (fun u : Sphere n => -(f u*polynomialFunction p u)) := by
    funext u
    rw [heven]
    change f u*polynomialFunction p (-(u : Space n)) = _
    rw [polynomialFunction_odd hp hd, mul_neg]
  rw [he, mean, integral_neg] at h
  change -mean (fun u : Sphere n => f u*polynomialFunction p u) = _ at h
  linarith

lemma cosine_projection_even {n j : ℕ} (hn : 2 ≤ n) [NeZero n] (f : C(Sphere n, ℝ)) :
    (harmonicSpace n (2*j)).starProjection (toH n (cosineMap f)) =
      higherFactor n j 1 • (harmonicSpace n (2*j)).starProjection (toH n f) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((harmonicSpace n (2*j)).smul_mem _ ((harmonicSpace n (2*j)).starProjection_apply_mem _))
  rintro v ⟨p, hp, rfl⟩
  rw [inner_sub_left, real_inner_smul_left, Submodule.inner_starProjection_left_eq_right]
  rw [Submodule.starProjection_eq_self_iff.mpr (show polynomialL2 n p ∈ harmonicSpace n (2*j) from ⟨p,hp,rfl⟩)]
  change ⟪toH n (cosineMap f),toH n (polynomialRestriction n p)⟫ -
    higherFactor n j 1 * ⟪toH n f,toH n (polynomialRestriction n p)⟫ = 0
  rw [inner_toH, inner_toH]
  change mean (fun u : Sphere n => cosine f u*(polynomialRestriction n p) u) - _ = 0
  rw [← cosine_selfadj f.continuous (polynomialRestriction n p).continuous]
  have he : (fun u : Sphere n => f u*cosine (polynomialRestriction n p) u) =
      (fun u : Sphere n => higherFactor n j 1*(f u*polynomialFunction p u)) := by
    funext u
    rw [show cosine (polynomialRestriction n p) u = _ from cosine_harmonic hn hp.1 hp.2 u]
    ring
  rw [he, mean, integral_const_mul]
  change _ - higherFactor n j 1 * (∫ u : Sphere n, f u * polynomialFunction p u ∂sigma n) = 0
  exact sub_self _

lemma cosine_projection_odd {n d : ℕ} [NeZero n] (f : C(Sphere n, ℝ)) (hd : Odd d) :
    (harmonicSpace n d).starProjection (toH n (cosineMap f)) = 0 := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  rintro v ⟨p, hp, rfl⟩
  rw [sub_zero]
  change ⟪toH n (cosineMap f),toH n (polynomialRestriction n p)⟫ = 0
  rw [inner_toH]
  exact mean_sphere_even_mul_odd (cosine_neg f) hp.1 hd

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.SignSpectrum
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

lemma signFactor_abs_step {n j : ℕ} (hn : 2 ≤ n) (hj : 1 ≤ j) {a : ℝ} (ha : 0 ≤ a) :
    |signFactor n (j+1) a| ≤ |signFactor n j a| := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hden : 0 < 1+(n : ℝ)+2*j := by linarith
  have he : 0 ≤ eigenvalue n (2*j) := by
    unfold eigenvalue
    push_cast
    apply mul_nonneg (by positivity)
    linarith
  have he' : 0 ≤ eigenvalue n (2*(j+1)) := by
    unfold eigenvalue
    push_cast
    apply mul_nonneg (by positivity)
    linarith
  have hb : (2*(j : ℝ)-1)*(1+a*eigenvalue n (2*(j+1))) ≤
      (1+(n : ℝ)+2*j)*(1+a*eigenvalue n (2*j)) := by
    have hpos : 0 ≤ a*(((n : ℝ)-2)*(2*j)*(2*j+n)+2*n) := by positivity
    simp only [eigenvalue, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    nlinarith
  simp only [signFactor, higherFactor_succ, abs_mul]
  rw [abs_div, abs_of_pos hden, abs_of_nonpos (by linarith : 1-2*(j : ℝ) ≤ 0), neg_sub,
    abs_of_nonneg (by positivity : 0 ≤ 1+a*eigenvalue n (2*(j+1))),
    abs_of_nonneg (by positivity : 0 ≤ 1+a*eigenvalue n (2*j))]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  simpa only [mul_comm] using hb

lemma signFactor_abs_le_four {n j : ℕ} (hn : 2 ≤ n) (hj : 2 ≤ j) {a : ℝ} (ha : 0 ≤ a) :
    |signFactor n j a| ≤ (1+a*(4*(n+2)))/((n+1)*(n+3)) := by
  have hstep : |signFactor n j a| ≤ |signFactor n 2 a| := by
    induction j, hj using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih => exact (signFactor_abs_step hn (by omega) ha).trans ih
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have he : signFactor n 2 a = -(1+a*(4*(n+2)))/((n+1)*(n+3)) := by
    norm_num [signFactor, higherFactor, Finset.prod_range_succ, eigenvalue]
    field_simp
    ring
  rw [he, abs_of_nonpos (by exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity) : -(1+a*(4*(n+2)))/((n+1)*(n+3)) ≤ 0)] at hstep
  simpa only [neg_div, neg_neg] using hstep

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology MvPolynomial
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma homogeneous_two_mem_harmonic_sup {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous 2) :
    polynomialL2 n p ∈ harmonicSpace n 0 ⊔ harmonicSpace n 2 := by
  have hs := homogeneous_mem_fischerSpan hn 2 hp
  clear hp
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j,l,p,hd,hp,hΔ,rfl⟩ := hx
    have hr : polynomialL2 n (radiusPolynomial n ^ j * p) = polynomialL2 n p := by
      change toH n (polynomialRestriction n _) = toH n (polynomialRestriction n p)
      rw [map_mul, map_pow, polynomialRestriction_radius, one_pow, one_mul]
    rw [hr]
    have hl : l = 0 ∨ l = 2 := by omega
    rcases hl with rfl | rfl
    · exact Submodule.mem_sup_left ⟨p,⟨hp,hΔ⟩,rfl⟩
    · exact Submodule.mem_sup_right ⟨p,⟨hp,hΔ⟩,rfl⟩
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using Submodule.add_mem _ hp hq
  | smul c p _ hp => simpa only [map_smul] using Submodule.smul_mem _ c hp

lemma lowSpace_eq {n : ℕ} (hn : 2 ≤ n) [NeZero n] :
    lowSpace n = harmonicSpace n 0 ⊔ harmonicSpace n 2 := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i,j⟩,rfl⟩
    change toH n (coordinateProduct n i j) ∈ _
    rw [← polynomialL2_X_mul_X]
    exact homogeneous_two_mem_harmonic_sup hn ((isHomogeneous_X ℝ i).mul (isHomogeneous_X ℝ j))
  · apply sup_le
    · intro v hv
      obtain ⟨c,rfl⟩ := harmonicSpace_zero_constant hv
      exact constant_mem_lowSpace n c
    · exact harmonicSpace_two_le_lowSpace n

lemma harmonic_inner_ne {n : ℕ} (hn : 2 ≤ n) [NeZero n] {d e : ℕ} (hde : d ≠ e)
    {v w : H n} (hv : v ∈ harmonicSpace n d) (hw : w ∈ harmonicSpace n e) :
    ⟪v,w⟫ = 0 := by
  exact harmonicSpace_orthogonal hn hde ⟨v,hv⟩ ⟨w,hw⟩

lemma lowSpace_projection {n : ℕ} (hn : 2 ≤ n) [NeZero n] (v : H n) :
    (lowSpace n).starProjection v = (harmonicSpace n 0).starProjection v +
      (harmonicSpace n 2).starProjection v := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [lowSpace_eq hn]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ((harmonicSpace n 0).starProjection_apply_mem v))
      (Submodule.mem_sup_right ((harmonicSpace n 2).starProjection_apply_mem v))
  · intro w hw
    rw [lowSpace_eq hn, Submodule.mem_sup] at hw
    obtain ⟨w0,hw0,w2,hw2,rfl⟩ := hw
    rw [inner_add_right]
    have h0 : ⟪(harmonicSpace n 2).starProjection v,w0⟫ = 0 :=
      harmonic_inner_ne hn (by decide) ((harmonicSpace n 2).starProjection_apply_mem v) hw0
    have h2 : ⟪(harmonicSpace n 0).starProjection v,w2⟫ = 0 :=
      harmonic_inner_ne hn (by decide) ((harmonicSpace n 0).starProjection_apply_mem v) hw2
    simp only [inner_sub_left, inner_add_left, h0, h2, add_zero, zero_add]
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hw0,
      Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hw2]
    ring

lemma Q_eq_sub_projections {n : ℕ} (hn : 2 ≤ n) [NeZero n] (v : H n) :
    Q n v = v - (harmonicSpace n 0).starProjection v - (harmonicSpace n 2).starProjection v := by
  rw [Q_eq_sub, lowSpace_projection hn, sub_add_eq_sub_sub]

lemma harmonic_projection_of_mem_ne {n : ℕ} (hn : 2 ≤ n) [NeZero n] {d e : ℕ} (hde : d ≠ e)
    {v : H n} (hv : v ∈ harmonicSpace n e) : (harmonicSpace n d).starProjection v = 0 := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  intro w hw
  rw [sub_zero]
  exact harmonic_inner_ne hn hde.symm hv hw

lemma harmonic_projection_Q {n d : ℕ} (hn : 2 ≤ n) [NeZero n] (v : H n) :
    (harmonicSpace n d).starProjection (Q n v) =
      if d = 0 ∨ d = 2 then 0 else (harmonicSpace n d).starProjection v := by
  rw [Q_eq_sub_projections hn, map_sub, map_sub]
  by_cases h0 : d = 0
  · subst d
    rw [ite_eq_left (Or.inl rfl), Submodule.starProjection_eq_self_iff.mpr ((harmonicSpace n _).starProjection_apply_mem v),
      harmonic_projection_of_mem_ne hn (by decide) ((harmonicSpace n 2).starProjection_apply_mem v)]
    simp
  · by_cases h2 : d = 2
    · subst d
      rw [ite_eq_left (Or.inr rfl), Submodule.starProjection_eq_self_iff.mpr ((harmonicSpace n _).starProjection_apply_mem v),
        harmonic_projection_of_mem_ne hn (by decide) ((harmonicSpace n 0).starProjection_apply_mem v)]
      simp
    · rw [ite_eq_right (not_or.mpr ⟨h0,h2⟩),
        harmonic_projection_of_mem_ne hn h0 ((harmonicSpace n 0).starProjection_apply_mem v),
        harmonic_projection_of_mem_ne hn h2 ((harmonicSpace n 2).starProjection_apply_mem v)]
      simp

end PettyProjection.Spherical
end

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {F : ℕ → Submodule ℝ E} [∀ i, CompleteSpace (F i)]

lemma hilbertSum_norm_le_of_projection_bound
    (h : IsHilbertSum ℝ (fun i => F i) (fun i => (F i).subtypeₗᵢ))
    (x y : E) {c : ℝ} (hc : 0 ≤ c)
    (hp : ∀ i, ‖(F i).starProjection y‖ ≤ c*‖(F i).starProjection x‖) :
    ‖y‖ ≤ c*‖x‖ := by
  have hsq : ‖y‖^2 ≤ c^2*‖x‖^2 := by
    apply hasSum_le _ (hilbertSum_hasSum_projection_norm_sq h y)
      (HasSum.mul_left (c^2) (hilbertSum_hasSum_projection_norm_sq h x))
    intro i
    have h := sq_le_sq₀ (norm_nonneg ((F i).starProjection y))
      (mul_nonneg hc (norm_nonneg ((F i).starProjection x))) |>.mpr (hp i)
    simpa only [mul_pow] using h
  nlinarith [norm_nonneg y, mul_nonneg hc (norm_nonneg x)]

omit [CompleteSpace E] in
lemma inner_projection_both (K : Submodule ℝ E) [CompleteSpace K] (x y : E) :
    ⟪K.starProjection x,K.starProjection y⟫ = ⟪x,K.starProjection y⟫ := by
  rw [Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem y)]

lemma hilbertSum_hasSum_inner
    (h : IsHilbertSum ℝ (fun i => F i) (fun i => (F i).subtypeₗᵢ)) (x y : E) :
    HasSum (fun i => ⟪(F i).starProjection x,(F i).starProjection y⟫) ⟪x,y⟫ := by
  simp only [inner_projection_both]
  exact (innerSL ℝ x).hasSum (hilbertSum_hasSum_projection h y)

lemma hilbertSum_multiplier_selfadj
    (h : IsHilbertSum ℝ (fun i => F i) (fun i => (F i).subtypeₗᵢ))
    (x y tx ty : E) (c : ℕ → ℝ)
    (hx : ∀ i, (F i).starProjection tx = c i • (F i).starProjection x)
    (hy : ∀ i, (F i).starProjection ty = c i • (F i).starProjection y) :
    ⟪x,ty⟫ = ⟪tx,y⟫ := by
  have h₁ := hilbertSum_hasSum_inner h x ty
  have h₂ := hilbertSum_hasSum_inner h tx y
  simp only [hx, hy, real_inner_smul_left, real_inner_smul_right] at h₁ h₂
  exact h₁.unique h₂

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma casimir_projection {n d : ℕ} [NeZero n] {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    (harmonicSpace n d).starProjection (toH n (casimirMap f hf)) =
      -eigenvalue n d • (harmonicSpace n d).starProjection (toH n (restrictContinuous f hf.continuous)) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((harmonicSpace n d).smul_mem _ ((harmonicSpace n d).starProjection_apply_mem _))
  rintro v ⟨p,hp,rfl⟩
  rw [inner_sub_left, real_inner_smul_left, Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (show polynomialL2 n p ∈ harmonicSpace n d from ⟨p,hp,rfl⟩)]
  change ⟪toH n (casimirMap f hf),toH n (polynomialRestriction n p)⟫ -
    (-eigenvalue n d)*⟪toH n (restrictContinuous f hf.continuous),toH n (polynomialRestriction n p)⟫ = 0
  rw [inner_toH, inner_toH]
  change mean (fun x : Sphere n => casimir f x*polynomialFunction p x) -
    (-eigenvalue n d)*mean (fun x : Sphere n => f x*polynomialFunction p x) = 0
  simp_rw [mul_comm (casimir f _)]
  rw [mean_casimir_comm ((polynomialFunction_contDiff p).of_le le_top) hf]
  simp_rw [casimir_harmonic hp.1 hp.2, mul_left_comm (f _) (-eigenvalue n d)]
  rw [mean, integral_const_mul]
  exact sub_self _

lemma signOperator_projection_even {n j : ℕ} (hn : 2 ≤ n) [NeZero n]
    (a : ℝ) {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    (harmonicSpace n (2*j)).starProjection (toH n (signOperator a f hf)) =
      signFactor n j a • (harmonicSpace n (2*j)).starProjection (toH n (restrictContinuous f hf.continuous)) := by
  rw [signOperator, cosine_projection_even hn, map_sub, map_smul, map_sub, map_smul,
    casimir_projection hf, smul_smul, smul_sub, smul_smul, ← sub_smul]
  congr 1
  unfold signFactor
  ring

lemma signOperator_projection_odd {n d : ℕ} [NeZero n]
    (a : ℝ) {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) (hd : Odd d) :
    (harmonicSpace n d).starProjection (toH n (signOperator a f hf)) = 0 :=
  cosine_projection_odd _ hd

lemma norm_Q_signOperator_le {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {a : ℝ} (ha : 0 ≤ a) {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    ‖Q n (toH n (signOperator a f hf))‖ ≤
      ((1+a*(4*(n+2)))/((n+1)*(n+3)))*‖Q n (toH n (restrictContinuous f hf.continuous))‖ := by
  apply hilbertSum_norm_le_of_projection_bound (harmonicSpace_isHilbertSum hn) _ _ (by positivity)
  intro d
  rw [harmonic_projection_Q hn, harmonic_projection_Q hn]
  split_ifs with hd
  · simp
  · by_cases he : Even d
    · obtain ⟨j,hj⟩ := he
      have hde : d = 2*j := by omega
      rw [hde]
      have hj2 : 2 ≤ j := by omega
      rw [signOperator_projection_even hn, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (signFactor_abs_le_four hn hj2 ha) (norm_nonneg _)
    · rw [signOperator_projection_odd a hf (Nat.not_even_iff_odd.mp he), norm_zero]
      positivity

lemma signOperator_selfadj {n : ℕ} (hn : 2 ≤ n) [NeZero n] (a : ℝ)
    {f g : Space n → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    mean (fun x : Sphere n => f x*signOperator a g hg x) =
      mean (fun x : Sphere n => signOperator a f hf x*g x) := by
  change mean (fun x => restrictContinuous f hf.continuous x*signOperator a g hg x) =
    mean (fun x => signOperator a f hf x*restrictContinuous g hg.continuous x)
  rw [← inner_toH n (restrictContinuous f hf.continuous) (signOperator a g hg),
    ← inner_toH n (signOperator a f hf) (restrictContinuous g hg.continuous)]
  let c : ℕ → ℝ := fun d => if Even d then signFactor n (d/2) a else 0
  apply hilbertSum_multiplier_selfadj (harmonicSpace_isHilbertSum hn) _ _ _ _ c
  all_goals
    intro d
    by_cases he : Even d
    · obtain ⟨j,hj⟩ := he
      have hd : d = 2*j := by omega
      rw [hd]
      simp only [c, even_two_mul, ↓reduceIte, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
      exact signOperator_projection_even hn a _
    · simp only [c, he, ↓reduceIte, zero_smul]
      exact signOperator_projection_odd a _ (Nat.not_even_iff_odd.mp he)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma cosine_sub_smul {n : ℕ} [NeZero n] {f g : Sphere n → ℝ}
    (hf : Continuous f) (hg : Continuous g) (a : ℝ) (u : Sphere n) :
    cosine (fun x => f x-a*g x) u = cosine f u-a*cosine g u := by
  unfold cosine mean
  simp_rw [mul_sub, mul_left_comm _ a]
  rw [integral_sub (continuous_integrable (by fun_prop)) (continuous_integrable (by fun_prop)),
    integral_const_mul]
  ring

lemma signOperator_apply {n : ℕ} [NeZero n] (a : ℝ) {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (u : Sphere n) :
    signOperator a f hf u = cosine (fun x : Sphere n => f x) u -
      a*cosine (fun x : Sphere n => casimir f x) u := by
  exact cosine_sub_smul (hf.continuous.comp continuous_subtype_val)
    ((casimir_continuous hf).comp continuous_subtype_val) a u

lemma casimir_const {n : ℕ} (c : ℝ) : casimir (fun _ : Space n => c) = 0 := by
  have hr (X : Space n →L[ℝ] Space n) : rotDeriv X (fun _ => c) = 0 := by
    ext x
    simp [rotDeriv]
  ext x
  simp [casimir, hr, rotDeriv]

lemma mean_casimir_zero {n : ℕ} [NeZero n] {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    mean (fun x : Sphere n => casimir f x) = 0 := by
  have h := mean_casimir_comm (f := fun _ => 1) contDiff_const hf
  simpa only [one_mul, casimir_const, Pi.zero_apply, mul_zero, mean, integral_zero] using h

lemma mean_signOperator {n : ℕ} [NeZero n] (a : ℝ) {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) : mean (signOperator a f hf) = mean (fun x : Sphere n => f x) := by
  rw [signOperator, show (cosineMap (restrictContinuous f hf.continuous - a • casimirMap f hf) : Sphere n → ℝ) =
      cosine (restrictContinuous f hf.continuous - a • casimirMap f hf) from rfl,
    mean_cosine (ContinuousMap.continuous _)]
  change mean (fun x : Sphere n => f x-a*casimir f x) = _
  unfold mean
  rw [integral_sub (f := fun x : Sphere n => f x) (g := fun x : Sphere n => a*casimir f x)
    (continuous_integrable (hf.continuous.comp continuous_subtype_val))
    (continuous_integrable (continuous_const.mul ((casimir_continuous hf).comp continuous_subtype_val))),
    integral_const_mul]
  change mean (fun x : Sphere n => f x) - a*mean (fun x : Sphere n => casimir f x) = _
  rw [mean_casimir_zero hf, mul_zero, sub_zero]
  rfl

lemma mean_signOperator_expand {n : ℕ} [NeZero n] (a : ℝ) {f g : Space n → ℝ}
    (hf : Continuous f) (hg : ContDiff ℝ 2 g) :
    mean (fun x : Sphere n => f x*signOperator a g hg x) =
      mean (fun x : Sphere n => f x*cosine (fun y : Sphere n => g y) x) -
        a*mean (fun x : Sphere n => f x*cosine (fun y : Sphere n => casimir g y) x) := by
  simp_rw [signOperator_apply, mul_sub, mul_left_comm (f _) a]
  exact (integral_sub
    (continuous_integrable ((hf.comp continuous_subtype_val).mul (cosine_continuous (hg.continuous.comp continuous_subtype_val))))
    (continuous_integrable (continuous_const.mul ((hf.comp continuous_subtype_val).mul
      (cosine_continuous ((casimir_continuous hg).comp continuous_subtype_val)))))).trans
    (by
      change _ - (∫ x : Sphere n, a * (f x * cosine (fun y : Sphere n => casimir g y) x) ∂sigma n) = _
      rw [integral_const_mul]
      rfl)

lemma cosine_casimir_selfadj {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {f g : Space n → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    mean (fun x : Sphere n => f x*cosine (fun y : Sphere n => casimir g y) x) =
      mean (fun x : Sphere n => g x*cosine (fun y : Sphere n => casimir f y) x) := by
  have h := signOperator_selfadj hn 1 hf hg
  simp_rw [mul_comm (signOperator 1 f hf _)] at h
  rw [mean_signOperator_expand 1 hf.continuous hg, mean_signOperator_expand 1 hg.continuous hf] at h
  have hc := cosine_selfadj (hf.continuous.comp continuous_subtype_val)
    (hg.continuous.comp continuous_subtype_val)
  simp_rw [mul_comm (cosine _ _)] at hc
  change (mean (fun x : Sphere n => f x * cosine (fun y : Sphere n => g y) x)) =
    mean (fun x : Sphere n => g x * cosine (fun y : Sphere n => f y) x) at hc
  linarith

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma inner_Q_Q {n : ℕ} [NeZero n] (x y : H n) :
    ⟪Q n x,Q n y⟫ = ⟪Q n x,y⟫ := by
  change ⟪(lowSpace n)ᗮ.starProjection x,(lowSpace n)ᗮ.starProjection y⟫ = _
  rw [Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr ((lowSpace n)ᗮ.starProjection_apply_mem y)]
  exact (Submodule.inner_starProjection_left_eq_right _ _ _).symm

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma radialField_continuous {n : ℕ} {f : Space n → ℝ} (hf : Continuous f) :
    Continuous (radialField f) := (hf.comp continuous_subtype_val).smul continuous_subtype_val

lemma tangentField_continuous {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (tangentField f) := (sphereGradient_continuous hf).comp continuous_subtype_val

lemma signedPair_radial_radial {n : ℕ} [NeZero n] {f g : Space n → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    signedPair (radialField f) (radialField g) = cosineConstant n *
      mean (fun u : Sphere n => f u*cosine (fun v : Sphere n => g v) u) := by
  rw [signedPair_eq (radialField_continuous hf) (radialField_continuous hg)]
  have hi (u v : Sphere n) :
      Real.sign ⟪(u : Space n),(v : Space n)⟫ * ⟪radialField f u,radialField g v⟫ =
        f u*(|⟪(u : Space n),(v : Space n)⟫| * g v) := by
    simp only [radialField, real_inner_smul_left, real_inner_smul_right]
    calc
      _ = (Real.sign ⟪(u : Space n),(v : Space n)⟫ * ⟪(u : Space n),(v : Space n)⟫)*f u*g v := by ring
      _ = _ := by rw [sign_mul_self]; ring
  simp_rw [hi, mean, integral_const_mul]
  simp only [cosine, mean, ← mul_div_assoc, integral_div]
  field_simp [(cosineConstant_pos n).ne']

lemma signedPair_tangent_radial {n : ℕ} [NeZero n] {f g : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : Continuous g) :
    signedPair (tangentField f) (radialField g) = -cosineConstant n *
      mean (fun u : Sphere n => g u*cosine (fun v : Sphere n => casimir f v) u) := by
  rw [signedPair_eq_swap (tangentField_continuous (hf.of_le (by norm_num))) (radialField_continuous hg)]
  have hi (u v : Sphere n) :
      Real.sign ⟪(u : Space n),(v : Space n)⟫ * ⟪tangentField f u,radialField g v⟫ =
        g v*(Real.sign ⟪(v : Space n),(u : Space n)⟫*⟪sphereGradient f u,(v : Space n)⟫) := by
    simp only [radialField, tangentField, real_inner_smul_right]
    rw [real_inner_comm (u : Space n) (v : Space n)]
    ring
  simp_rw [hi, mean, integral_const_mul]
  change mean (fun v : Sphere n => g v * mean (fun u : Sphere n =>
    Real.sign ⟪(v : Space n),(u : Space n)⟫ * ⟪sphereGradient f u,(v : Space n)⟫)) = _
  simp_rw [mean_sign_gradient_radial hf]
  simp only [cosine, mean, ← mul_div_assoc, integral_div, mul_neg]
  rw [integral_neg]
  have hb := (cosineConstant_pos n).ne'
  field_simp

lemma signedPair_tangent_tangent {n : ℕ} [NeZero n] {f g : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    signedPair (tangentField f) (tangentField g) = ((n : ℝ)-1)*
      signedPair (radialField f) (tangentField g) := by
  rw [signedPair_eq_swap (tangentField_continuous hf) (tangentField_continuous hg),
    signedPair_eq_swap (radialField_continuous hf.continuous) (tangentField_continuous hg)]
  have hi (v : Sphere n) :
      mean (fun u : Sphere n => Real.sign ⟪(u : Space n),(v : Space n)⟫ * ⟪tangentField f u,tangentField g v⟫) =
        ((n : ℝ)-1)*mean (fun u : Sphere n => Real.sign ⟪(u : Space n),(v : Space n)⟫ * ⟪radialField f u,tangentField g v⟫) := by
    have h := mean_sign_gradient_tangent hf (v : Space n) (sphereGradient g v)
      (by rw [real_inner_comm]; exact sphereGradient_tangent g v)
    convert h using 1
    · congr 1
      funext u
      rw [real_inner_comm (u : Space n) (v : Space n)]
      rfl
    · congr 1
      congr 1
      funext u
      simp only [radialField, tangentField, real_inner_smul_left]
      rw [real_inner_comm (u : Space n) (v : Space n)]
      ring
  simp_rw [hi]
  exact integral_const_mul _ _

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma signField_continuous {n : ℕ} (k : ℝ) {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (signField k f) :=
  (radialField_continuous hf.continuous).add ((tangentField_continuous hf).const_smul k⁻¹)

lemma signedPair_fields {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    (k : ℝ) {f g : Space n → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    signedPair (signField k f) (signField k g) = cosineConstant n *
      mean (fun u : Sphere n => f u*signOperator (2/k+((n : ℝ)-1)/k^2) g hg u) := by
  have hf1 := hf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hg1 := hg.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hrf := radialField_continuous hf.continuous
  have hrg := radialField_continuous hg.continuous
  have htf := tangentField_continuous hf1
  have htg := tangentField_continuous hg1
  have hktf : Continuous (fun u => k⁻¹ • tangentField f u) := htf.const_smul k⁻¹
  have hktg : Continuous (fun u => k⁻¹ • tangentField g u) := htg.const_smul k⁻¹
  have hrt : signedPair (radialField f) (tangentField g) = -cosineConstant n *
      mean (fun u : Sphere n => f u*cosine (fun v : Sphere n => casimir g v) u) := by
    rw [signedPair_symm hrf htg]
    exact signedPair_tangent_radial hg hf.continuous
  have htr : signedPair (tangentField f) (radialField g) = -cosineConstant n *
      mean (fun u : Sphere n => f u*cosine (fun v : Sphere n => casimir g v) u) := by
    rw [signedPair_tangent_radial hf hg.continuous, cosine_casimir_selfadj hn hg hf]
  change signedPair (fun u => radialField f u+k⁻¹ • tangentField f u)
    (fun u => radialField g u+k⁻¹ • tangentField g u) = _
  rw [signedPair_add_left hrf hktf (show Continuous (fun u => radialField g u+k⁻¹ • tangentField g u) from signField_continuous k hg1),
    signedPair_add_right hrf hrg hktg,
    signedPair_add_right hktf hrg hktg,
    signedPair_smul_right, signedPair_smul_left, signedPair_smul_left, signedPair_smul_right,
    signedPair_radial_radial hf.continuous hg.continuous,
    signedPair_tangent_tangent hf1 hg1, hrt, htr,
    mean_signOperator_expand _ hf.continuous hg]
  simp only [div_eq_mul_inv]
  ring

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.NormRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma norm_gradient_eq {n : ℕ} (f : Space n → ℝ) (x : Space n) :
    ‖∇ f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ (Space n)).symm.norm_map _

lemma gradient_pow {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (k : ℕ) :
    ∇ (fun y => f y^k) x = ((k : ℝ)*f x^(k-1)) • ∇ f x := by
  apply (InnerProductSpace.toDual ℝ (Space n)).injective
  rw [toDual_gradient, map_smul, toDual_gradient]
  simpa only [nsmul_eq_mul] using (hf.hasFDerivAt.pow k).fderiv

lemma signField_eq_gradient {n : ℕ} (k : ℝ) (f : Space n → ℝ) (u : Sphere n) :
    signField k f u = f u • (u : Space n) +
      k⁻¹ • (∇ f u - ⟪∇ f u,(u : Space n)⟫ • (u : Space n)) := by
  rw [inner_gradient_left]
  rfl

lemma norm_signField_le {n : ℕ} (k : ℝ) (f : Space n → ℝ) (u : Sphere n) :
    ‖signField k f u‖ ≤ |f u| + 2*|k⁻¹| *‖fderiv ℝ f u‖ := by
  rw [signField_eq_gradient]
  calc
    _ ≤ ‖f u • (u : Space n)‖ + ‖k⁻¹ • (∇ f u - ⟪∇ f u,(u : Space n)⟫ • (u : Space n))‖ := norm_add_le _ _
    _ ≤ |f u| + |k⁻¹| *(‖∇ f u‖ + |⟪∇ f u,(u : Space n)⟫|) := by
      simp only [norm_smul, norm_coe, mul_one, Real.norm_eq_abs]
      gcongr
      have h := norm_sub_le (∇ f u) (⟪∇ f u,(u : Space n)⟫ • (u : Space n))
      simpa only [norm_smul, norm_coe, mul_one, Real.norm_eq_abs] using h
    _ ≤ |f u| + |k⁻¹| *(‖∇ f u‖ + ‖∇ f u‖) := by
      gcongr
      simpa only [norm_coe, mul_one] using abs_real_inner_le_norm (∇ f u) (u : Space n)
    _ = _ := by rw [norm_gradient_eq]; ring

lemma normSmooth_powerField_bound {n : ℕ} (g : Seminorm ℝ (Space n)) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j (u : Sphere n),
      ‖signField (k : ℝ) (fun x => normSmooth g (shrinkingBump n j) x^k) u‖ ≤ B := by
  obtain ⟨C,hC⟩ := seminorm_lipschitz n g
  let M : ℝ := 2*C
  have hM : 0 ≤ M := by positivity
  have hv (j : ℕ) (u : Sphere n) : |normSmooth g (shrinkingBump n j) u| ≤ M := by
    have hg : |g u| ≤ C := by
      have h := hC.dist_le_mul (u : Space n) 0
      simpa only [map_zero, dist_zero_right, norm_coe, mul_one, Real.norm_eq_abs] using h
    have he := normSmooth_dist_le g (shrinkingBump n j) hC u
    have hr : (shrinkingBump n j).rOut ≤ 1 := by
      change 1 / ((j : ℝ)+1) ≤ 1
      exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
    have hc := mul_le_mul_of_nonneg_left hr C.coe_nonneg
    have ht := abs_add_le (normSmooth g (shrinkingBump n j) u-g u) (g u)
    rw [sub_add_cancel] at ht
    rw [Real.dist_eq] at he
    dsimp [M]
    linarith
  have hd (j : ℕ) (u : Sphere n) :
      ‖fderiv ℝ (fun x => normSmooth g (shrinkingBump n j) x^k) u‖ ≤
        (k : ℝ) * M^(k-1) * C := by
    have hdiff := (normSmooth_contDiff g (shrinkingBump n j)).differentiable (by norm_num) (u : Space n)
    rw [(hdiff.hasFDerivAt.pow k).fderiv, norm_smul, Real.norm_eq_abs,
      nsmul_eq_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k), abs_pow]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hv j u) _) (Nat.cast_nonneg _))
      (norm_fderiv_le_of_lipschitz ℝ (normSmooth_lipschitz g _ hC)) (norm_nonneg _) (by positivity)
  refine ⟨M^k + 2*|(k : ℝ)⁻¹| *((k : ℝ)*M^(k-1)*C), by positivity, ?_⟩
  intro j u
  exact (norm_signField_le _ _ u).trans (add_le_add
    (by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hv j u) k)
    (mul_le_mul_of_nonneg_left (hd j u) (by positivity)))

lemma normSmooth_powerField_tendsto {n : ℕ} (g : Seminorm ℝ (Space n)) (k : ℕ) :
    ∀ᵐ (u : Sphere n) ∂sigma n,
      Tendsto (fun j => signField (k : ℝ) (fun x => normSmooth g (shrinkingBump n j) x^k) u)
        atTop (𝓝 (signField (k : ℝ) (fun x => g x^k) u)) := by
  filter_upwards [seminorm_ae_differentiable_sphere g] with u hu
  have hg : Tendsto (fun j => ∇ (fun x => normSmooth g (shrinkingBump n j) x^k) u)
      atTop (𝓝 (∇ (fun x => g x^k) u)) := by
    simp_rw [gradient_pow ((normSmooth_contDiff g _).differentiable (by norm_num) (u : Space n)) k, gradient_pow hu k]
    exact (((normSmooth_tendsto g u).pow (k-1)).const_mul (k : ℝ)).smul (normSmooth_gradient_tendsto g hu)
  simp_rw [signField_eq_gradient]
  exact ((normSmooth_tendsto g u).pow k).smul_const (u : Space n) |>.add
    ((hg.sub ((hg.inner (tendsto_const_nhds (x := (u : Space n)))).smul_const (u : Space n))).const_smul (k : ℝ)⁻¹)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma signedPair_tendsto {n : ℕ} [NeZero n] {F G : ℕ → Sphere n → Space n}
    {F₀ G₀ : Sphere n → Space n} {B C : ℝ} (hB : 0 ≤ B)
    (hF : ∀ j, Continuous (F j)) (hG : ∀ j, Continuous (G j))
    (hFB : ∀ j u, ‖F j u‖ ≤ B) (hGC : ∀ j u, ‖G j u‖ ≤ C)
    (hFlim : ∀ᵐ u ∂sigma n, Tendsto (fun j => F j u) atTop (𝓝 (F₀ u)))
    (hGlim : ∀ᵐ u ∂sigma n, Tendsto (fun j => G j u) atTop (𝓝 (G₀ u))) :
    Tendsto (fun j => signedPair (F j) (G j)) atTop (𝓝 (signedPair F₀ G₀)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => B*C)
  · intro j
    exact (signedPair_integrable (hF j) (hG j)).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (abs_sign_le _) (abs_real_inner_le_norm _ _) (abs_nonneg _) (by norm_num)).trans
      (by simpa only [one_mul] using mul_le_mul (hFB j z.1) (hGC j z.2) (norm_nonneg _) hB)
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hFlim,
      Measure.quasiMeasurePreserving_snd.ae hGlim] with z hzF hzG
    exact (hzF.inner hzG).const_mul _

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma inner_Q_Q_expand {n : ℕ} (hn : 2 ≤ n) [NeZero n] (f g : C(Sphere n, ℝ)) :
    ⟪Q n (toH n f),Q n (toH n g)⟫ = mean (fun u => f u*g u) - mean f*mean g -
      ⟪(harmonicSpace n 2).starProjection (toH n f),(harmonicSpace n 2).starProjection (toH n g)⟫ := by
  rw [inner_Q_Q, Q_eq_sub_projections hn, inner_sub_left, inner_sub_left,
    harmonicSpace_zero_projection, inner_toH, inner_toH]
  have h : mean (fun u => (mean f)*g u) = mean f*mean g := integral_const_mul (mean f) g
  change _ - mean (fun u => mean f*g u) - _ = _
  rw [h]
  congr 1
  have hs := Submodule.inner_starProjection_left_eq_right (harmonicSpace n 2)
    (toH n f) ((harmonicSpace n 2).starProjection (toH n g))
  rw [Submodule.starProjection_eq_self_iff.mpr ((harmonicSpace n 2).starProjection_apply_mem _)] at hs
  exact (Submodule.inner_starProjection_left_eq_right _ _ _).trans hs.symm

lemma sign_spectral_estimate_with_two {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {a : ℝ} (ha : 0 ≤ a) (f : C(Sphere n, ℝ)) {g : Space n → ℝ}
    (hg : ContDiff ℝ 2 g) :
    mean f*mean (fun x : Sphere n => g x) -
      ((1+a*(4*(n+2)))/((n+1)*(n+3)))*‖Q n (toH n f)‖*
        ‖Q n (toH n (restrictContinuous g hg.continuous))‖ -
      |signFactor n 1 a| * ‖(harmonicSpace n 2).starProjection (toH n f)‖ *
        ‖(harmonicSpace n 2).starProjection (toH n (restrictContinuous g hg.continuous))‖ ≤
      mean (fun x => f x*signOperator a g hg x) := by
  have hi := inner_Q_Q_expand hn f (signOperator a g hg)
  rw [mean_signOperator] at hi
  have hfat := signOperator_projection_even (j := 1) hn a hg
  norm_num only [Nat.mul_one] at hfat
  rw [hfat, real_inner_smul_right] at hi
  have hcs := neg_le_of_abs_le (abs_real_inner_le_norm
    (Q n (toH n f)) (Q n (toH n (signOperator a g hg))))
  have hb := mul_le_mul_of_nonneg_left (norm_Q_signOperator_le hn ha hg)
    (norm_nonneg (Q n (toH n f)))
  have hab := mul_le_mul_of_nonneg_left
    (abs_real_inner_le_norm ((harmonicSpace n 2).starProjection (toH n f))
      ((harmonicSpace n 2).starProjection (toH n (restrictContinuous g hg.continuous))))
      (abs_nonneg (signFactor n 1 a))
  rw [← abs_mul] at hab
  have htwo := neg_le_of_abs_le hab
  rw [hi] at hcs
  nlinarith

lemma sign_form_estimate_with_two {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    {k : ℝ} (hk : 0 < k) {f g : Space n → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    mean (fun u : Sphere n => f u)*mean (fun u : Sphere n => g u) -
      ((1+(2/k+((n : ℝ)-1)/k^2)*(4*(n+2)))/((n+1)*(n+3)))*
        ‖Q n (toH n (restrictContinuous f hf.continuous))‖*
        ‖Q n (toH n (restrictContinuous g hg.continuous))‖ -
      |signFactor n 1 (2/k+((n : ℝ)-1)/k^2)| *
        ‖(harmonicSpace n 2).starProjection (toH n (restrictContinuous f hf.continuous))‖ *
        ‖(harmonicSpace n 2).starProjection (toH n (restrictContinuous g hg.continuous))‖ ≤
      signedPair (signField k f) (signField k g)/cosineConstant n := by
  rw [signedPair_fields hn k hf hg, mul_div_cancel_left₀ _ (cosineConstant_pos n).ne']
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  exact sign_spectral_estimate_with_two hn (a := 2/k+((n : ℝ)-1)/k^2) (by positivity) (restrictContinuous f hf.continuous) hg

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma normSmooth_power_restrict_tendsto {n : ℕ} (g : Seminorm ℝ (Space n)) (k : ℕ) :
    Tendsto (fun j => restrictContinuous (fun x => normSmooth g (shrinkingBump n j) x^k)
      ((normSmooth_contDiff g _).continuous.pow k)) atTop
      (𝓝 (restrictContinuous (fun x => g x^k) ((seminorm_continuous n g).pow k))) := by
  obtain ⟨F,R,hF,_,hFt,_⟩ := seminorm_approximation g
  have h := hFt.pow k
  simp only [hF] at h
  convert h using 1 <;> congr 1

lemma norm_signedPair_tendsto {n : ℕ} [NeZero n]
    (f g : Seminorm ℝ (Space n)) (k : ℕ) :
    Tendsto (fun j => signedPair
      (signField (k : ℝ) (fun x => normSmooth f (shrinkingBump n j) x^k))
      (signField (k : ℝ) (fun x => normSmooth g (shrinkingBump n j) x^k))) atTop
      (𝓝 (signedPair (signField (k : ℝ) (fun x => f x^k))
        (signField (k : ℝ) (fun x => g x^k)))) := by
  obtain ⟨B,hB,hFB⟩ := normSmooth_powerField_bound f k
  obtain ⟨C,_,hGC⟩ := normSmooth_powerField_bound g k
  exact signedPair_tendsto hB
    (fun j => signField_continuous _ ((normSmooth_contDiff f _).pow k |>.of_le (by norm_num)))
    (fun j => signField_continuous _ ((normSmooth_contDiff g _).pow k |>.of_le (by norm_num)))
    hFB hGC (normSmooth_powerField_tendsto f k) (normSmooth_powerField_tendsto g k)

/-- The sign-transform lower bound for powers of arbitrary nonsmooth norms. -/
theorem norm_sign_form_oai {n : ℕ} (hn : 2 ≤ n) [NeZero n]
    (f g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k)
    (h2 : (harmonicSpace n 2).starProjection (toH n
      (restrictContinuous (fun x => f x^k) ((seminorm_continuous n f).pow k))) = 0) :
    mean (fun u : Sphere n => f u^k)*mean (fun u : Sphere n => g u^k) -
      ((1+(2/(k : ℝ)+((n : ℝ)-1)/(k : ℝ)^2)*(4*(n+2)))/((n+1)*(n+3)))*
        ‖Q n (toH n (restrictContinuous (fun x => f x^k) ((seminorm_continuous n f).pow k)))‖*
        ‖Q n (toH n (restrictContinuous (fun x => g x^k) ((seminorm_continuous n g).pow k)))‖ ≤
      signedPair (signField (k : ℝ) (fun x => f x^k))
        (signField (k : ℝ) (fun x => g x^k))/cosineConstant n := by
  have hF := normSmooth_power_restrict_tendsto f k
  have hG := normSmooth_power_restrict_tendsto g k
  have hmF := (continuous_mean.tendsto _).comp hF
  have hmG := (continuous_mean.tendsto _).comp hG
  have hqF := (((Q n).continuous.comp (toH n).continuous).norm.tendsto _).comp hF
  have hqG := (((Q n).continuous.comp (toH n).continuous).norm.tendsto _).comp hG
  have hpF := ((((harmonicSpace n 2).starProjection.continuous.comp (toH n).continuous).norm).tendsto _).comp hF
  have hpG := ((((harmonicSpace n 2).starProjection.continuous.comp (toH n).continuous).norm).tendsto _).comp hG
  have hleft := ((hmF.mul hmG).sub ((hqF.const_mul
    ((1+(2/(k : ℝ)+((n : ℝ)-1)/(k : ℝ)^2)*(4*(n+2)))/((n+1)*(n+3)))).mul hqG)).sub
      ((hpF.const_mul |signFactor n 1 (2/(k : ℝ)+((n : ℝ)-1)/(k : ℝ)^2)|).mul hpG)
  simp only [Function.comp_apply] at hleft
  rw [h2, norm_zero, mul_zero, zero_mul, sub_zero] at hleft
  exact le_of_tendsto_of_tendsto hleft ((norm_signedPair_tendsto f g k).div_const (cosineConstant n))
    (Eventually.of_forall fun j => sign_form_estimate_with_two hn (by exact_mod_cast hk)
      ((normSmooth_contDiff f _).pow k |>.of_le (by norm_num))
      ((normSmooth_contDiff g _).pow k |>.of_le (by norm_num)))

end PettyProjection.Spherical
end

end OAI
end

theorem solution : type_of% @OAI.PettyProjection.Spherical.norm_sign_form_oai := @OAI.PettyProjection.Spherical.norm_sign_form_oai
