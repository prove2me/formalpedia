-- Prove2me | solution 1 for OAI.PettyProjection.measure_bilinear
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:12:41.029694+00:00
-- url     : https://prove2.me/submissions/22ca34e6-b1ec-47fe-b740-5614f5ba1f88

import Mathlib
import Definitions.Def_PettyProjectionVolume
import Definitions.Def_OAIQWPP000
import Theorems.Thm_OAI_PettyProjection_RelativeGauge_exists_symmetric_position
import Theorems.Thm_OAI_PettyProjection_Spherical_norm_estimate
import Theorems.Thm_OAI_PettyProjection_Spherical_norm_sign_form

section
-- module Solutions.OAIQW_PettyProjection.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
namespace OAI.PettyProjection
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434
end OAI.PettyProjection
end

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

lemma polynomialRestriction_apply {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (u : Sphere n) :
    polynomialRestriction n p u = polynomialFunction p u := rfl

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

lemma constant_mem_harmonicSpace_zero (n : ℕ) [NeZero n] (c : ℝ) :
    toH n (ContinuousMap.const (Sphere n) c) ∈ harmonicSpace n 0 := by
  refine Submodule.mem_map.mpr ⟨C c, ⟨isHomogeneous_C _ _, ?_⟩, ?_⟩
  · simp [LinearMap.mem_ker, laplaceLinear, laplacePolynomial]
  · change toH n (polynomialRestriction n (C c)) = _
    congr 1
    ext u
    exact congrFun (polynomialFunction_C _) _

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
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection

lemma support_linear_image {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    (T : Space n →L[ℝ] Space n) (u : Space n) :
    support (T '' K) u = support K (T.adjoint u) := by
  apply le_antisymm
  · apply (support_le_iff (hK.image T.continuous) (hKn.image T)).mpr
    rintro _ ⟨x,hx,rfl⟩
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact inner_le_support hK hx _
  · obtain ⟨x,hx,he⟩ := support_attained hK hKn (T.adjoint u)
    rw [he,ContinuousLinearMap.adjoint_inner_left]
    exact inner_le_support (hK.image T.continuous) (mem_image_of_mem T hx) u

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal RealInnerProductSpace Pointwise
namespace PettyProjection.Spherical

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
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma wulff_closed {n : ℕ} (s : Sphere n → ℝ) : IsClosed (wulff s) := by
  unfold wulff
  rw [ofPred_forall]
  exact isClosed_iInter (fun _ => isClosed_le (by fun_prop) continuous_const)

lemma wulff_convex {n : ℕ} (s : Sphere n → ℝ) : Convex ℝ (wulff s) := by
  intro x hx y hy a b ha hb hab u
  rw [inner_add_right,real_inner_smul_right,real_inner_smul_right]
  calc
    _ ≤ a*s u+b*s u := add_le_add (mul_le_mul_of_nonneg_left (hx u) ha)
      (mul_le_mul_of_nonneg_left (hy u) hb)
    _ = s u := by rw [← add_mul,hab,one_mul]

lemma closedBall_subset_wulff {n : ℕ} {s : Sphere n → ℝ} {r : ℝ}
    (hr : ∀ u, r ≤ s u) : closedBall (0 : Space n) r ⊆ wulff s := by
  intro x hx u
  calc
    _ ≤ ‖(u : Space n)‖*‖x‖ := real_inner_le_norm _ _
    _ = ‖x‖ := by rw [norm_coe,one_mul]
    _ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hx
    _ ≤ s u := hr u

lemma wulff_subset_closedBall {n : ℕ} {s : Sphere n → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hs : ∀ u, s u ≤ R) : wulff s ⊆ closedBall (0 : Space n) R := by
  intro x hx
  rw [mem_closedBall,dist_zero_right]
  by_cases h : x = 0
  · simpa [h] using hR
  · let u : Sphere n := ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]⟩
    have hu : ⟪(u : Space n),x⟫ = ‖x‖ := by
      dsimp only [u]
      rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
      field_simp
    exact hu ▸ (hx u).trans (hs u)

lemma positive_constraint_bounds {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) : ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ u, m ≤ s u ∧ s u ≤ M := by
  have hne : (univ : Set (Sphere n)).Nonempty := by
    obtain ⟨u,hu⟩ := (NormedSpace.sphere_nonempty (x := (0 : Space n))).mpr (by norm_num : (0:ℝ) ≤ 1)
    exact ⟨⟨u,hu⟩,mem_univ _⟩
  obtain ⟨u,_,hu⟩ := isCompact_univ.exists_isMinOn hne s.continuous.continuousOn
  obtain ⟨v,_,hv⟩ := isCompact_univ.exists_isMaxOn hne s.continuous.continuousOn
  exact ⟨s u,s v,hs u,hs v,fun w => ⟨hu (mem_univ w),hv (mem_univ w)⟩⟩

lemma wulff_nhds {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    wulff s ∈ 𝓝 (0 : Space n) := by
  obtain ⟨m,M,hm,_,hb⟩ := positive_constraint_bounds s hs
  exact Metric.mem_nhds_iff.mpr ⟨m,hm,ball_subset_closedBall.trans
    (closedBall_subset_wulff (fun u => (hb u).1))⟩

lemma wulff_compact {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    IsCompact (wulff s) := by
  obtain ⟨m,M,_,hM,hb⟩ := positive_constraint_bounds s hs
  exact (isCompact_closedBall (0 : Space n) M).of_isClosed_subset (wulff_closed _)
    (wulff_subset_closedBall hM.le (fun u => (hb u).2))

lemma gauge_ae_differentiable_sphere {n : ℕ} {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) :
    ∀ᵐ (u : Sphere n) ∂Spherical.sigma n, DifferentiableAt ℝ (gauge K) (u : Space n) := by
  obtain ⟨C,hC⟩ := hc.lipschitz_gauge h0
  apply Spherical.sphere_ae_of_radial hC.ae_differentiableAt
  intro u r hr hd
  have hh : DifferentiableAt ℝ (fun x : Space n => r⁻¹ * gauge K (r • x)) (u : Space n) :=
    (hd.comp (u : Space n) (differentiableAt_id.const_smul r)).const_mul r⁻¹
  have he : (fun x : Space n => r⁻¹ * gauge K (r • x)) = gauge K := by
    funext x
    rw [gauge_smul_of_nonneg (α := ℝ) hr.le,smul_eq_mul,← mul_assoc,
      inv_mul_cancel₀ hr.ne',one_mul]
  rwa [he] at hh

end PettyProjection
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

lemma coefficient_pos (n : ℕ) : 0 < coefficient n := by
  unfold coefficient
  split_ifs <;> positivity

lemma beta_pos (n : ℕ) : 0 < beta n := by
  unfold beta
  split_ifs <;> norm_num

open Finset

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
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma continuous_gradient_of_contDiff {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f) :=
  (InnerProductSpace.toDual ℝ (Space n)).symm.continuous.comp (hf.continuous_fderiv (by norm_num))

lemma sphereGradient_continuous {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (sphereGradient f) := by
  exact (continuous_gradient_of_contDiff hf).sub
    (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_id).smul continuous_id)

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.WulffVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uU

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma support_gradient_of_active {n : ℕ} {C : Set (Space n)}
    (hC : IsCompact C) {x y : Space n} (hy : y ∈ C)
    (hxy : support C x = ⟪x,y⟫)
    (hd : DifferentiableAt ℝ (support C) x) : ∇ (support C) x = y := by
  let l : Space n →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Space n) y
  have he (z : Space n) : l z = ⟪z,y⟫ := by
    change ⟪y,z⟫ = ⟪z,y⟫
    exact real_inner_comm z y
  have hl : IsLocalMin (fun z => support C z-l z) x := by
    apply Eventually.of_forall
    intro z
    dsimp only
    rw [he,he,hxy,sub_self]
    exact sub_nonneg.mpr (inner_le_support hC hy z)
  have hz := hl.hasFDerivAt_eq_zero (hd.hasFDerivAt.sub l.hasFDerivAt)
  have hd' : fderiv ℝ (support C) x = l := sub_eq_zero.mp hz
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left,hd',he]
  exact real_inner_comm _ _

lemma wulff_gradient_of_active {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) {x : Space n} {u : Sphere n}
    (hu : wulffMax s x = ⟪x,(u : Space n)⟫ / s u)
    (hd : DifferentiableAt ℝ (gauge (wulff s)) x) :
    ∇ (gauge (wulff s)) x = (s u)⁻¹ • (u : Space n) := by
  have he : gauge (wulff s) = support (wulffCoefficients s) :=
    funext (gauge_wulff_eq_max s hs)
  rw [he] at hd ⊢
  apply support_gradient_of_active (wulffCoefficients_compact s hs) (mem_range_self u) _ hd
  simpa only [real_inner_smul_right,div_eq_inv_mul,wulffMax] using hu

lemma wulff_active_unique {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) {x : Space n} (hd : DifferentiableAt ℝ (gauge (wulff s)) x)
    {u v : Sphere n} (hu : wulffMax s x = ⟪x,(u : Space n)⟫/s u)
    (hv : wulffMax s x = ⟪x,(v : Space n)⟫/s v) : u = v := by
  have he := (wulff_gradient_of_active s hs hu hd).symm.trans (wulff_gradient_of_active s hs hv hd)
  have hn := congrArg norm he
  simp only [norm_smul,norm_coe,mul_one,Real.norm_eq_abs,abs_inv,abs_of_pos (hs u),
    abs_of_pos (hs v)] at hn
  have hsuv : s u = s v := inv_injective hn
  apply Subtype.ext
  rw [hsuv] at he
  exact (smul_right_injective _ (inv_ne_zero (hs v).ne')) he

end PettyProjection
end

noncomputable section
open Set Filter Topology
namespace PettyProjection

/-- Convergence of maximizers at a unique maximum, with a compact parameter
space and joint continuity only at the limiting parameter. -/
lemma selected_max_tendsto {U : Type uU} [TopologicalSpace U] [CompactSpace U]
    {f : ℝ → U → ℝ} {a : ℝ → U} {u₀ : U}
    (hc : ∀ u : U, ContinuousAt (fun p : ℝ × U => f p.1 p.2) (0,u))
    (hm : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, f t u ≤ f t (a t))
    (hu : ∀ u, (∀ v, f 0 v ≤ f 0 u) → u = u₀) :
    Tendsto a (𝓝 0) (𝓝 u₀) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro u hu'
  obtain ⟨l,hl,hat⟩ := mapClusterPt_iff_ultrafilter.mp hu'
  apply hu
  intro v
  have ht : Tendsto (fun t : ℝ => t) (l : Filter ℝ) (𝓝 0) := hl
  have hv : Tendsto (fun t => f t v) (l : Filter ℝ) (𝓝 (f 0 v)) :=
    (hc v).tendsto.comp (ht.prodMk_nhds tendsto_const_nhds)
  have hav : Tendsto (fun t => f t (a t)) (l : Filter ℝ) (𝓝 (f 0 u)) :=
    (hc u).tendsto.comp (ht.prodMk_nhds hat)
  exact le_of_tendsto_of_tendsto hv hav (hl (hm.mono (fun t h => h v)))

lemma quotient_bounds {a b z t : ℝ} (ht : t ≠ 0) (hl : t*a ≤ z) (hh : z ≤ t*b) :
    min a b ≤ z/t ∧ z/t ≤ max a b := by
  have he : z/t*t = z := div_mul_cancel₀ z ht
  rcases lt_or_gt_of_ne ht with ht | ht
  · have hb : b ≤ z/t := by nlinarith
    have ha : z/t ≤ a := by nlinarith
    exact ⟨(min_le_right a b).trans hb,ha.trans (le_max_left a b)⟩
  · have ha : a ≤ z/t := by nlinarith
    have hb : z/t ≤ b := by nlinarith
    exact ⟨(min_le_left a b).trans ha,hb.trans (le_max_right a b)⟩

/-- Envelope differentiation from an exact continuous difference quotient.
The statement does not require a smooth boundary or a smooth maximizer. -/
lemma hasDerivAt_selected_max {U : Type uU} [TopologicalSpace U] [CompactSpace U]
    {f d : ℝ → U → ℝ} {q : ℝ → ℝ} {a : ℝ → U} {u₀ : U}
    (hc : ∀ u : U, ContinuousAt (fun p : ℝ × U => f p.1 p.2) (0,u))
    (hd : ContinuousAt (fun p : ℝ × U => d p.1 p.2) (0,u₀))
    (hq : ∀ᶠ t in 𝓝 (0 : ℝ), q t = f t (a t) ∧ ∀ u, f t u ≤ q t)
    (hq₀ : q 0 = f 0 u₀) (hm₀ : ∀ u, f 0 u ≤ q 0)
    (hu : ∀ u, (∀ v, f 0 v ≤ f 0 u) → u = u₀)
    (he : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, f t u-f 0 u = t*d t u) :
    HasDerivAt q (d 0 u₀) 0 := by
  have ha : Tendsto a (𝓝 0) (𝓝 u₀) := selected_max_tendsto hc
    (hq.mono (fun t h u => h.1 ▸ h.2 u)) hu
  have hd₀ : Tendsto (fun t => d t u₀) (𝓝 0) (𝓝 (d 0 u₀)) :=
    hd.tendsto.comp (tendsto_id.prodMk_nhds tendsto_const_nhds)
  have hda : Tendsto (fun t => d t (a t)) (𝓝 0) (𝓝 (d 0 u₀)) :=
    hd.tendsto.comp (tendsto_id.prodMk_nhds ha)
  have hlo : Tendsto (fun t => min (d t u₀) (d t (a t))) (𝓝 0) (𝓝 (d 0 u₀)) := by
    simpa only [min_self] using hd₀.min hda
  have hhi : Tendsto (fun t => max (d t u₀) (d t (a t))) (𝓝 0) (𝓝 (d 0 u₀)) := by
    simpa only [max_self] using hd₀.max hda
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add,smul_eq_mul,← div_eq_inv_mul]
  have hb : ∀ᶠ t in 𝓝[≠] (0 : ℝ), min (d t u₀) (d t (a t)) ≤ (q t-q 0)/t ∧
      (q t-q 0)/t ≤ max (d t u₀) (d t (a t)) := by
    filter_upwards [hq.filter_mono nhdsWithin_le_nhds,he.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht he ht0
    have htn : t ≠ 0 := ht0
    have hl : t*d t u₀ ≤ q t-q 0 := by
      rw [← he u₀,hq₀]
      exact sub_le_sub_right (ht.2 u₀) _
    have hh : q t-q 0 ≤ t*d t (a t) := by
      rw [← he (a t),ht.1]
      exact sub_le_sub_left (hm₀ (a t)) _
    exact quotient_bounds htn hl hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (hlo.mono_left nhdsWithin_le_nhds) (hhi.mono_left nhdsWithin_le_nhds)
    (hb.mono (fun _ h => h.1)) (hb.mono (fun _ h => h.2))

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma positive_constraints_eventually {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, m ≤ (s+t • φ) u ∧ (s+t • φ) u ≤ M) := by
  obtain ⟨a,b,ha,hb,hab⟩ := positive_constraint_bounds s hs
  refine ⟨a/2,b+a/2,by positivity,by positivity,?_⟩
  have ht : ∀ᶠ t in 𝓝 (0 : ℝ), |t| *(‖φ‖+1) < a/2 := by
    have h : Tendsto (fun t : ℝ => |t| *(‖φ‖+1)) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0:ℝ)).mul_const (‖φ‖+1)
    exact h.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [ht] with t ht u
  have hφ : |φ u| ≤ ‖φ‖ := φ.norm_coe_le_norm u
  have hbound : |t*φ u| ≤ |t| *(‖φ‖+1) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hφ.trans (by linarith)) (abs_nonneg _)
  have hlo := neg_abs_le (t*φ u)
  have hhi := le_abs_self (t*φ u)
  have hh := hab u
  change a/2 ≤ s u+t*φ u ∧ s u+t*φ u ≤ b+a/2
  constructor <;> linarith

lemma positive_constraints_nhds {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, 0 < (s+t • φ) u := by
  obtain ⟨m,M,hm,_,he⟩ := positive_constraints_eventually s φ hs
  exact he.mono (fun _ h u => hm.trans_le (h u).1)

lemma wulff_derivative_active {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) {x : Space n}
    (hd : DifferentiableAt ℝ (gauge (wulff s)) x) {u₀ : Sphere n}
    (hu₀ : wulffMax s x = ⟪x,(u₀ : Space n)⟫/s u₀) :
    HasDerivAt (fun t : ℝ => gauge (wulff ⇑(s+t • φ)) x)
      (-(gauge (wulff s) x)*φ u₀/s u₀) 0 := by
  classical
  let f : ℝ → Sphere n → ℝ := fun t u => ⟪x,(u : Space n)⟫/(s u+t*φ u)
  let d : ℝ → Sphere n → ℝ := fun t u => -(⟪x,(u : Space n)⟫*φ u)/(s u*(s u+t*φ u))
  let a : ℝ → Sphere n := fun t => if hp : ∀ u, 0 < (s+t • φ) u then
    (wulffMax_attained (s+t • φ) hp x).choose else u₀
  have hpos := positive_constraints_nhds s φ hs
  have hq : ∀ᶠ t in 𝓝 (0 : ℝ), gauge (wulff ⇑(s+t • φ)) x = f t (a t) ∧
      ∀ u, f t u ≤ gauge (wulff ⇑(s+t • φ)) x := by
    filter_upwards [hpos] with t ht
    rw [gauge_wulff_eq_max (s+t • φ) ht]
    constructor
    · dsimp only [a]
      rw [dite_eq_left ht]
      exact (wulffMax_attained (s+t • φ) ht x).choose_spec
    · intro u; exact le_wulffMax (s+t • φ) ht x u
  have hq0 : gauge (wulff (s+(0:ℝ) • φ)) x = f 0 u₀ := by
    simpa only [zero_smul,add_zero,f,zero_mul] using (gauge_wulff_eq_max s hs x).trans hu₀
  have hm0 : ∀ u, f 0 u ≤ gauge (wulff (s+(0:ℝ) • φ)) x := by
    intro u
    simpa only [zero_smul,add_zero,f,zero_mul,gauge_wulff_eq_max s hs x] using le_wulffMax s hs x u
  have hc (u : Sphere n) : ContinuousAt (fun p : ℝ × Sphere n => f p.1 p.2) (0,u) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using (hs u).ne'
  have hdc : ContinuousAt (fun p : ℝ × Sphere n => d p.1 p.2) (0,u₀) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using mul_ne_zero (hs u₀).ne' (hs u₀).ne'
  have hu : ∀ u, (∀ v, f 0 v ≤ f 0 u) → u = u₀ := by
    intro u h
    apply wulff_active_unique s hs hd _ hu₀
    apply le_antisymm
    · simpa only [f,zero_mul,add_zero,← hu₀] using h u₀
    · exact le_wulffMax s hs x u
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, f t u-f 0 u = t*d t u := by
    filter_upwards [hpos] with t ht u
    have hst : s u+t*φ u ≠ 0 := (ht u).ne'
    dsimp only [f,d]
    simp only [zero_mul,add_zero]
    field_simp [hst,(hs u).ne']
    ring
  have h := hasDerivAt_selected_max hc hdc hq hq0 hm0 hu he
  have he0 : d 0 u₀ = -(gauge (wulff s) x)*φ u₀/s u₀ := by
    rw [gauge_wulff_eq_max s hs x,hu₀]
    dsimp [d]
    ring
  rwa [he0] at h

/-- Wulff variation against an actual continuous positively homogeneous test.
No symmetry or boundary smoothness is assumed. -/
theorem wulff_derivative {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ), 0 < a → ∀ x, φ (a • x) = a*φ x)
    {x : Space n} (hd : DifferentiableAt ℝ (gauge (wulff s)) x) :
    HasDerivAt (fun t : ℝ => gauge (wulff (s+t • (⟨fun u : Sphere n => φ u,
      hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))) x)
      (-(gauge (wulff s) x)*φ (∇ (gauge (wulff s)) x)) 0 := by
  obtain ⟨u,hu⟩ := wulffMax_attained s hs x
  have he := wulff_gradient_of_active s hs hu hd
  have h := wulff_derivative_active s ⟨fun u : Sphere n => φ u,hφ.comp continuous_subtype_val⟩ hs hd hu
  rw [he,hh _ (inv_pos.mpr (hs u))]
  convert h using 1
  dsimp
  ring

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe surface sigma mean)

lemma surface_real_univ (n : ℕ) [NeZero n] : (surface n).real univ = n*kappa n := by
  rw [surface,Measure.toSphere_real_apply_univ]
  simp only [finrank_euclideanSpace_fin]
  congr 1
  exact congrArg ENNReal.toReal (Measure.addHaar_closedBall_eq_addHaar_ball volume (0 : Space n) (1:ℝ)).symm

/-- Polar integration of an arbitrary convex neighborhood of zero; the body
need not be symmetric or have a smooth boundary. -/
lemma gauge_volume_lintegral {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hp : ∀ u : Sphere n, 0 < gauge K (u : Space n)) :
    volume K = ∫⁻ u : Sphere n, ENNReal.ofReal ((gauge K (u : Space n))⁻¹ ^ n / n)
      ∂surface n := by
  let ν := Measure.volumeIoiPow (Module.finrank ℝ (Space n)-1)
  let A : Set ({0}ᶜ : Set (Space n)) := Subtype.val ⁻¹' interior K
  let S : Set (Sphere n × Ioi (0:ℝ)) :=
    {z | z.2.1 < (gauge K (z.1 : Space n))⁻¹}
  have hA : MeasurableSet A := isOpen_interior.measurableSet.preimage measurable_subtype_coe
  have hS : MeasurableSet S := by
    apply isOpen_lt (by fun_prop) ?_ |>.measurableSet
    exact ((continuous_gauge hc h0).comp (continuous_subtype_val.comp continuous_fst)).inv₀
      (fun z => (hp z.1).ne')
  have he : (homeomorphUnitSphereProd (Space n)).symm ⁻¹' A = S := by
    ext z
    change (↑((homeomorphUnitSphereProd (Space n)).symm z) : Space n) ∈ interior K ↔ _
    rw [homeomorphUnitSphereProd_symm_apply_coe,← gauge_lt_one_iff_mem_interior hc h0,
      gauge_smul_of_nonneg (α := ℝ) z.2.property.le]
    change (z.2 : ℝ)*gauge K (z.1 : Space n) < 1 ↔ (z.2 : ℝ) < (gauge K (z.1 : Space n))⁻¹
    rw [inv_eq_one_div,lt_div_iff₀ (hp z.1)]
  have hm := ((volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd).symm
    (homeomorphUnitSphereProd (Space n)).toMeasurableEquiv
  have hm' := hm.measure_preimage hA.nullMeasurableSet
  change (surface n).prod ν ((homeomorphUnitSphereProd (Space n)).symm ⁻¹' A) = _ at hm'
  rw [he, ((MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : Space n)).compl)).comap_apply] at hm'
  have hi : Subtype.val '' A = interior K \ {0} := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact ⟨hy,y.property⟩
    · intro hx; exact ⟨⟨x,hx.2⟩,hx.1,rfl⟩
  rw [hi,measure_sdiff_null (measure_singleton _),
    measure_interior_of_null_frontier (hc.addHaar_frontier volume)] at hm'
  rw [← hm',Measure.prod_apply hS]
  apply lintegral_congr
  intro u
  have hu : Prod.mk u ⁻¹' S = Iio (⟨(gauge K (u : Space n))⁻¹,inv_pos.mpr (hp u)⟩ : Ioi (0:ℝ)) := rfl
  rw [hu,Measure.volumeIoiPow_apply_Iio]
  have hn : n-1+1 = n := Nat.sub_add_cancel (NeZero.one_le : 1 ≤ n)
  have hnR := congrArg (fun j : ℕ => (j : ℝ)) hn
  simp only [Nat.cast_add,Nat.cast_one] at hnR
  simp only [finrank_euclideanSpace_fin,hn,hnR]

lemma gauge_volume {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hp : ∀ u : Sphere n, 0 < gauge K (u : Space n)) :
    volume.real K = kappa n * mean (fun u : Sphere n => (gauge K (u : Space n))⁻¹ ^ n) := by
  have hcont : Continuous (fun u : Sphere n => (gauge K (u : Space n))⁻¹ ^ n) :=
    (((continuous_gauge hc h0).comp continuous_subtype_val).inv₀ (fun u => (hp u).ne')).pow n
  have hnn : ∀ u : Sphere n, 0 ≤ (gauge K (u : Space n))⁻¹ ^ n := fun u => pow_nonneg (inv_nonneg.mpr (hp u).le) n
  have hv := congrArg ENNReal.toReal (gauge_volume_lintegral hc h0 hp)
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.div_const n |>.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (Eventually.of_forall (fun u => div_nonneg (hnn u) (Nat.cast_nonneg n))),
    ENNReal.toReal_ofReal (integral_nonneg (fun u => div_nonneg (hnn u) (Nat.cast_nonneg n))),
    integral_div] at hv
  change volume.real K = _ at hv
  rw [hv,mean,sigma,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  change _ = kappa n * (((surface n).real univ)⁻¹ * _)
  rw [surface_real_univ]
  field_simp [(kappa_pos n).ne',(Nat.cast_pos.mpr (NeZero.pos n) : (0:ℝ)<n).ne']

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma wulff_sphere_gauge_bounds {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    {m M : ℝ} (hm : 0 < m) (hs : ∀ u, m ≤ s u ∧ s u ≤ M)
    (u : Sphere n) : M⁻¹ ≤ gauge (wulff s) (u : Space n) ∧
      gauge (wulff s) (u : Space n) ≤ m⁻¹ := by
  have hp : ∀ v, 0 < s v := fun v => hm.trans_le (hs v).1
  rw [gauge_wulff_eq_max s hp]
  constructor
  · have h := le_wulffMax s hp (u : Space n) u
    rw [real_inner_self_eq_norm_sq,norm_coe,one_pow,one_div] at h
    exact (inv_anti₀ (hp u) (hs u).2).trans h
  · obtain ⟨v,hv⟩ := wulffMax_attained s hp (u : Space n)
    rw [hv]
    have hi : ⟪(u : Space n),(v : Space n)⟫ ≤ 1 := by
      simpa only [norm_coe,one_mul] using real_inner_le_norm (u : Space n) (v : Space n)
    calc
      _ ≤ 1 / s v := div_le_div_of_nonneg_right hi (hp v).le
      _ ≤ m⁻¹ := by simpa only [one_div] using inv_anti₀ hm (hs v).1

lemma quotient_perturb_bound {a b c t r m B : ℝ} (hm : 0 < m)
    (ht : m ≤ b+t*c) (hr : m ≤ b+r*c) (ha : |a| ≤ 1) (hc : |c| ≤ B) :
    |a/(b+t*c)-a/(b+r*c)| ≤ (B/m^2)*|t-r| := by
  have ht0 := hm.trans_le ht
  have hr0 := hm.trans_le hr
  have hB : 0 ≤ B := (abs_nonneg c).trans hc
  have he : a/(b+t*c)-a/(b+r*c) = a*c*(r-t)/((b+t*c)*(b+r*c)) := by
    rw [div_sub_div _ _ ht0.ne' hr0.ne']
    congr 1
    ring
  rw [he,abs_div,abs_mul,abs_mul,abs_mul,abs_of_pos ht0,abs_of_pos hr0,abs_sub_comm r t]
  calc
    _ ≤ (1*B)*|t-r|/(m*m) := by gcongr
    _ = _ := by ring

lemma wulff_gauge_param_sub_le {n : ℕ} [NeZero n] (s φ : C(Sphere n,ℝ))
    {m t r : ℝ} (hm : 0 < m) (ht : ∀ u, m ≤ (s+t • φ) u)
    (hr : ∀ u, m ≤ (s+r • φ) u) (u : Sphere n) :
    gauge (wulff ⇑(s+t • φ)) (u : Space n)-gauge (wulff ⇑(s+r • φ)) (u : Space n) ≤
      (‖φ‖/m^2)*|t-r| := by
  have htp : ∀ v, 0 < (s+t • φ) v := fun v => hm.trans_le (ht v)
  have hrp : ∀ v, 0 < (s+r • φ) v := fun v => hm.trans_le (hr v)
  rw [gauge_wulff_eq_max (s+t • φ) htp,gauge_wulff_eq_max (s+r • φ) hrp]
  obtain ⟨v,hv⟩ := wulffMax_attained (s+t • φ) htp (u : Space n)
  rw [hv]
  have hi : |⟪(u : Space n),(v : Space n)⟫| ≤ 1 := by
    simpa only [norm_coe,one_mul] using abs_real_inner_le_norm (u : Space n) (v : Space n)
  calc
    _ ≤ ⟪(u : Space n),(v : Space n)⟫/(s+t • φ) v - ⟪(u : Space n),(v : Space n)⟫/(s+r • φ) v :=
      sub_le_sub_left (le_wulffMax (s+r • φ) hrp _ v) _
    _ ≤ |⟪(u : Space n),(v : Space n)⟫/(s+t • φ) v - ⟪(u : Space n),(v : Space n)⟫/(s+r • φ) v| := le_abs_self _
    _ ≤ _ := quotient_perturb_bound hm (ht v) (hr v) hi (φ.norm_coe_le_norm v)

lemma wulff_gauge_param_lipschitz {n : ℕ} [NeZero n] (s φ : C(Sphere n,ℝ))
    {m : ℝ} (hm : 0 < m) {T : Set ℝ} (hT : ∀ t ∈ T, ∀ u, m ≤ (s+t • φ) u)
    (u : Sphere n) : LipschitzOnWith ⟨‖φ‖/m^2,by positivity⟩
      (fun t : ℝ => gauge (wulff ⇑(s+t • φ)) (u : Space n)) T := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht r hr
  change |gauge (wulff ⇑(s+t • φ)) (u : Space n)-gauge (wulff ⇑(s+r • φ)) (u : Space n)| ≤ (‖φ‖/m^2)*|t-r|
  apply abs_le.mpr
  constructor
  · have h := wulff_gauge_param_sub_le s φ hm (hT r hr) (hT t ht) u
    rw [abs_sub_comm r t] at h
    linarith
  · exact wulff_gauge_param_sub_le s φ hm (hT t ht) (hT r hr) u

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.BrunnMinkowski
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

lemma volumeReal_smul_nonneg {r : ℝ} (hr : 0 ≤ r) (K : Set E) :
    volume.real (r • K)=r^(Module.finrank ℝ E)*volume.real K := by
  rw [Measure.real,Measure.addHaar_smul_of_nonneg volume hr,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr _)]
  rfl

end
end PettyProjection
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
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

lemma normalizedVolume_formula {n : ℕ} (K : Set (Space n)) :
    normalizedVolume K=(volume.real K/kappa n)^((n:ℝ)⁻¹) := by
  rw [Real.div_rpow measureReal_nonneg (kappa_pos n).le]
  rfl

end PettyProjection
end

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

lemma real_sign_eq (t : ℝ) : Real.sign t = t/|t| := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [Real.sign_of_neg ht, abs_of_neg ht]
    field_simp [ht.ne]
  · simp
  · rw [Real.sign_of_pos ht, abs_of_pos ht, div_self ht.ne']

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

lemma higherKernel_const_pos {n : ℕ} [NeZero n] (r : ℕ) (u : Sphere n) :
    0 < higherKernel r u (fun _ => 1) := by
  have hc : Continuous (fun x : Sphere n => max ⟪(u : Space n),(x : Space n)⟫ 0 ^ r) := by
    fun_prop
  simp only [higherKernel, mul_one, mean]
  exact integral_pos_of_integrable_nonneg_nonzero hc (continuous_integrable hc)
    (fun x => pow_nonneg (le_max_right _ _) _) (x := u)
    (by rw [real_inner_self_eq_norm_sq, norm_coe]; norm_num)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma cosineConstant_pos (n : ℕ) [NeZero n] : 0 < cosineConstant n :=
  mul_pos (by norm_num) (higherKernel_const_pos 1 (pole n))

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
open Set MeasureTheory Metric Filter Topology MvPolynomial
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma harmonic_inner_ne {n : ℕ} (hn : 2 ≤ n) [NeZero n] {d e : ℕ} (hde : d ≠ e)
    {v w : H n} (hv : v ∈ harmonicSpace n d) (hw : w ∈ harmonicSpace n e) :
    ⟪v,w⟫ = 0 := by
  exact harmonicSpace_orthogonal hn hde ⟨v,hv⟩ ⟨w,hw⟩

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

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma signField_continuous {n : ℕ} (k : ℝ) {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (signField k f) :=
  (radialField_continuous hf.continuous).add ((tangentField_continuous hf).const_smul k⁻¹)

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

lemma ae_bound_of_limit {n : ℕ} {F : ℕ → Sphere n → Space n}
    {F₀ : Sphere n → Space n} {B : ℝ} (hFB : ∀ j u, ‖F j u‖ ≤ B)
    (hFlim : ∀ᵐ u ∂sigma n, Tendsto (fun j => F j u) atTop (𝓝 (F₀ u))) :
    ∀ᵐ u ∂sigma n, ‖F₀ u‖ ≤ B := by
  filter_upwards [hFlim] with u hu
  exact le_of_tendsto hu.norm (Eventually.of_forall fun j => hFB j u)

lemma signedPair_integrable_of_ae_bound {n : ℕ} [NeZero n] {F G : Sphere n → Space n}
    {B C : ℝ} (hB : 0 ≤ B)
    (hF : AEStronglyMeasurable F (sigma n)) (hG : AEStronglyMeasurable G (sigma n))
    (hFB : ∀ᵐ u ∂sigma n, ‖F u‖ ≤ B) (hGC : ∀ᵐ u ∂sigma n, ‖G u‖ ≤ C) :
    Integrable (fun z : Sphere n × Sphere n => Real.sign ⟪(z.1 : Space n),(z.2 : Space n)⟫ *
      ⟪F z.1,G z.2⟫) ((sigma n).prod (sigma n)) := by
  apply (integrable_const (B*C)).mono'
  · exact ((sign_measurable.comp (by fun_prop : Continuous
      (fun z : Sphere n × Sphere n => ⟪(z.1 : Space n),(z.2 : Space n)⟫)).measurable).aestronglyMeasurable).mul
        ((hF.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).inner
          (hG.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hFB,
      Measure.quasiMeasurePreserving_snd.ae hGC] with z hzF hzG
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (abs_sign_le _) (abs_real_inner_le_norm _ _) (abs_nonneg _) (by norm_num)).trans
      (by simpa only [one_mul] using mul_le_mul hzF hzG (norm_nonneg _) hB)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma reverse_lorentz {a b x y : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hx2 : x^2 ≤ a^2-1) (hy2 : y^2 ≤ b^2-1) :
    1 ≤ a*b-x*y := by
  have hab : 0 ≤ a*b-1 := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  have he : (x*y)^2 ≤ (a*b-1)^2 := by
    have hp := mul_le_mul hx2 hy2 (sq_nonneg y) (by nlinarith : 0 ≤ a^2-1)
    nlinarith [sq_nonneg (a-b)]
  have hxy : 0 ≤ x*y := mul_nonneg hx hy
  nlinarith [sq_nonneg (a*b-1-x*y)]

lemma reverse_lorentz_strict {a b x y : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hx2 : x^2 ≤ a^2-1) (hy2 : y^2 ≤ b^2-1)
    (hxs : 1 < a → x^2 < a^2-1) (hys : 1 < b → y^2 < b^2-1)
    (he : a*b-x*y = 1) : a = 1 ∧ b = 1 := by
  have hprod : x*y = a*b-1 := by linarith
  by_cases hA : a = 1
  · have hx0 : x = 0 := by rw [hA] at hx2; nlinarith [sq_nonneg x]
    rw [hA,hx0] at he
    constructor; exact hA; nlinarith
  have ha' : 1 < a := lt_of_le_of_ne ha (Ne.symm hA)
  by_cases hB : b = 1
  · have hy0 : y = 0 := by rw [hB] at hy2; nlinarith [sq_nonneg y]
    rw [hB,hy0] at he
    exact False.elim (hA (by nlinarith))
  have hb' : 1 < b := lt_of_le_of_ne hb (Ne.symm hB)
  have hpa : 0 < a^2-1 := by nlinarith
  have hpb : 0 < b^2-1 := by nlinarith
  have hp : x^2*y^2 < (a^2-1)*(b^2-1) :=
    (mul_le_mul_of_nonneg_left hy2 (sq_nonneg x)).trans_lt
      (mul_lt_mul_of_pos_right (hxs ha') hpb)
  have hbstrict := hys hb'
  nlinarith [sq_nonneg (a-b), sq_nonneg (x*y-(a*b-1))]

lemma coefficient_sign_factor {n : ℕ} (hn : 4 ≤ n) :
    ((1+(2/(Scalar.exponent n : ℝ)+((n : ℝ)-1)/(Scalar.exponent n : ℝ)^2)*
      (4*(n+2)))/((n+1)*(n+3))) = Scalar.coefficient n := by
  unfold Scalar.exponent Scalar.coefficient
  split_ifs with h
  · subst n; norm_num
  · have h1 : (n : ℝ)+1 ≠ 0 := by positivity
    have h3 : (n : ℝ)+3 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical
open Scalar

lemma gaugeMoment_ranges {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (g : Seminorm ℝ (Space n)) (hg : ∀ u : Sphere n, 0 < g u)
    (hnorm : mean (fun u : Sphere n => (g u)⁻¹^n) = 1) :
    1 ≤ gaugeMoment g (exponent n-1) ∧ gaugeMoment g (exponent n-1) ≤ gaugeMoment g (exponent n) := by
  obtain ⟨hm,ht,htm,_,_⟩ := norm_mean_ranges hn (restrictContinuous g (seminorm_continuous n g)) hg hnorm
  have hk : 0 < (exponent n : ℝ) := by unfold exponent; split_ifs <;> norm_num
  have hc : ((exponent n : ℝ)-1)/(exponent n : ℝ) ≤ 1 := (div_le_one hk).mpr (by linarith)
  change 0 ≤ gaugeMoment g (exponent n)-1 at hm
  change 0 ≤ gaugeMoment g (exponent n-1)-1 at ht
  change gaugeMoment g (exponent n-1)-1 ≤ _*(gaugeMoment g (exponent n)-1) at htm
  constructor; linarith
  have hp := mul_le_mul_of_nonneg_right hc hm
  linarith

lemma gaugeTail_of_one {n : ℕ} [NeZero n] (g : Seminorm ℝ (Space n)) (k : ℕ)
    (hg : ∀ u : Sphere n, g u = 1) : gaugeTail g k = 0 := by
  have he : restrictContinuous (fun x => g x^k) ((seminorm_continuous n g).pow k) =
      ContinuousMap.const (Sphere n) 1 := by ext u; simp [restrictContinuous,hg u]
  unfold gaugeTail
  rw [he,Q_constant,norm_zero]

lemma scaled_norm_energy {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (g : Seminorm ℝ (Space n)) (hg : ∀ u : Sphere n, 0 < g u)
    (hnorm : mean (fun u : Sphere n => (g u)⁻¹^n) = 1)
    {s : ℝ} (hs : 0 < s) (hst : 1 ≤ s*gaugeMoment g (exponent n-1)) :
    let a := s*gaugeMoment g (exponent n)
    let e := s*Real.sqrt (coefficient n)*gaugeTail g (exponent n)
    1 ≤ a ∧ 0 ≤ e ∧ e^2 ≤ a^2-1 ∧ (1 < a → e^2 < a^2-1) := by
  dsimp only
  obtain ⟨ht,htm⟩ := gaugeMoment_ranges hn g hg hnorm
  have ha : 1 ≤ s*gaugeMoment g (exponent n) := hst.trans (mul_le_mul_of_nonneg_left htm hs.le)
  have he : 0 ≤ s*Real.sqrt (coefficient n)*gaugeTail g (exponent n) := by
    apply mul_nonneg (mul_nonneg hs.le (Real.sqrt_nonneg _)); exact norm_nonneg _
  have hc := coefficient_pos n
  have hid : (s*Real.sqrt (coefficient n)*gaugeTail g (exponent n))^2 =
      s^2*(coefficient n*gaugeTail g (exponent n)^2) := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hc.le]; ring
  obtain ⟨hnrm,hnrme⟩ := norm_estimate hn g hg hnorm
  change coefficient n*gaugeTail g (exponent n)^2 ≤
      gaugeMoment g (exponent n)^2-gaugeMoment g (exponent n-1)^2 at hnrm
  have hsq : 1 ≤ (s*gaugeMoment g (exponent n-1))^2 := by nlinarith
  have herr : (s*Real.sqrt (coefficient n)*gaugeTail g (exponent n))^2 ≤
      (s*gaugeMoment g (exponent n))^2-1 := by
    rw [hid]
    calc
      _ ≤ s^2*(gaugeMoment g (exponent n)^2-gaugeMoment g (exponent n-1)^2) :=
        mul_le_mul_of_nonneg_left hnrm (sq_nonneg s)
      _ = (s*gaugeMoment g (exponent n))^2-(s*gaugeMoment g (exponent n-1))^2 := by ring
      _ ≤ _ := sub_le_sub_left hsq _
  refine ⟨ha,he,herr,?_⟩
  intro ha'
  by_cases hconst : ∀ u : Sphere n, g u = 1
  · rw [gaugeTail_of_one g _ hconst]
    nlinarith
  have hstrict : coefficient n*gaugeTail g (exponent n)^2 <
      gaugeMoment g (exponent n)^2-gaugeMoment g (exponent n-1)^2 := by
    apply lt_of_le_of_ne hnrm
    intro heq
    exact hconst (hnrme.mp heq)
  rw [hid]
  calc
    _ < s^2*(gaugeMoment g (exponent n)^2-gaugeMoment g (exponent n-1)^2) :=
      mul_lt_mul_of_pos_left hstrict (sq_pos_of_pos hs)
    _ = (s*gaugeMoment g (exponent n))^2-(s*gaugeMoment g (exponent n-1))^2 := by ring
    _ ≤ _ := sub_le_sub_left hsq _

lemma normalized_one_eq {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (g : Seminorm ℝ (Space n)) (hg : ∀ u : Sphere n, 0 < g u)
    (hnorm : mean (fun u : Sphere n => (g u)⁻¹^n) = 1)
    {s : ℝ} (hs : 0 < s) (hst : 1 ≤ s*gaugeMoment g (exponent n-1))
    (ha : s*gaugeMoment g (exponent n) = 1) :
    (∀ u : Sphere n, g u = 1) ∧ s = 1 := by
  have hne := norm_estimate hn g hg hnorm
  have ht := (gaugeMoment_ranges hn g hg hnorm).1
  have hmt : gaugeMoment g (exponent n) ≤ gaugeMoment g (exponent n-1) := by
    apply (mul_le_mul_iff_right₀ hs).mp
    simpa only [mul_comm s] using (ha.le.trans hst)
  have hm : 0 ≤ gaugeMoment g (exponent n) := by nlinarith [ha]
  have heq : coefficient n*gaugeTail g (exponent n)^2 =
      gaugeMoment g (exponent n)^2-gaugeMoment g (exponent n-1)^2 := by
    have hineq : coefficient n*gaugeTail g (exponent n)^2 ≤
        gaugeMoment g (exponent n)^2-gaugeMoment g (exponent n-1)^2 := hne.1
    apply le_antisymm hineq
    have hc := mul_nonneg (coefficient_pos n).le (sq_nonneg (gaugeTail g (exponent n)))
    nlinarith
  have hconst := hne.2.mp heq
  refine ⟨hconst,?_⟩
  have hmone : gaugeMoment g (exponent n) = 1 := by
    unfold gaugeMoment
    have he : (fun u : Sphere n => g u^exponent n) = (fun _ => (1 : ℝ)) := by funext u; simp [hconst u]
    rw [he,mean_const]
  simpa only [hmone,mul_one] using ha

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma seminorm_euler {n : ℕ} (g : Seminorm ℝ (Space n)) {x : Space n}
    (hd : DifferentiableAt ℝ (g : Space n → ℝ) x) :
    fderiv ℝ g x x = g x := by
  have he : (fun t : ℝ => g (t • x)) =ᶠ[𝓝 (1 : ℝ)] (fun t => t * g x) := by
    filter_upwards [eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)] with t ht
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ht]
  have hx : HasFDerivAt (g : Space n → ℝ) (fderiv ℝ g x) ((1 : ℝ) • x) := by simpa using hd.hasFDerivAt
  have hc := hx.comp_hasDerivAt (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).smul_const x)
  simp only [one_smul] at hc
  have hl := (hasDerivAt_id (1 : ℝ)).mul_const (g x)
  simp only [one_mul] at hl
  exact (hc.congr_of_eventuallyEq he.symm).unique hl

lemma signField_power_eq {n : ℕ} (g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k)
    {u : Sphere n} (hd : DifferentiableAt ℝ (g : Space n → ℝ) (u : Space n)) :
    signField (k : ℝ) (fun x => g x^k) u = gaugeField g k u := by
  rw [signField_eq_gradient, gradient_pow hd k]
  rw [real_inner_smul_left, inner_gradient_left, seminorm_euler g hd]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hp : g u^(k-1)*g u = g u^k := by
    rw [← pow_succ]; congr 1; omega
  rw [smul_sub, smul_smul, smul_smul]
  have h1 : (k : ℝ)⁻¹*((k : ℝ)*g u^(k-1)) = g u^(k-1) := by field_simp
  have h2 : (k : ℝ)⁻¹*((k : ℝ)*g u^(k-1)*g u) = g u^k := by
    calc
      _ = ((k : ℝ)⁻¹*((k : ℝ)*g u^(k-1)))*g u := by ring
      _ = _ := by rw [h1,hp]
  rw [h1,h2]
  dsimp only [gaugeField]
  abel

lemma signField_power_ae_eq {n : ℕ} (g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k) :
    signField (k : ℝ) (fun x => g x^k) =ᵐ[sigma n] gaugeField g k := by
  filter_upwards [seminorm_ae_differentiable_sphere g] with u hu
  exact signField_power_eq g hk hu

lemma gaugeField_measurable_bound {n : ℕ} (g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k) :
    AEStronglyMeasurable (gaugeField g k) (sigma n) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ u ∂sigma n, ‖gaugeField g k u‖ ≤ B := by
  have hlim := normSmooth_powerField_tendsto g k
  have he := signField_power_ae_eq g hk
  have hm := aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (fun j => (signField_continuous (k : ℝ)
      ((normSmooth_contDiff g _).pow k |>.of_le (by norm_num))).aestronglyMeasurable) hlim
  obtain ⟨B,hB,hbound⟩ := normSmooth_powerField_bound g k
  refine ⟨hm.congr he, B,hB, ?_⟩
  filter_upwards [he, ae_bound_of_limit hbound hlim] with u hu hb
  rw [← hu]; exact hb

lemma signedPair_congr_ae {n : ℕ} {F G F' G' : Sphere n → Space n}
    (hF : F =ᵐ[sigma n] F') (hG : G =ᵐ[sigma n] G') :
    signedPair F G = signedPair F' G' := by
  have : IsFiniteMeasure (sigma n) := by unfold sigma; infer_instance
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hF,
    Measure.quasiMeasurePreserving_snd.ae hG] with z hzF hzG
  rw [hzF,hzG]

lemma signedPair_gaugeField {n : ℕ} (f g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k) :
    signedPair (signField (k : ℝ) (fun x => f x^k)) (signField (k : ℝ) (fun x => g x^k)) =
      signedPair (gaugeField f k) (gaugeField g k) :=
  signedPair_congr_ae (signField_power_ae_eq f hk) (signField_power_ae_eq g hk)

lemma gaugeField_absolute_integrable {n : ℕ} [NeZero n]
    (f g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k) :
    Integrable (fun z : Sphere n × Sphere n =>
      |⟪gaugeField f k z.1,gaugeField g k z.2⟫|) ((sigma n).prod (sigma n)) := by
  obtain ⟨hf,B,hB,hFB⟩ := gaugeField_measurable_bound f hk
  obtain ⟨hg,C,_,hGC⟩ := gaugeField_measurable_bound g hk
  apply (integrable_const (B*C)).mono'
  · have hm : AEStronglyMeasurable (fun z : Sphere n × Sphere n =>
        ⟪gaugeField f k z.1,gaugeField g k z.2⟫) ((sigma n).prod (sigma n)) :=
      (hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).inner
        (hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    simpa only [Real.norm_eq_abs] using hm.norm
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hFB,
      Measure.quasiMeasurePreserving_snd.ae hGC] with z hzF hzG
    simpa only [Real.norm_eq_abs, abs_abs] using
      (abs_real_inner_le_norm _ _).trans (mul_le_mul hzF hzG (norm_nonneg _) hB)

lemma signedPair_gaugeField_le_absolute {n : ℕ} [NeZero n]
    (f g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k) :
    signedPair (gaugeField f k) (gaugeField g k) ≤
      absolutePair (gaugeField f k) (gaugeField g k) := by
  obtain ⟨hf,B,hB,hFB⟩ := gaugeField_measurable_bound f hk
  obtain ⟨hg,C,_,hGC⟩ := gaugeField_measurable_bound g hk
  apply integral_mono (signedPair_integrable_of_ae_bound hB hf hg hFB hGC)
    (gaugeField_absolute_integrable f g hk)
  intro z
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (abs_sign_le _))

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical
open Scalar

lemma norm_absolutePair_lower {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (f g : Seminorm ℝ (Space n))
    (h2 : (harmonicSpace n 2).starProjection (toH n
      (restrictContinuous (fun x => f x^exponent n) ((seminorm_continuous n f).pow _))) = 0) :
    gaugeMoment f (exponent n)*gaugeMoment g (exponent n) -
      coefficient n*gaugeTail f (exponent n)*gaugeTail g (exponent n) ≤
      absolutePair (gaugeField f (exponent n)) (gaugeField g (exponent n))/cosineConstant n := by
  have hk : 0 < exponent n := by unfold exponent; split_ifs <;> norm_num
  have h := norm_sign_form (by omega) f g hk h2
  rw [coefficient_sign_factor hn, signedPair_gaugeField f g hk] at h
  exact h.trans (div_le_div_of_nonneg_right (signedPair_gaugeField_le_absolute f g hk)
    (cosineConstant_pos n).le)

/-- Spherical form of the full bilinear estimate, before construction of the
variational representing bodies. Both norms can be nonsmooth. -/
theorem normalized_norm_pair {n : ℕ} (hn : 4 ≤ n) [NeZero n]
    (f g : Seminorm ℝ (Space n)) (hf : ∀ u : Sphere n, 0 < f u) (hg : ∀ u : Sphere n, 0 < g u)
    (hfn : mean (fun u : Sphere n => (f u)⁻¹^n) = 1)
    (hgn : mean (fun u : Sphere n => (g u)⁻¹^n) = 1)
    (h2 : (harmonicSpace n 2).starProjection (toH n
      (restrictContinuous (fun x => f x^exponent n) ((seminorm_continuous n f).pow _))) = 0)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hsf : 1 ≤ s*gaugeMoment f (exponent n-1)) (htg : 1 ≤ t*gaugeMoment g (exponent n-1)) :
    cosineConstant n ≤ s*t*absolutePair (gaugeField f (exponent n)) (gaugeField g (exponent n)) ∧
    (s*t*absolutePair (gaugeField f (exponent n)) (gaugeField g (exponent n)) = cosineConstant n →
      (∀ u : Sphere n, f u = 1) ∧ (∀ u : Sphere n, g u = 1) ∧ s = 1 ∧ t = 1) := by
  let a := s*gaugeMoment f (exponent n)
  let b := t*gaugeMoment g (exponent n)
  let x := s*Real.sqrt (coefficient n)*gaugeTail f (exponent n)
  let y := t*Real.sqrt (coefficient n)*gaugeTail g (exponent n)
  obtain ⟨ha,hx,hx2,hxs⟩ := scaled_norm_energy hn f hf hfn hs hsf
  obtain ⟨hb,hy,hy2,hys⟩ := scaled_norm_energy hn g hg hgn ht htg
  have hlor := reverse_lorentz ha hb hx hy hx2 hy2
  have hid : a*b-x*y = s*t*(gaugeMoment f (exponent n)*gaugeMoment g (exponent n)-
      coefficient n*gaugeTail f (exponent n)*gaugeTail g (exponent n)) := by
    calc
      _ = s*t*(gaugeMoment f (exponent n)*gaugeMoment g (exponent n)-
          (Real.sqrt (coefficient n))^2*gaugeTail f (exponent n)*gaugeTail g (exponent n)) := by
        dsimp only [a,b,x,y]; ring
      _ = _ := by rw [Real.sq_sqrt (coefficient_pos n).le]
  have hlow : a*b-x*y ≤ s*t*
      (absolutePair (gaugeField f (exponent n)) (gaugeField g (exponent n))/cosineConstant n) := by
    rw [hid]
    exact mul_le_mul_of_nonneg_left (norm_absolutePair_lower hn f g h2) (mul_nonneg hs.le ht.le)
  have hbound : cosineConstant n ≤ s*t*absolutePair
      (gaugeField f (exponent n)) (gaugeField g (exponent n)) := by
    have h := hlor.trans hlow
    rw [← mul_div_assoc] at h
    simpa only [one_mul] using (le_div_iff₀ (cosineConstant_pos n)).mp h
  refine ⟨hbound,?_⟩
  intro heq
  have hupper : a*b-x*y ≤ 1 := by
    rw [← mul_div_assoc,heq,div_self (cosineConstant_pos n).ne'] at hlow
    exact hlow
  obtain ⟨ha1,hb1⟩ := reverse_lorentz_strict ha hb hx hy hx2 hy2 hxs hys (le_antisymm hupper hlor)
  obtain ⟨hf1,hs1⟩ := normalized_one_eq hn f hf hfn hs hsf ha1
  obtain ⟨hg1,ht1⟩ := normalized_one_eq hn g hg hgn ht htg hb1
  exact ⟨hf1,hg1,hs1,ht1⟩

end PettyProjection.Spherical
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.SeminormBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uι

noncomputable section
open Set Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere seminorm_continuous)

lemma gauge_seminormUnit {n : ℕ} (g : Seminorm ℝ (Space n)) (x : Space n) :
    gauge (seminormUnit g) x=g x := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hp : 0<g x+ε := add_pos_of_nonneg_of_pos (apply_nonneg g x) hε
    apply gauge_le_of_mem hp.le
    refine ⟨(g x+ε)⁻¹ • x,?_,smul_inv_smul₀ hp.ne' x⟩
    change g ((g x+ε)⁻¹ • x)≤1
    rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le),inv_mul_le_iff₀ hp]
    linarith
  · unfold gauge
    apply le_csInf (absorbent_nhds_zero (seminormUnit_nhds g)).gauge_set_nonempty
    rintro r ⟨hr,y,hy,rfl⟩
    rw [map_smul_eq_mul,Real.norm_of_nonneg hr.le]
    exact mul_le_of_le_one_right hr.le hy

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.RelativeGauges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma objective_scale {n : ℕ} [NeZero n] (b : Bool) {g f : Seminorm ℝ (Space n)}
    (hg : g≠0) {a : ℝ} (ha : 0<a) (he : ∀ x,f x=a*g x) :
    objective b f=if b then Real.log a+objective b g else a*objective b g := by
  cases b
  · change (∫ u : Sphere n,f u ∂sigma n)=a*∫ u : Sphere n,g u ∂sigma n
    simp_rw [he]; exact integral_const_mul _ _
  · have hae : (fun u : Sphere n => Real.log (f u))=ᵐ[sigma n]
        (fun u : Sphere n => Real.log a+Real.log (g u)) := by
      filter_upwards [seminorm_pos_ae_sphere hg] with u hu
      rw [he,Real.log_mul ha.ne' hu.ne']
    change (∫ u : Sphere n,Real.log (f u) ∂sigma n)=Real.log a+∫ u : Sphere n,Real.log (g u) ∂sigma n
    rw [integral_congr_ae hae,integral_add (integrable_const _) (seminorm_log_integrable hg),integral_const]
    simp only [probReal_univ,one_smul]

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere seminorm_continuous)

namespace RelativeGauge
variable {n : ℕ} {V : Submodule ℝ (Space n)}

lemma body_ofBody {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K) (hb : Balanced ℝ K)
    (hsub : K⊆V) (hinner : ∃ r : ℝ,0<r ∧ ∀ x∈V,‖x‖≤r → x∈K) :
    (ofBody hK hc hb hinner).body=K := by
  ext x
  change (x∈V ∧ gauge (V.starProjection ⁻¹' K) x≤1) ↔ x∈K
  rw [gauge_le_one_iff_mem_closure (s := V.starProjection ⁻¹' K) (hc.linear_preimage V.starProjection.toLinearMap)
    (cylinder_nhds hinner),(hK.isClosed.preimage V.starProjection.continuous).closure_eq]
  constructor
  · rintro ⟨hx,hy⟩
    change V.starProjection x∈K at hy
    rwa [V.starProjection_eq_self_iff.mpr hx] at hy
  · intro hx
    refine ⟨hsub hx,?_⟩
    change V.starProjection x∈K
    rwa [V.starProjection_eq_self_iff.mpr (hsub hx)]

end RelativeGauge
end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.VariationalMinimizers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean objectiveIntegrand)

lemma objective_param_lipschitz {n : ℕ} [NeZero n] (b : Bool)
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u,0 < s u) :
    ∃ T ∈ 𝓝 (0 : ℝ), ∃ C : ℝ≥0, ∀ u : Sphere n,
      LipschitzOnWith C (fun t : ℝ => objectiveIntegrand b (gauge (wulff ⇑(s+t • φ)) (u : Space n))) T := by
  obtain ⟨m,M,hm,hM,he⟩ := positive_constraints_eventually s φ hs
  let T : Set ℝ := {t | ∀ u, m ≤ (s+t • φ) u ∧ (s+t • φ) u ≤ M}
  have hT : T ∈ 𝓝 (0 : ℝ) := he
  have hc : ContDiffOn ℝ 1 (objectiveIntegrand b) (Icc M⁻¹ m⁻¹) := by
    cases b
    · exact contDiff_id.contDiffOn
    · intro a ha
      exact (Real.contDiffAt_log.mpr ((inv_pos.mpr hM).trans_le ha.1).ne').contDiffWithinAt
  obtain ⟨D,hD⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  let C : ℝ≥0 := ⟨‖φ‖/m^2,by positivity⟩
  refine ⟨T,hT,D*C,fun u => ?_⟩
  apply hD.comp (wulff_gauge_param_lipschitz s φ hm (fun t ht v => (ht v).1) u)
  exact fun t ht => wulff_sphere_gauge_bounds (s+t • φ) hm ht u

lemma objectiveIntegrand_continuousOn (b : Bool) : ContinuousOn (objectiveIntegrand b) (Ioi 0) := by
  cases b
  · exact continuous_id.continuousOn
  · exact Real.continuousOn_log.mono (fun _ h => ne_of_gt h)

lemma objective_gauge_derivative {n : ℕ} [NeZero n] (b : Bool) (s : C(Sphere n,ℝ))
    (hs : ∀ u,0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ),0 < a → ∀ x,φ (a • x)=a*φ x)
    {u : Sphere n} (hd : DifferentiableAt ℝ (gauge (wulff s)) (u : Space n)) :
    HasDerivAt (fun t : ℝ => objectiveIntegrand b (gauge (wulff ⇑(s+t • (⟨fun v : Sphere n => φ v,
      hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))) (u : Space n)))
      (- (if b then 1 else gauge (wulff s) (u:Space n))*φ (∇ (gauge (wulff s)) (u : Space n))) 0 := by
  have hp := gauge_pos_sphere (wulff_compact s hs) (wulff_convex _) (wulff_nhds s hs) u
  have hder := wulff_derivative s hs φ hφ hh hd
  cases b
  · exact hder
  · have hdlog := hder.log (by simpa only [zero_smul,add_zero] using hp.ne')
    apply hdlog.congr_deriv
    simp only [zero_smul,add_zero]
    change -gauge (wulff s) (u:Space n)*φ _/gauge (wulff s) (u:Space n)= -1*φ _
    field_simp

/-- Two-sided first variation of both variational objectives, with no smoothness
assumption on the optimizer. -/
theorem wulff_objective_derivative {n : ℕ} [NeZero n] (b : Bool) (s : C(Sphere n,ℝ))
    (hs : ∀ u,0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ),0 < a → ∀ x,φ (a • x)=a*φ x) :
    HasDerivAt (fun t : ℝ => mean (fun u : Sphere n => objectiveIntegrand b
      (gauge (wulff ⇑(s+t • (⟨fun v : Sphere n => φ v,
        hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))) (u:Space n))))
      (-mean (fun u : Sphere n => (if b then 1 else gauge (wulff s) (u:Space n))*
        φ (∇ (gauge (wulff s)) (u:Space n)))) 0 := by
  let φs : C(Sphere n,ℝ) := ⟨fun u => φ u,hφ.comp continuous_subtype_val⟩
  let F : ℝ → Sphere n → ℝ := fun t u => objectiveIntegrand b (gauge (wulff ⇑(s+t • φs)) (u:Space n))
  let F' : Sphere n → ℝ := fun u => -(if b then 1 else gauge (wulff s) (u:Space n))*φ (∇ (gauge (wulff s)) (u:Space n))
  have hg := continuous_gauge (wulff_convex s) (wulff_nhds s hs)
  have hp := gauge_pos_sphere (wulff_compact s hs) (wulff_convex _) (wulff_nhds s hs)
  have hc : Continuous (F 0) := by
    simp only [F,zero_smul,add_zero]
    exact (objectiveIntegrand_continuousOn b).comp_continuous (hg.comp continuous_subtype_val) hp
  obtain ⟨T,hT,C,hC⟩ := objective_param_lipschitz b s φs hs
  have hFm : ∀ᶠ t in 𝓝 (0:ℝ), AEStronglyMeasurable (F t) (sigma n) := by
    filter_upwards [positive_constraints_nhds s φs hs] with t ht
    have hgt := continuous_gauge (wulff_convex (s+t • φs)) (wulff_nhds (s+t • φs) ht)
    have hpt := gauge_pos_sphere (wulff_compact (s+t • φs) ht) (wulff_convex _) (wulff_nhds (s+t • φs) ht)
    exact ((objectiveIntegrand_continuousOn b).comp_continuous (hgt.comp continuous_subtype_val) hpt).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable F' (sigma n) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · exact (hg.measurable.comp measurable_subtype_coe).neg
      · exact measurable_const
    · exact hφ.measurable.comp ((measurable_gradient _).comp measurable_subtype_coe)
  have hder : ∀ᵐ u ∂sigma n, HasDerivAt (fun t => F t u) (F' u) 0 := by
    filter_upwards [gauge_ae_differentiable_sphere (wulff_convex s) (wulff_nhds s hs)] with u hu
    exact objective_gauge_derivative b s hs φ hφ hh hu
  have hI := (hasDerivAt_integral_of_dominated_loc_of_lip hT hFm
    (Spherical.continuous_integrable hc) hF'm
    (Eventually.of_forall (fun u => by simpa only [Real.nnabs_coe] using hC u))
    (integrable_const (C:ℝ)) hder).2
  apply hI.congr_deriv
  dsimp only [F',mean]
  simp only [neg_mul,integral_neg]

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere)

lemma support_even {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (hne : K.Nonempty) (hsym : ∀ x∈K,-x∈K) (u : Space n) : support K (-u)=support K u := by
  apply le_antisymm
  · apply (support_le_iff hK hne).mpr
    intro x hx
    have hh := inner_le_support hK (hsym x hx) u
    simpa only [inner_neg_left,inner_neg_right] using hh
  · apply (support_le_iff hK hne).mpr
    intro x hx
    have hh := inner_le_support hK (hsym x hx) (-u)
    simpa only [inner_neg_left,inner_neg_right,neg_neg] using hh

lemma wulff_balanced {n : ℕ} (s : Sphere n → ℝ)
    (hs : ∀ u : Sphere n,s ⟨-(u:Space n),by simp⟩=s u) : Balanced ℝ (wulff s) := by
  apply (balanced_iff_neg_mem (wulff_convex s)).mpr
  intro x hx u
  have hh := hx ⟨-(u:Space n),by simp⟩
  change ⟪(u:Space n),-x⟫≤ s u
  simpa only [inner_neg_left,inner_neg_right,hs] using hh

namespace RelativeGauge
variable {n : ℕ}

lemma top_gauge (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) (x : Space n) : gauge g.body x=g x := by
  rw [g.top_body]; exact gauge_seminormUnit _ _
lemma body_ofFullBody {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hb : Balanced ℝ K) (h0 : K∈𝓝 (0:Space n)) : (ofFullBody hK hc hb h0).body=K :=
  body_ofBody _ _ _ (fun _ _ => Submodule.mem_top) _

end RelativeGauge

lemma homogeneous_integrable {n : ℕ} [NeZero n] {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) {φ : Space n → ℝ} (hφ : Continuous φ)
    (hh : ∀ a : ℝ,0<a → ∀ x,φ (a • x)=a*φ x) : Integrable φ μ := by
  let φs : C(Sphere n,ℝ) := ⟨fun u => φ u,hφ.comp continuous_subtype_val⟩
  have hzero : φ 0=0 := by
    have hz := hh 2 (by norm_num) 0
    simp only [smul_zero] at hz
    linarith
  apply (hμ.const_mul ‖φs‖).mono' hφ.aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  by_cases hx : x=0
  · simp [hx,hzero]
  have hp := norm_pos_iff.mpr hx
  let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hx]⟩
  have he : x=‖x‖ • (u:Space n) := by simp [u,smul_smul,hx]
  rw [he,hh _ hp,norm_mul,Real.norm_of_nonneg hp.le]
  have hbound := φs.norm_coe_le_norm u
  change |φ (u:Space n)|≤‖φs‖ at hbound
  have heq : ‖‖x‖ • (u:Space n)‖=‖x‖ := by simp [norm_smul]
  rw [heq]
  simpa only [Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_left hbound hp.le

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere)

lemma homogeneous_zero {n : ℕ} {φ : Space n → ℝ}
    (hh : ∀ a : ℝ,0<a → ∀ x,φ (a • x)=a*φ x) : φ 0=0 := by
  have hh := hh 2 (by norm_num) 0
  simp only [smul_zero] at hh
  linarith

lemma support_wulff_bound {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hne : K.Nonempty) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ a : ℝ,0<a → ∀ x,φ (a • x)=a*φ x) (t : ℝ)
    (hp : ∀ u : Sphere n,0 < support K u+t*φ u) (x : Space n) :
    support (wulff (fun u : Sphere n => support K u+t*φ u)) x≤ support K x+t*φ x := by
  let s : C(Sphere n,ℝ) := ⟨fun u => support K u+t*φ u,((support_continuous hK).comp continuous_subtype_val).add (continuous_const.mul (hφ.comp continuous_subtype_val))⟩
  have hW := wulff_compact s hp
  have hWn : (wulff s).Nonempty := ⟨0,mem_of_mem_nhds (wulff_nhds s hp)⟩
  apply (support_le_iff hW hWn).mpr
  intro y hy
  by_cases hx : x=0
  · subst x
    rw [homogeneous_zero hh,inner_zero_left]
    have hz : support K 0=0 := by
      obtain ⟨z,hz,he⟩ := support_attained hK hne 0
      simpa only [inner_zero_left] using he
    simp only [hz,mul_zero,add_zero,le_refl]
  have hxpos := norm_pos_iff.mpr hx
  let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hx]⟩
  have hu := hy u
  have he : x=‖x‖ • (u:Space n) := by simp [u,smul_smul,hx]
  calc
    ⟪x,y⟫ = ‖x‖*⟪(u:Space n),y⟫ := by
      conv_lhs => rw [he,inner_smul_left]
      rfl
    _ ≤ ‖x‖*(support K u+t*φ u) := mul_le_mul_of_nonneg_left hu hxpos.le
    _ = support K x+t*φ x := by
      conv_rhs => rw [he,support_smul hK hne hxpos.le,hh _ hxpos]
      ring

lemma functional_wulff_bound {n : ℕ} [NeZero n] {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) {K : Set (Space n)}
    (hK : IsCompact K) (hne : K.Nonempty) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ a : ℝ,0<a → ∀ x,φ (a • x)=a*φ x) (t : ℝ)
    (hp : ∀ u : Sphere n,0 < support K u+t*φ u) :
    supportFunctional μ (wulff (fun u : Sphere n => support K u+t*φ u))≤
      supportFunctional μ K+t*(∫ x,φ x ∂μ) := by
  let s : C(Sphere n,ℝ) := ⟨fun u => support K u+t*φ u,((support_continuous hK).comp continuous_subtype_val).add (continuous_const.mul (hφ.comp continuous_subtype_val))⟩
  have hi := support_integrable hμ (wulff_compact s hp) ⟨0,mem_of_mem_nhds (wulff_nhds s hp)⟩
  have hφi := homogeneous_integrable hμ hφ hh
  have hh := integral_mono hi ((support_integrable hμ hK hne).add (hφi.const_mul t))
    (support_wulff_bound hK hne φ hφ hh t hp)
  simp only [Pi.add_apply] at hh
  rwa [integral_add (support_integrable hμ hK hne) (hφi.const_mul t),integral_const_mul] at hh

namespace RelativeGauge
variable {n : ℕ} [NeZero n] {V : Submodule ℝ (Space n)}
lemma minimizer_scaled_lower {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (hV : V≠⊥)
    (hq : ∀ x∈V,x≠0 → 0<cosineSeminorm μ hμ x) (b : Bool)
    {g : RelativeGauge V}
    (hmin : ∀ q : RelativeGauge V,supportFunctional μ q.body=1 →
      Spherical.objective b g.toSeminorm≤Spherical.objective b q.toSeminorm)
    (f : RelativeGauge V) {a : ℝ} (ha : 0<a) (hle : supportFunctional μ f.body≤a) :
    Spherical.objective b g.toSeminorm≤Spherical.objective b (f.scale a ha).toSeminorm := by
  have hp := f.functional_pos hV hμ hq
  have hn : supportFunctional μ (f.scale _ hp).body=1 := by
    rw [f.functional_scale _ hp μ,inv_mul_cancel₀ hp.ne']
  apply (hmin _ hn).trans
  apply Spherical.objective_mono b ((f.scale _ hp).ne_zero hV) ((f.scale _ ha).ne_zero hV)
  intro x
  exact mul_le_mul_of_nonneg_right hle (apply_nonneg f.toSeminorm x)

end RelativeGauge
end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.VariationalRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere sigma mean objective objectiveIntegrand)
namespace RelativeGauge
variable {n : ℕ} [NeZero n]

/-- Actual Euler equation for the normalized variational optimizer. The test
is only continuous, even and degree-one homogeneous, not assumed convex. -/
theorem normalized_representation {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0<cosineSeminorm μ hμ x) (b : Bool)
    (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) (hgn : supportFunctional μ g.body=1)
    (hmin : ∀ q : RelativeGauge (⊤ : Submodule ℝ (Space n)),supportFunctional μ q.body=1 →
      objective b g.toSeminorm≤objective b q.toSeminorm)
    (φ : Space n → ℝ) (hφ : Continuous φ) (heven : ∀ x,φ (-x)=φ x)
    (hh : ∀ a : ℝ,0<a → ∀ x,φ (a • x)=a*φ x) :
    (∫ x,φ x ∂μ)*(if b then 1 else objective false g.toSeminorm)=
      mean (fun u : Sphere n => (if b then 1 else g u)*φ (∇ (fun x => g x) (u:Space n))) := by
  let s : C(Sphere n,ℝ) := ⟨fun u => support g.body u,(support_continuous g.compact).comp continuous_subtype_val⟩
  let φs : C(Sphere n,ℝ) := ⟨fun u => φ u,hφ.comp continuous_subtype_val⟩
  have hs : ∀ u,0<s u := support_pos_of_nhds g.compact g.top_nhds
  have hw : wulff s=g.body := wulff_support g.compact g.convex g.nonempty
  have hge : gauge (wulff s)=(fun x => g x) := by ext x; rw [hw,g.top_gauge]
  let I := ∫ x,φ x ∂μ
  let F : ℝ → ℝ := fun t => mean (fun u : Sphere n => objectiveIntegrand b (gauge (wulff ⇑(s+t • φs)) (u:Space n)))
  let D := mean (fun u : Sphere n => (if b then 1 else g u)*φ (∇ (fun x => g x) (u:Space n)))
  let H : ℝ → ℝ := fun t => if b then Real.log (1+t*I)+F t else (1+t*I)*F t
  have hF0 : F 0=objective b g.toSeminorm := by
    simp only [F,zero_smul,add_zero,hge,objective]
  have hFder : HasDerivAt F (-D) 0 := by
    have h := wulff_objective_derivative b s hs φ hφ hh
    rw [hge] at h
    exact h
  have hlin : HasDerivAt (fun t : ℝ => 1+t*I) I 0 := by
    simpa only [one_mul,id_eq] using (((hasDerivAt_id (0:ℝ)).mul_const I).const_add 1)
  have hH0 : H 0=objective b g.toSeminorm := by
    dsimp only [H]; rw [zero_mul,add_zero,Real.log_one,zero_add,one_mul]; split <;> exact hF0
  have hHder : HasDerivAt H (I*(if b then 1 else objective false g.toSeminorm)-D) 0 := by
    cases b
    · have hd := hlin.mul hFder
      simpa only [Pi.mul_def,H,Bool.false_eq_true,ite_false,zero_mul,add_zero,one_mul,hF0,mul_neg,one_mul,sub_eq_add_neg] using hd
    · have hd := (hlin.log (by norm_num)).add hFder
      simpa only [Pi.add_def,H,ite_true,zero_mul,add_zero,div_one,mul_one,sub_eq_add_neg] using hd
  have hHmin : IsLocalMin H 0 := by
    have hpos : ∀ᶠ t in 𝓝 (0:ℝ),0<1+t*I := by
      have hc : Continuous (fun t : ℝ => 1+t*I) := by fun_prop
      have hh := hc.continuousAt.eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1+0*I))
      exact hh
    filter_upwards [positive_constraints_nhds s φs hs,hpos] with t ht htp
    rw [hH0]
    have hsym : ∀ u : Sphere n,(s+t • φs) ⟨-(u:Space n),by simp⟩=(s+t • φs) u := by
      intro u
      change support g.body (-(u:Space n))+t*φ (-(u:Space n))=support g.body u+t*φ u
      rw [support_even g.compact g.nonempty (fun _ h => g.neg_mem h),heven]
    let f := ofFullBody (wulff_compact (s+t • φs) ht) (wulff_convex _) (wulff_balanced _ hsym) (wulff_nhds (s+t • φs) ht)
    have hfb : f.body=wulff ⇑(s+t • φs) := body_ofFullBody _ _ _ _
    have hbound : supportFunctional μ f.body≤1+t*I := by
      rw [hfb]
      have hb := functional_wulff_bound hμ g.compact g.nonempty φ hφ hh t ht
      rw [hgn] at hb
      exact hb
    have hlo := minimizer_scaled_lower hμ (show (⊤ : Submodule ℝ (Space n))≠⊥ from top_ne_bot)
      (fun x _ hx => hq x hx) b hmin f htp hbound
    have hscale := Spherical.objective_scale b (g := f.toSeminorm)
      (f := (f.scale (1+t*I) htp).toSeminorm) (f.ne_zero top_ne_bot) htp (fun _ => rfl)
    rw [hscale] at hlo
    have hfobj : objective b f.toSeminorm=F t := by
      unfold objective
      congr 1
      funext u
      rw [← f.top_gauge,hfb]
    rw [hfobj] at hlo
    exact hlo
  have hz := hHmin.hasDerivAt_eq_zero hHder
  exact sub_eq_zero.mp hz

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe mean sigma)

lemma normalizedVolume_pow {n : ℕ} [NeZero n] (K : Set (Space n)) :
    normalizedVolume K^n=volume.real K/kappa n := by
  rw [normalizedVolume_formula]
  exact Real.rpow_inv_natCast_pow (div_nonneg measureReal_nonneg (kappa_pos n).le) (NeZero.ne n)

namespace RelativeGauge
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
lemma top_pos (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) (u : Sphere n) : 0 < g u :=
  g.pos (Submodule.mem_top) (by intro h;simpa [h] using norm_coe u)

lemma volumeNormalize_body_volume (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) :
    volume.real g.volumeNormalize.body=kappa n := by
  have ha := normalizedVolume_pos g.compact g.top_interior
  rw [volumeNormalize,g.body_scale,volumeReal_smul_nonneg (inv_nonneg.mpr ha.le),
    finrank_euclideanSpace_fin,inv_pow,normalizedVolume_pow]
  field_simp [(volumeReal_pos_of_body g.compact g.top_interior).ne',(kappa_pos n).ne']

lemma volumeNormalize_moment (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) :
    mean (fun u : Sphere n => (g.volumeNormalize u)⁻¹^n)=1 := by
  have hh := gauge_volume g.volumeNormalize.convex g.volumeNormalize.top_nhds
    (fun u => by rw [g.volumeNormalize.top_gauge];exact g.volumeNormalize.top_pos u)
  simp_rw [g.volumeNormalize.top_gauge] at hh
  rw [g.volumeNormalize_body_volume] at hh
  exact (mul_left_cancel₀ (kappa_pos n).ne' (by simpa only [mul_one] using hh.symm))

omit [NeZero n] in
lemma full_body_of_sphere_one (g : RelativeGauge (⊤ : Submodule ℝ (Space n)))
    (hg : ∀ u : Sphere n,g u=1) : g.body=unitBall n := by
  have he (x : Space n) : g x=‖x‖ := by
    by_cases hx : x=0
    · simp [hx]
    let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hx]⟩
    have h := hg u
    change g.toSeminorm (‖x‖⁻¹ • x)=1 at h
    rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at h
    have hn := norm_ne_zero_iff.mpr hx
    field_simp at h
    exact h
  ext x
  rw [g.top_body]
  change g x≤1 ↔ x∈closedBall 0 1
  rw [he,mem_closedBall,dist_zero_right]

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere mean sigma gaugeField gaugeMoment)

lemma exponent_pos (n : ℕ) : 0 < Scalar.exponent n := by unfold Scalar.exponent;split_ifs <;> norm_num

namespace RelativeGauge
variable {n : ℕ} [NeZero n] {μ : Measure (Space n)}

omit [NeZero n] in
lemma scale_field_ae (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) {a : ℝ} (ha : 0 < a)
    {k : ℕ} (hk : 0 < k) :
    gaugeField (g.scale a ha).toSeminorm k =ᵐ[sigma n] (fun u => a^k • gaugeField g.toSeminorm k u) := by
  filter_upwards [Spherical.seminorm_ae_differentiable_sphere g.toSeminorm] with u hu
  have hgrad : ∇ (fun x => g.scale a ha x) (u:Space n)=a • ∇ (fun x => g x) (u:Space n) := by
    apply (InnerProductSpace.toDual ℝ (Space n)).injective
    rw [toDual_gradient,map_smul,toDual_gradient]
    exact fderiv_const_mul hu a
  change (a*g u)^(k-1) • ∇ (fun x => g.scale a ha x) (u:Space n)=_
  rw [hgrad,mul_pow,smul_smul]
  change (a^(k-1)*g u^(k-1)*a) • _=a^k • (g u^(k-1) • _)
  rw [smul_smul]
  congr 1
  have hp : a^k=a^(k-1)*a := by
    conv_lhs => rw [show k=(k-1)+1 by omega,pow_succ]
  rw [hp]
  ring

omit [NeZero n] in
lemma scale_moment (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) {a : ℝ} (ha : 0 < a) (k : ℕ) :
    gaugeMoment (g.scale a ha).toSeminorm k=a^k*gaugeMoment g.toSeminorm k := by
  change mean (fun u : Sphere n => (a*g u)^k)=_
  simp only [mul_pow,gaugeMoment,mean,integral_const_mul]

lemma minimizer_field_representation
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0 < cosineSeminorm μ hμ x)
    (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) (hgn : supportFunctional μ g.body=1)
    (hmin : ∀ q : RelativeGauge (⊤ : Submodule ℝ (Space n)),supportFunctional μ q.body=1 →
      Spherical.objective (regime n) g.toSeminorm≤Spherical.objective (regime n) q.toSeminorm)
    (φ : Space n → ℝ) (hφ : Continuous φ) (heven : ∀ x,φ (-x)=φ x)
    (hh : ∀ a : ℝ,0 < a → ∀ x,φ (a • x)=a*φ x) :
    (∫ x,φ x ∂μ)*gaugeMoment g.toSeminorm (Scalar.exponent n-1)=
      mean (fun u : Sphere n => φ (gaugeField g.toSeminorm (Scalar.exponent n) u)) := by
  have hv := normalized_representation hμ hq (regime n) g hgn hmin φ hφ heven hh
  have he : mean (fun u : Sphere n => φ (gaugeField g.toSeminorm (Scalar.exponent n) u))=
      mean (fun u : Sphere n => (if regime n then 1 else g u)*φ (∇ (fun x => g x) (u:Space n))) := by
    congr 1
    funext u
    by_cases hn : n=4
    · simp [gaugeField,Scalar.exponent,regime,hn]
    · simp only [gaugeField,Scalar.exponent,ite_eq_right hn,Nat.reduceSub,pow_one,
        regime,decide_eq_false hn,Bool.false_eq_true,ite_false]
      exact hh _ (g.top_pos u) _
  rw [he]
  convert hv using 1
  congr 1
  by_cases hn : n=4
  · simp [gaugeMoment,Scalar.exponent,regime,hn,Spherical.mean_const]
  · simp [gaugeMoment,Scalar.exponent,regime,hn,Spherical.objective,Spherical.objectiveIntegrand]

lemma scaled_field_representation
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0 < cosineSeminorm μ hμ x)
    (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) (hgn : supportFunctional μ g.body=1)
    (hmin : ∀ q : RelativeGauge (⊤ : Submodule ℝ (Space n)),supportFunctional μ q.body=1 →
      Spherical.objective (regime n) g.toSeminorm≤Spherical.objective (regime n) q.toSeminorm)
    {a : ℝ} (ha : 0 < a)
    (φ : Space n → ℝ) (hφ : Continuous φ) (heven : ∀ x,φ (-x)=φ x)
    (hh : ∀ r : ℝ,0 < r → ∀ x,φ (r • x)=r*φ x) :
    (∫ x,φ x ∂μ)*gaugeMoment (g.scale a ha).toSeminorm (Scalar.exponent n-1)=
      supportFunctional μ (g.scale a ha).body*
        mean (fun u : Sphere n => φ (gaugeField (g.scale a ha).toSeminorm (Scalar.exponent n) u)) := by
  have he : mean (fun u : Sphere n => φ (gaugeField (g.scale a ha).toSeminorm (Scalar.exponent n) u))=
      a^(Scalar.exponent n)*mean (fun u : Sphere n => φ (gaugeField g.toSeminorm (Scalar.exponent n) u)) := by
    simp only [mean]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [g.scale_field_ae ha (exponent_pos n)] with u hu
    rw [hu,hh _ (pow_pos ha _)]
  rw [g.scale_moment ha,g.functional_scale,hgn,mul_one,he]
  have hr := minimizer_field_representation hμ hq g hgn hmin φ hφ heven hh
  rw [← hr]
  have hk : a^(Scalar.exponent n)=a^(Scalar.exponent n-1)*a := by
    rw [← pow_succ];congr 1;have := exponent_pos n;omega
  rw [hk]
  field_simp

end RelativeGauge
end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.GaussianMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe surface sigma mean)

lemma gaussianRadial_eq (d : ℕ) : gaussianRadial d=(1/2:ℝ)*Real.Gamma (((d:ℝ)+1)/2) := by
  simpa only [gaussianRadial,Real.rpow_natCast,Real.rpow_two] using
    integral_rpow_mul_exp_neg_rpow (p := (2:ℝ)) (q := (d:ℝ)) (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) d])

lemma gaussianRadial_pos (d : ℕ) : 0<gaussianRadial d := by
  rw [gaussianRadial_eq]
  exact mul_pos (by norm_num) (Real.Gamma_pos_of_pos (by positivity))

lemma gaussianRadial_add_two (d : ℕ) :
    gaussianRadial (d+2)=((d:ℝ)+1)/2*gaussianRadial d := by
  rw [gaussianRadial_eq,gaussianRadial_eq]
  have he : (((d+2:ℕ):ℝ)+1)/2=((d:ℝ)+1)/2+1 := by push_cast;ring
  rw [he,Real.Gamma_add_one (by positivity)]
  ring

lemma integral_radial_gaussian (m k : ℕ) :
    (∫ r : Ioi (0:ℝ),r.val^k*Real.exp (-(r.val^2)) ∂Measure.volumeIoiPow m)=gaussianRadial (m+k) := by
  simp only [Measure.volumeIoiPow,ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul]
  · rw [integral_subtype_comap measurableSet_Ioi (fun r : ℝ => (r^m).toNNReal • (r^k*Real.exp (-(r^2))))]
    unfold gaussianRadial
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [NNReal.smul_def,Real.coe_toNNReal _ (pow_nonneg hx.le _),pow_add]
    ring
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

lemma surface_integral_eq_mean {n : ℕ} [NeZero n] (f : Sphere n → ℝ) :
    (∫ u,f u ∂surface n)=(n:ℝ)*kappa n*mean f := by
  rw [mean,sigma,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  change _=(n:ℝ)*kappa n*(((surface n).real univ)⁻¹* _)
  rw [surface_real_univ]
  field_simp [(kappa_pos n).ne',(Nat.cast_pos.mpr (NeZero.pos n) : (0:ℝ)<n).ne']

/-- Polar separation for any positively homogeneous integrand. No smoothness
or differentiability is used, and the Bochner integral has its ordinary meaning. -/
lemma homogeneous_gaussian_integral {n : ℕ} [NeZero n] (k : ℕ) (f : Space n → ℝ)
    (hh : ∀ r : ℝ,0<r → ∀ x,f (r • x)=r^k*f x) :
    (∫ x,f x*Real.exp (-(‖x‖^2)))=
      (n:ℝ)*kappa n*mean (fun u : Sphere n => f u)*gaussianRadial (n-1+k) := by
  let F : Space n → ℝ := fun x => f x*Real.exp (-(‖x‖^2))
  let ν := Measure.volumeIoiPow (Module.finrank ℝ (Space n)-1)
  have he : (∫ x,F x)=∫ x : ({0}ᶜ : Set (Space n)),F x ∂volume.comap Subtype.val := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl,restrict_compl_singleton]
  rw [show (∫ x,f x*Real.exp (-(‖x‖^2)))=∫ x,F x from rfl,he]
  have hm := (volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd
  rw [← (hm.symm (homeomorphUnitSphereProd (Space n)).toMeasurableEquiv).integral_comp
    (homeomorphUnitSphereProd (Space n)).symm.measurableEmbedding (fun x => F x)]
  have hfun : (fun z : Sphere n × Ioi (0:ℝ) => F ↑((homeomorphUnitSphereProd (Space n)).symm z))=
      (fun z => f z.1*(z.2.val^k*Real.exp (-(z.2.val^2)))) := by
    funext z
    rw [homeomorphUnitSphereProd_symm_apply_coe]
    dsimp only [F]
    rw [hh _ z.2.property,norm_smul,Real.norm_of_nonneg z.2.property.le,norm_coe,mul_one]
    ring
  change (∫ z : Sphere n × Ioi (0:ℝ),F ↑((homeomorphUnitSphereProd (Space n)).symm z) ∂(surface n).prod ν)=_
  rw [hfun]
  rw [integral_prod_mul (fun u : Sphere n => f u) (fun r : Ioi (0:ℝ) => r.val^k*Real.exp (-(r.val^2))),
    surface_integral_eq_mean]
  dsimp only [ν]
  rw [integral_radial_gaussian]
  simp only [finrank_euclideanSpace_fin]

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
variable {n : ℕ}

lemma functional_map {μ : Measure (Space n)} (A : Space n →L[ℝ] Space n)
    {K : Set (Space n)} (hK : IsCompact K) :
    supportFunctional (μ.map A) K=∫ x,support K (A x) ∂μ := by
  exact integral_map A.continuous.measurable.aemeasurable (support_continuous hK).aestronglyMeasurable

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.PositionMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe surface sigma mean)

lemma gaussian_real_second_moment :
    (∫ t : ℝ,t^2*Real.exp (-(t^2)))=(1/2:ℝ)*(∫ t : ℝ,Real.exp (-(t^2))) := by
  have h0 := integral_fun_norm_addHaar (volume : Measure ℝ) (fun r : ℝ => Real.exp (-(r^2)))
  have h2 := integral_fun_norm_addHaar (volume : Measure ℝ) (fun r : ℝ => r^2*Real.exp (-(r^2)))
  simp only [Module.finrank_self,Nat.sub_self,pow_zero,one_smul,Real.norm_eq_abs,sq_abs] at h0 h2
  have he : (∫ r in Ioi (0:ℝ),Real.exp (-(r^2)))=gaussianRadial 0 := by simp [gaussianRadial]
  change _=volume.real (ball (0:ℝ) 1)*gaussianRadial 2 at h2
  rw [he] at h0
  change _=volume.real (ball (0:ℝ) 1)*gaussianRadial 0 at h0
  rw [h2,h0,show (2:ℕ)=0+2 from rfl,gaussianRadial_add_two]
  norm_num
  ring

lemma seminorm_add_kernel {n : ℕ} (g : Seminorm ℝ (Space n)) {e : Space n}
    (he : g e=0) (x : Space n) (t : ℝ) : g (x+t • e)=g x := by
  have h1 := map_add_le_add g x (t • e)
  have h2 := map_add_le_add g (x+t • e) (-(t • e))
  have hz : g (t • e)=0 := by rw [map_smul_eq_mul,he,mul_zero]
  rw [hz,add_zero] at h1
  rw [add_neg_cancel_right,map_neg_eq_map,hz,add_zero] at h2
  exact le_antisymm h1 h2

lemma gaussian_shadow_norm {n : ℕ} (e : Sphere n) (z : perpendicular (e:Space n)) (t : ℝ) :
    ‖(z:Space n)+t • (e:Space n)‖^2=‖z‖^2+t^2 := by
  rw [norm_add_sq_real,inner_smul_right,real_inner_comm,perpendicular_inner,norm_smul,
    Real.norm_eq_abs,mul_pow,norm_coe,one_pow,mul_one,sq_abs]
  simp

/-- Genuine Gaussian independence in a seminorm kernel, proved by the
measure-preserving orthogonal coordinate map and Fubini product integrals. -/
lemma gaussian_kernel_moment {n : ℕ} (g : Seminorm ℝ (Space n)) (k : ℕ)
    (e : Sphere n) (he : g e=0) :
    (∫ x : Space n,g x^k*⟪(e:Space n),x⟫^2*Real.exp (-(‖x‖^2)))=
      (1/2:ℝ)*(∫ x : Space n,g x^k*Real.exp (-(‖x‖^2))) := by
  let F : perpendicular (e:Space n) → ℝ := fun z => g z^k*Real.exp (-(‖z‖^2))
  have he0 : (fun z : perpendicular (e:Space n) × ℝ =>
      g (shadowMeasurableEquiv e z)^k*Real.exp (-(‖shadowMeasurableEquiv e z‖^2)))=
      (fun z => F z.1*Real.exp (-(z.2^2))) := by
    funext z
    change g ((z.1:Space n)+z.2 • (e:Space n))^k*Real.exp (-‖(z.1:Space n)+z.2 • (e:Space n)‖^2)=_
    rw [seminorm_add_kernel g he,gaussian_shadow_norm,neg_add,Real.exp_add]
    dsimp only [F]
    ring
  have he2 : (fun z : perpendicular (e:Space n) × ℝ =>
      g (shadowMeasurableEquiv e z)^k*⟪(e:Space n),shadowMeasurableEquiv e z⟫^2*
        Real.exp (-(‖shadowMeasurableEquiv e z‖^2)))=
      (fun z => F z.1*(z.2^2*Real.exp (-(z.2^2)))) := by
    funext z
    change g ((z.1:Space n)+z.2 • (e:Space n))^k*⟪(e:Space n),(z.1:Space n)+z.2 • (e:Space n)⟫^2*
      Real.exp (-‖(z.1:Space n)+z.2 • (e:Space n)‖^2)=_
    rw [seminorm_add_kernel g he,gaussian_shadow_norm,neg_add,Real.exp_add,
      inner_add_right,perpendicular_inner,inner_smul_right,real_inner_self_eq_norm_sq,norm_coe]
    dsimp only [F]
    ring
  rw [← (shadowMeasurableEquiv_measurePreserving e).integral_comp (shadowMeasurableEquiv e).measurableEmbedding
    (fun x : Space n => g x^k*⟪(e:Space n),x⟫^2*Real.exp (-(‖x‖^2))),
    ← (shadowMeasurableEquiv_measurePreserving e).integral_comp (shadowMeasurableEquiv e).measurableEmbedding
    (fun x : Space n => g x^k*Real.exp (-(‖x‖^2)))]
  rw [he0,he2,Measure.volume_eq_prod,
    integral_prod_mul F (fun t : ℝ => t^2*Real.exp (-(t^2))),
    integral_prod_mul F (fun t : ℝ => Real.exp (-(t^2))),gaussian_real_second_moment]
  ring

/-- The boundary moment ratio, for every seminorm and every natural
homogeneity degree, including all singular and nonsmooth cases. -/
theorem sphere_kernel_moment {n : ℕ} [NeZero n] (g : Seminorm ℝ (Space n)) (k : ℕ)
    (e : Sphere n) (he : g e=0) :
    ((n:ℝ)+k)*mean (fun u : Sphere n => g u^k*⟪(e:Space n),(u:Space n)⟫^2)=
      mean (fun u : Sphere n => g u^k) := by
  have hh0 : ∀ r : ℝ,0<r → ∀ x : Space n,g (r • x)^k=r^k*g x^k := by
    intro r hr x
    rw [map_smul_eq_mul,Real.norm_of_nonneg hr.le,mul_pow]
  have hh2 : ∀ r : ℝ,0<r → ∀ x : Space n,g (r • x)^k*⟪(e:Space n),r • x⟫^2=
      r^(k+2)*(g x^k*⟪(e:Space n),x⟫^2) := by
    intro r hr x
    rw [hh0 r hr,inner_smul_right,mul_pow,pow_add]
    ring
  have hG := gaussian_kernel_moment g k e he
  rw [homogeneous_gaussian_integral (k+2) _ hh2,homogeneous_gaussian_integral k _ hh0] at hG
  rw [show n-1+(k+2)=(n-1+k)+2 by omega,gaussianRadial_add_two] at hG
  have hn : ((n-1+k:ℕ):ℝ)+1=(n:ℝ)+k := by
    have hh : n-1+k+1=n+k := by have := NeZero.pos n;omega
    exact_mod_cast hh
  rw [hn] at hG
  have hc : (n:ℝ)*kappa n*gaussianRadial (n-1+k)≠0 :=
    mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne n)) (kappa_pos n).ne') (gaussianRadial_pos _).ne'
  apply (mul_left_cancel₀ hc)
  nlinarith only [hG]

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection.Position
variable {n : ℕ}
lemma quad_basis_add (A : Mat n) (i j : Fin n) (a b : ℝ) :
    quad A (a • EuclideanSpace.single i 1+b • EuclideanSpace.single j 1)=
      a^2*A (i,i)+a*b*(A (i,j)+A (j,i))+b^2*A (j,j) := by
  simp [quad_eq,add_mul,mul_add,Finset.sum_add_distrib]
  ring
end PettyProjection.Position
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection.Position
open Spherical (Sphere mean sigma norm_coe continuous_integrable seminorm_continuous)
variable {n : ℕ} [NeZero n]

lemma mean_power_pos (g : Seminorm ℝ (Space n)) (hg : g≠0) (k : ℕ) :
    0 < mean (fun u : Sphere n => g u^k) := by
  obtain ⟨R,e,hR,_,hb⟩ := Spherical.seminorm_coordinate_minorant g hg
  have he := hb e
  simp only [real_inner_self_eq_norm_sq,norm_coe,one_pow,abs_one,mul_one] at he
  have hc : Continuous (fun u : Sphere n => g u^k) := ((seminorm_continuous n g).comp continuous_subtype_val).pow k
  apply integral_pos_of_integrable_nonneg_nonzero (x := e) hc (continuous_integrable hc)
    (fun u => pow_nonneg (apply_nonneg g (u:Space n)) k)
  exact (pow_pos (hR.trans_le he) k).ne'

omit [NeZero n] in
lemma field_symmetric (g : Seminorm ℝ (Space n)) (k : ℕ) : Symmetric (momentField g k) := by
  intro i j
  change mean _ / _ - _ / _=mean _ / _ - _ / _
  congr 2
  · congr 1; funext u; ring
  · simp only [eq_comm]

lemma field_quad (g : Seminorm ℝ (Space n)) (k : ℕ) (x : Space n) :
    quad (momentField g k) x=mean (fun u : Sphere n => g u^k*⟪x,(u:Space n)⟫^2)/
      mean (fun u : Sphere n => g u^k)-‖x‖^2/(n:ℝ) := by
  have hc (i j : Fin n) : Continuous (fun u : Sphere n =>
      g u^k*(u:Space n) i*(u:Space n) j*x i*x j) := by
    exact (((((seminorm_continuous n g).comp continuous_subtype_val).pow k).mul (by fun_prop)).mul (by fun_prop)).mul continuous_const |>.mul continuous_const
  have hnum : (∑ i : Fin n,∑ j : Fin n,
      mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) j)*x i*x j)=
      mean (fun u : Sphere n => g u^k*⟪x,(u:Space n)⟫^2) := by
    have hi (i : Fin n) : (∑ j : Fin n,mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) j)*x i*x j)=
        mean (fun u : Sphere n => ∑ j : Fin n,g u^k*(u:Space n) i*(u:Space n) j*x i*x j) := by
      simp_rw [mean,← integral_mul_const]
      exact (integral_finsetSum _ (fun j _ => continuous_integrable (hc i j))).symm
    simp_rw [hi]
    rw [← Spherical.mean_sum _ (fun i _ => continuous_finsetSum _ (fun j _ => hc i j))]
    congr 1
    funext u
    simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,sq,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [quad_eq]
  simp only [momentField,sub_mul,Finset.sum_sub_distrib]
  have hdiv : (∑ i : Fin n,∑ j : Fin n,
      mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) j)/mean (fun u : Sphere n => g u^k)*x i*x j)=
      mean (fun u : Sphere n => g u^k*⟪x,(u:Space n)⟫^2)/mean (fun u : Sphere n => g u^k) := by
    simp_rw [div_mul_eq_mul_div,← Finset.sum_div]
    rw [hnum]
  rw [hdiv]
  congr 1
  simp only [ite_div,zero_div,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [Finset.sum_div]
  simp only [one_div,sq]
  apply Finset.sum_congr rfl
  intro i _
  ring

end PettyProjection.Position
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.AffinePosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere mean sigma gaugeField gaugeMoment absolutePair)

lemma represents_pair {n : ℕ} [NeZero n] {μ ν : Measure (Space n)}
    (hν : Integrable (fun x : Space n => ‖x‖) ν)
    (f g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k) {s t : ℝ}
    (hf : Represents μ f k s) (hg : Represents ν g k t) :
    measurePair μ ν=s*t*absolutePair (gaugeField f k) (gaugeField g k) := by
  have hcos : measurePair μ ν=∫ x,cosineSeminorm ν hν x ∂μ := by
    unfold measurePair
    apply integral_congr_ae
    filter_upwards [] with x
    change (∫ y,|⟪x,y⟫| ∂ν)=∫ y,|⟪y,x⟫| ∂ν
    simp only [real_inner_comm x]
  rw [hcos,hf _ (Spherical.seminorm_continuous n _) (fun x => map_neg_eq_map _ x)
    (fun r hr x => by rw [map_smul_eq_mul,Real.norm_of_nonneg hr.le])]
  have he (u : Sphere n) : cosineSeminorm ν hν (gaugeField f k u)=
      t*mean (fun v : Sphere n => |⟪gaugeField f k u,gaugeField g k v⟫|) := by
    have hh := hg (fun x => |⟪gaugeField f k u,x⟫|) (by fun_prop)
      (fun x => by simp) (fun r hr x => by simp only [inner_smul_right,abs_mul,abs_of_pos hr])
    change (∫ x,|⟪x,gaugeField f k u⟫| ∂ν)=_
    simpa only [real_inner_comm (gaugeField f k u)] using hh
  simp_rw [he]
  rw [mean,integral_const_mul,mul_assoc]
  congr 1
  congr 1
  exact (integral_prod _ (Spherical.gaugeField_absolute_integrable f g hk)).symm

namespace RelativeGauge
variable {n : ℕ} [NeZero n] {μ : Measure (Space n)}

lemma scaled_represents
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0 < cosineSeminorm μ hμ x)
    (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) (hgn : supportFunctional μ g.body=1)
    (hmin : ∀ q : RelativeGauge (⊤ : Submodule ℝ (Space n)),supportFunctional μ q.body=1 →
      Spherical.objective (regime n) g.toSeminorm≤Spherical.objective (regime n) q.toSeminorm)
    {a : ℝ} (ha : 0 < a) :
    Represents μ (g.scale a ha).toSeminorm (Scalar.exponent n)
      (supportFunctional μ (g.scale a ha).body/gaugeMoment (g.scale a ha).toSeminorm (Scalar.exponent n-1)) := by
  intro φ hφ he hh
  have ht : 0 < gaugeMoment (g.scale a ha).toSeminorm (Scalar.exponent n-1) :=
    Position.mean_power_pos _ ((g.scale a ha).ne_zero top_ne_bot) _
  have h := scaled_field_representation hμ hq g hgn hmin ha φ hφ he hh
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff ht.ne').mpr h

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma volumeReal_linearEquiv (T : Space n ≃L[ℝ] Space n) (K : Set (Space n)) :
    volume.real (T '' K)=|LinearMap.det T.toLinearMap| * volume.real K := by
  unfold Measure.real
  rw [Measure.addHaar_image_continuousLinearEquiv,ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _)]

lemma linearEquiv_body (T : Space n ≃L[ℝ] Space n) {K : Set (Space n)} (hK : IsConvexBody K) :
    IsConvexBody (T '' K) := by
  refine ⟨hK.1.image T.continuous,hK.2.1.linear_image T.toLinearMap,?_⟩
  change (interior (T.toHomeomorph '' K)).Nonempty
  rw [← T.toHomeomorph.image_interior]
  exact hK.2.2.image T

lemma linearEquiv_det_ne_zero (T : Space n ≃L[ℝ] Space n) : LinearMap.det T.toLinearMap≠0 :=
  T.toLinearEquiv.isUnit_det'.ne_zero

lemma volumeFactor_pos (T : Space n ≃L[ℝ] Space n) : 0 < volumeFactor T :=
  Real.rpow_pos_of_pos (abs_pos.mpr (linearEquiv_det_ne_zero T)) _

lemma normalizedVolume_linearEquiv (T : Space n ≃L[ℝ] Space n) (K : Set (Space n)) :
    normalizedVolume (T '' K)=volumeFactor T*normalizedVolume K := by
  rw [normalizedVolume,volumeRoot,volumeReal_linearEquiv,
    Real.mul_rpow (abs_nonneg _) measureReal_nonneg]
  unfold volumeFactor normalizedVolume volumeRoot
  ring

lemma volumeFactor_symm (T : Space n ≃L[ℝ] Space n) : volumeFactor T.symm=(volumeFactor T)⁻¹ := by
  unfold volumeFactor
  rw [show T.symm.toLinearMap=(T.toLinearEquiv.symm : Space n →ₗ[ℝ] Space n) from rfl,
    LinearEquiv.det_coe_symm,abs_inv,Real.inv_rpow (abs_nonneg _)]

lemma symmetric_equiv_symm (T : Space n ≃L[ℝ] Space n) (hT : T.toLinearMap.IsSymmetric) :
    T.symm.toLinearMap.IsSymmetric := by
  intro x y
  change ⟪T.symm x,y⟫=⟪x,T.symm y⟫
  have hh := hT (T.symm x) (T.symm y)
  change ⟪T (T.symm x),T.symm y⟫=⟪T.symm x,T (T.symm y)⟫ at hh
  simpa only [T.apply_symm_apply] using hh.symm

lemma functional_map_symmetric {μ : Measure (Space n)} (T : Space n ≃L[ℝ] Space n)
    (hT : T.toLinearMap.IsSymmetric) {K : Set (Space n)} (hK : IsCompact K) (hne : K.Nonempty) :
    supportFunctional (μ.map T) K=supportFunctional μ (T '' K) := by
  change supportFunctional (μ.map T.toContinuousLinearMap) K=_
  rw [functional_map T.toContinuousLinearMap hK]
  unfold supportFunctional
  apply integral_congr_ae
  filter_upwards [] with x
  change support K (T.toContinuousLinearMap x)=support (T.toContinuousLinearMap '' K) x
  rw [support_linear_image hK hne T.toContinuousLinearMap,hT.clm_adjoint_eq]

lemma measurePair_cosine {μ ν : Measure (Space n)}
    (hν : Integrable (fun x : Space n => ‖x‖) ν) :
    measurePair μ ν=∫ x,cosineSeminorm ν hν x ∂μ := by
  unfold measurePair
  apply integral_congr_ae
  filter_upwards [] with x
  change (∫ y,|⟪x,y⟫| ∂ν)=∫ y,|⟪y,x⟫| ∂ν
  simp only [real_inner_comm x]

lemma measurePair_map_symmetric {μ ν : Measure (Space n)}
    (hν : Integrable (fun x : Space n => ‖x‖) ν)
    (T : Space n ≃L[ℝ] Space n) (hT : T.toLinearMap.IsSymmetric) :
    measurePair (μ.map T) (ν.map T.symm)=measurePair μ ν := by
  change measurePair (μ.map T.toContinuousLinearMap) (ν.map T.symm.toContinuousLinearMap)=_
  rw [measurePair_cosine (norm_integrable_map hν T.symm.toContinuousLinearMap),
    integral_map T.toContinuousLinearMap.continuous.measurable.aemeasurable (Spherical.seminorm_continuous n _).aestronglyMeasurable,
    measurePair_cosine hν]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [cosine_map ν hν T.symm.toContinuousLinearMap,(symmetric_equiv_symm T hT).clm_adjoint_eq]
  simp

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection.Position
open Spherical
variable {n : ℕ} [NeZero n]

lemma mean_inner_sq (x : Space n) : (n:ℝ)*mean (fun u : Sphere n => ⟪x,(u:Space n)⟫^2)=‖x‖^2 := by
  by_cases hx : x=0
  · simp [hx,mean]
  let e : Sphere n := ⟨‖x‖⁻¹ • x,by rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
  have he := sphere_kernel_moment (0 : Seminorm ℝ (Space n)) 0 e (by simp)
  simp only [Nat.cast_zero,add_zero,pow_zero,one_mul,mean_const] at he
  have hh : mean (fun u : Sphere n => ⟪(e:Space n),(u:Space n)⟫^2)=
      ‖x‖⁻¹^2*mean (fun u : Sphere n => ⟪x,(u:Space n)⟫^2) := by
    simp only [e,inner_smul_left,conj_trivial,mul_pow,mean,integral_const_mul]
  rw [hh] at he
  have hn := norm_ne_zero_iff.mpr hx
  field_simp at he
  nlinarith [sq_pos_of_ne_zero hn]

omit [NeZero n] in
lemma symmetric_eq_zero_of_quad {A : Mat n} (hA : Symmetric A) (hq : ∀ x,quad A x=0) : A=0 := by
  have hd (i : Fin n) : A (i,i)=0 := by rw [← quad_basis,hq]
  apply WithLp.ofLp_injective
  funext ij
  have hh := hq (EuclideanSpace.single ij.1 1+EuclideanSpace.single ij.2 1)
  have he := quad_basis_add A ij.1 ij.2 1 1
  simp only [one_smul,one_pow,one_mul,hd,hA ij.2 ij.1] at he
  change A ij=0
  linarith

lemma constantMomentField_zero : momentField (0 : Seminorm ℝ (Space n)) 0=0 := by
  apply symmetric_eq_zero_of_quad (field_symmetric _ _) (fun x => ?_)
  rw [field_quad]
  simp only [pow_zero,one_mul,mean_const,div_one]
  have hm := mean_inner_sq x
  have hn : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [sub_eq_zero,eq_div_iff hn]
  linarith

lemma coordinateProduct_mean (i j : Fin n) : mean (coordinateProduct n i j)=(if i=j then 1 else 0)/(n:ℝ) := by
  have hh := congrArg (fun A : Mat n => A (i,j)) (constantMomentField_zero (n := n))
  change mean (fun u : Sphere n => (0 : Seminorm ℝ (Space n)) u^0*(u:Space n) i*(u:Space n) j)/
    mean (fun u : Sphere n => (0 : Seminorm ℝ (Space n)) u^0)-(if i=j then 1 else 0)/(n:ℝ)=0 at hh
  simp only [pow_zero,one_mul,mean_const,div_one] at hh
  exact sub_eq_zero.mp hh

/-- The matrix isotropy condition gives precisely the actual H₂ projection,
not a replacement cancellation condition. -/
lemma field_zero_harmonic {n : ℕ} (hn : 2≤n) [NeZero n] (g : Seminorm ℝ (Space n))
    (hg : g≠0) (k : ℕ) (hF : momentField g k=0) :
    (harmonicSpace n 2).starProjection (toH n
      (restrictContinuous (fun x => g x^k) ((seminorm_continuous n g).pow k)))=0 := by
  let f : C(Sphere n,ℝ) := restrictContinuous (fun x => g x^k) ((seminorm_continuous n g).pow k)
  let c := mean (fun u : Sphere n => g u^k)
  let v := toH n f-toH n (ContinuousMap.const (Sphere n) c)
  have ho : v∈(lowSpace n)ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨i,j⟩,rfl⟩ := hw
      rw [real_inner_comm,show v=toH n (f-ContinuousMap.const (Sphere n) c) by simp [v],inner_toH]
      change mean (fun u : Sphere n => (g u^k-c)*((u:Space n) i*(u:Space n) j))=0
      have hij := congrArg (fun A : Mat n => A (i,j)) hF
      change mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) j)/c-(if i=j then 1 else 0)/(n:ℝ)=0 at hij
      have hc : c≠0 := (mean_power_pos g hg k).ne'
      have hv := (div_eq_iff hc).mp (sub_eq_zero.mp hij)
      change _=0
      simp_rw [sub_mul]
      have hi : Integrable (fun u : Sphere n => g u^k*((u:Space n) i*(u:Space n) j)) (sigma n) :=
        continuous_integrable (((seminorm_continuous n g).comp continuous_subtype_val).pow k |>.mul
          (by fun_prop : Continuous (fun u : Sphere n => (u:Space n) i*(u:Space n) j)))
      have hi' : Integrable (fun u : Sphere n => c*((u:Space n) i*(u:Space n) j)) (sigma n) :=
        continuous_integrable (by fun_prop)
      rw [mean,integral_sub hi hi',integral_const_mul]
      change mean (fun u : Sphere n => g u^k*((u:Space n) i*(u:Space n) j))-c*mean (coordinateProduct n i j)=0
      rw [coordinateProduct_mean]
      have he : mean (fun u : Sphere n => g u^k*((u:Space n) i*(u:Space n) j))=
          mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) j) := by congr 1;funext u;ring
      rw [he,hv]; ring
    | zero => simp
    | add x y _ _ hx hy => simp only [inner_add_left,hx,hy,add_zero]
    | smul a x _ hx => simp only [inner_smul_left,conj_trivial,hx,mul_zero]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  intro w hw
  simp only [sub_zero]
  have hvol := (Submodule.mem_orthogonal _ _).mp ho w (harmonicSpace_two_le_lowSpace n hw)
  have hconst : ⟪toH n (ContinuousMap.const (Sphere n) c),w⟫=0 :=
    harmonic_inner_ne hn (d := 0) (by decide) (constant_mem_harmonicSpace_zero n c) hw
  change ⟪toH n f,w⟫=0
  dsimp only [v] at hvol
  have hconst' : ⟪w,toH n (ContinuousMap.const (Sphere n) c)⟫=0 :=
    (real_inner_comm _ _).trans hconst
  rw [inner_sub_right,hconst',sub_zero] at hvol
  exact (real_inner_comm _ _).trans hvol
end PettyProjection.Position
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection
namespace RelativeGauge
variable {n : ℕ} [NeZero n]

lemma exists_full_minimizer {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0 < cosineSeminorm μ hμ x) (b : Bool) :
    ∃ g : RelativeGauge (⊤ : Submodule ℝ (Space n)),IsMinimizer μ b g :=
  exists_minimizer hμ top_ne_bot (fun x _ hx => hq x hx) b

end RelativeGauge
end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.BilinearEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere mean sigma gaugeMoment)
namespace RelativeGauge
variable {n : ℕ} [NeZero n] {μ : Measure (Space n)}

omit [NeZero n] in
lemma scale_momentField (g : RelativeGauge (⊤ : Submodule ℝ (Space n)))
    {a : ℝ} (ha : 0<a) (k : ℕ) :
    Position.momentField (g.scale a ha).toSeminorm k=Position.momentField g.toSeminorm k := by
  apply WithLp.ofLp_injective
  funext ij
  change mean (fun u : Sphere n => (a*g u)^k*(u:Space n) ij.1*(u:Space n) ij.2)/
    mean (fun u : Sphere n => (a*g u)^k)-_=mean (fun u : Sphere n => g u^k*(u:Space n) ij.1*(u:Space n) ij.2)/
    mean (fun u : Sphere n => g u^k)-_
  have he : mean (fun u : Sphere n => (a*g u)^k*(u:Space n) ij.1*(u:Space n) ij.2)=
      a^k*mean (fun u : Sphere n => g u^k*(u:Space n) ij.1*(u:Space n) ij.2) := by
    simp_rw [mul_pow,mul_assoc]
    exact integral_const_mul _ _
  have he' : mean (fun u : Sphere n => (a*g u)^k)=a^k*mean (fun u : Sphere n => g u^k) := by
    simp only [mul_pow,mean,integral_const_mul]
  rw [he,he',mul_div_mul_left _ _ (pow_ne_zero _ ha.ne')]

lemma volumeNormalize_harmonic (hn : 2≤n) (g : RelativeGauge (⊤ : Submodule ℝ (Space n)))
    (hF : Position.momentField g.toSeminorm (Scalar.exponent n)=0) :
    (Spherical.harmonicSpace n 2).starProjection (Spherical.toH n
      (Spherical.restrictContinuous (fun x => g.volumeNormalize x^Scalar.exponent n)
        ((Spherical.seminorm_continuous n g.volumeNormalize.toSeminorm).pow _)))=0 := by
  apply Position.field_zero_harmonic hn _ (g.volumeNormalize.ne_zero top_ne_bot)
  rw [volumeNormalize,g.scale_momentField,hF]

lemma volumeNormalize_representation
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0<cosineSeminorm μ hμ x)
    (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) (hg : IsMinimizer μ (regime n) g) :
    ∃ s : ℝ,0<s ∧ Represents μ g.volumeNormalize.toSeminorm (Scalar.exponent n) s ∧
      supportFunctional μ g.volumeNormalize.body=s*gaugeMoment g.volumeNormalize.toSeminorm (Scalar.exponent n-1) := by
  have hm := Position.mean_power_pos g.volumeNormalize.toSeminorm (g.volumeNormalize.ne_zero top_ne_bot) (Scalar.exponent n-1)
  have hv := normalizedVolume_pos g.compact g.top_interior
  have hf : 0<supportFunctional μ g.volumeNormalize.body := by
    rw [volumeNormalize,g.functional_scale,hg.1,mul_one]
    exact inv_pos.mpr hv
  refine ⟨_,div_pos hf hm,scaled_represents hμ hq g hg.1 hg.2 hv,?_⟩
  exact (div_mul_cancel₀ _ hm.ne').symm

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere mean sigma gaugeMoment cosineConstant)
open RelativeGauge

lemma normalizedVolume_of_volume {n : ℕ} {K : Set (Space n)} (hK : volume.real K=kappa n) :
    normalizedVolume K=1 := by
  rw [normalizedVolume_formula,hK,div_self (kappa_pos n).ne',Real.one_rpow]

lemma cosine_equiv_pos {n : ℕ} {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    (T : Space n ≃L[ℝ] Space n) :
    ∀ x : Space n,x≠0 → 0< cosineSeminorm (μ.map T) (norm_integrable_map hμ T.toContinuousLinearMap) x := by
  intro x hx
  exact cosine_map_pos hμ hq T.toContinuousLinearMap x ⟨T.symm x,T.apply_symm_apply x⟩ hx

/-- The genuine bilinear inequality, with its global rigidity
consequence. The hypotheses are the support-functional bounds supplied by
Brunn--Minkowski, not the desired projection-volume conclusion. -/
theorem measure_bilinear_oai {n : ℕ} (hn : 4≤ n) [NeZero n] {μ ν : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hν : Integrable (fun x : Space n => ‖x‖) ν)
    (hqμ : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    (hqν : ∀ x : Space n,x≠0 → 0< cosineSeminorm ν hν x)
    (hbμ : ∀ M : Set (Space n),IsConvexBody M → normalizedVolume M≤ supportFunctional μ M)
    (hbν : ∀ M : Set (Space n),IsConvexBody M → normalizedVolume M≤ supportFunctional ν M) :
    cosineConstant n≤ measurePair μ ν ∧
      (measurePair μ ν=cosineConstant n →
        ∃ T : Space n ≃L[ℝ] Space n,supportFunctional μ (T '' unitBall n)=normalizedVolume (T '' unitBall n)) := by
  obtain ⟨T,hT,g,hg,hF⟩ := exists_symmetric_position hμ hqμ
  let μ' := μ.map T
  let ν' := ν.map T.symm
  have hiμ : Integrable (fun x : Space n => ‖x‖) μ' := norm_integrable_map hμ T.toContinuousLinearMap
  have hiν : Integrable (fun x : Space n => ‖x‖) ν' := norm_integrable_map hν T.symm.toContinuousLinearMap
  have hpμ : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ' hiμ x := cosine_equiv_pos hμ hqμ T
  have hpν : ∀ x : Space n,x≠0 → 0< cosineSeminorm ν' hiν x := cosine_equiv_pos hν hqν T.symm
  obtain ⟨f,hf⟩ := exists_full_minimizer hiν hpν (regime n)
  obtain ⟨s,hs,hsrep,hse⟩ := volumeNormalize_representation hiμ hpμ g hg
  obtain ⟨t,ht,htrep,hte⟩ := volumeNormalize_representation hiν hpν f hf
  let α := volumeFactor T
  have hα : 0<α := volumeFactor_pos T
  have hgbody : IsConvexBody g.volumeNormalize.body :=
    ⟨g.volumeNormalize.compact,g.volumeNormalize.convex,g.volumeNormalize.top_interior⟩
  have hfbody : IsConvexBody f.volumeNormalize.body :=
    ⟨f.volumeNormalize.compact,f.volumeNormalize.convex,f.volumeNormalize.top_interior⟩
  have hgs : α≤ supportFunctional μ' g.volumeNormalize.body := by
    have h := hbμ _ (linearEquiv_body T hgbody)
    rw [normalizedVolume_linearEquiv,normalizedVolume_of_volume g.volumeNormalize_body_volume,mul_one,
      ← functional_map_symmetric T hT hgbody.1 (hgbody.2.2.mono interior_subset)] at h
    exact h
  have hft : α⁻¹≤ supportFunctional ν' f.volumeNormalize.body := by
    have h := hbν _ (linearEquiv_body T.symm hfbody)
    rw [normalizedVolume_linearEquiv,normalizedVolume_of_volume f.volumeNormalize_body_volume,mul_one,
      volumeFactor_symm,← functional_map_symmetric T.symm (symmetric_equiv_symm T hT)
        hfbody.1 (hfbody.2.2.mono interior_subset)] at h
    exact h
  rw [hse] at hgs
  rw [hte] at hft
  have hsbound : 1≤(s/α)*gaugeMoment g.volumeNormalize.toSeminorm (Scalar.exponent n-1) := by
    rw [div_mul_eq_mul_div,le_div_iff₀ hα,one_mul]
    exact hgs
  have htbound : 1≤(t*α)*gaugeMoment f.volumeNormalize.toSeminorm (Scalar.exponent n-1) := by
    have hh := mul_le_mul_of_nonneg_left hft hα.le
    rw [mul_inv_cancel₀ hα.ne'] at hh
    nlinarith [hh]
  obtain ⟨hlow,heq⟩ := Spherical.normalized_norm_pair hn g.volumeNormalize.toSeminorm
    f.volumeNormalize.toSeminorm g.volumeNormalize.top_pos f.volumeNormalize.top_pos
    g.volumeNormalize_moment f.volumeNormalize_moment (g.volumeNormalize_harmonic (by omega) hF)
    (div_pos hs hα) (mul_pos ht hα) hsbound htbound
  have hsprod : (s/α)*(t*α)=s*t := by field_simp
  rw [hsprod] at hlow heq
  have hpair := represents_pair hiν g.volumeNormalize.toSeminorm f.volumeNormalize.toSeminorm
    (exponent_pos n) hsrep htrep
  have hPinv : measurePair μ' ν'=measurePair μ ν := measurePair_map_symmetric hν T hT
  rw [hPinv] at hpair
  refine ⟨hpair.symm ▸ hlow,?_⟩
  intro h
  obtain ⟨hg1,_,hs1,_⟩ := heq (hpair.symm.trans h)
  have hbody : g.volumeNormalize.body=unitBall n := full_body_of_sphere_one _ hg1
  have hmoment : gaugeMoment g.volumeNormalize.toSeminorm (Scalar.exponent n-1)=1 := by
    simp only [gaugeMoment]
    simp_rw [hg1,one_pow]
    exact Spherical.mean_const n 1
  have hsα : s=α := (div_eq_one_iff_eq hα.ne').mp hs1
  rw [hbody,hmoment,mul_one,hsα] at hse
  refine ⟨T,?_⟩
  have hball : IsConvexBody (unitBall n) := hbody ▸ hgbody
  rw [← functional_map_symmetric T hT hball.1 (hball.2.2.mono interior_subset),
    hse,normalizedVolume_linearEquiv,normalizedVolume_of_volume (K := unitBall n) rfl,mul_one]

end PettyProjection
end

end OAI
end

theorem solution : type_of% @OAI.PettyProjection.measure_bilinear_oai := @OAI.PettyProjection.measure_bilinear_oai
