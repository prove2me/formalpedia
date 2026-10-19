-- Prove2me | solution 1 for OAI.FiniteEntropySeparation.gaussian_poincare_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:18:05.848553+00:00
-- url     : https://prove2.me/submissions/98e70322-e977-4cca-939e-b0e4e5a31156

import Mathlib
import Definitions.Def_OAIQWFE002
import Theorems.Thm_HighDimProb_RandomProcesses_gaussian_integration_by_parts
import Theorems.Thm_OAI_FiniteEntropySeparation_hermite_orthogonality

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianIBP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ENNReal NNReal Polynomial
open MeasureTheory ProbabilityTheory Filter
namespace FiniteEntropySeparation

 theorem gaussian_integrationByParts {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hi : Integrable f (gaussianReal μ v)) (hi' : Integrable f' (gaussianReal μ v))
    (hx : Integrable (fun x => (x-μ)*f x) (gaussianReal μ v)) :
    (∫ x, (x-μ)*f x ∂gaussianReal μ v) = (v : ℝ) * ∫ x, f' x ∂gaussianReal μ v := by
  -- from the published standard-Gaussian Stein identity
  -- HighDimProb.RandomProcesses.gaussian_integration_by_parts, by x = μ + √v y
  set s : ℝ := Real.sqrt v with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast pos_iff_ne_zero.mpr hv)
  have hss : s * s = v := Real.mul_self_sqrt (NNReal.coe_nonneg v)
  let T : ℝ → ℝ := fun y => μ + s * y
  have hT : Measurable T := by fun_prop
  have hmap : (gaussianReal 0 1).map T = gaussianReal μ v := by
    have h1 := gaussianReal_map_const_mul (μ := (0:ℝ)) (v := 1) s
    rw [show T = (fun x => x + μ) ∘ (fun y => s * y) by funext y; simp [T, add_comm]]
    rw [← Measure.map_map (by fun_prop) (by fun_prop), h1, gaussianReal_map_add_const]
    congr 1
    · ring
    · ext; simp [sq, hss]
  have hint (g : ℝ → ℝ) (hg : AEStronglyMeasurable g (gaussianReal μ v)) :
      Integrable g (gaussianReal μ v) ↔ Integrable (g ∘ T) (gaussianReal 0 1) := by
    rw [← hmap]; exact integrable_map_measure (hmap ▸ hg) hT.aemeasurable
  have hcomp (g : ℝ → ℝ) (hg : AEStronglyMeasurable g (gaussianReal μ v)) :
      ∫ x, g x ∂gaussianReal μ v = ∫ y, g (T y) ∂gaussianReal 0 1 := by
    rw [← hmap]; exact integral_map hT.aemeasurable (hmap ▸ hg)
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hm1 : AEStronglyMeasurable f (gaussianReal μ v) := hfc.aestronglyMeasurable
  have hm2 : AEStronglyMeasurable f' (gaussianReal μ v) := hi'.aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (fun x => (x-μ)*f x) (gaussianReal μ v) := hx.aestronglyMeasurable
  have h := HighDimProb.RandomProcesses.gaussian_integration_by_parts (f := fun y => f (T y))
    (f' := fun y => s * f' (T y))
    (fun y => by
      have := (hf (T y)).comp y (((hasDerivAt_id y).const_mul s).const_add μ)
      exact this.congr_deriv (by simp only [T, id]; ring))
    ((hint f hm1).mp hi) (((hint f' hm2).mp hi').const_mul s)
    (by
      have := ((hint _ hm3).mp hx).const_mul s⁻¹
      refine this.congr (ae_of_all _ fun y => ?_)
      simp only [Function.comp, T, add_sub_cancel_left]
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hs0.ne', one_mul])
  rw [integral_const_mul] at h
  rw [hcomp _ hm3, hcomp _ hm2]
  have he : ∫ y, (T y - μ) * f (T y) ∂gaussianReal 0 1 =
      s * ∫ y, y * f (T y) ∂gaussianReal 0 1 := by
    rw [← integral_const_mul]; congr 1; funext y; simp only [T]; ring
  rw [he, ← h, ← mul_assoc, hss]
 theorem gaussian_pow_integrable (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x^n) (gaussianReal μ v) := by
  by_cases hn : n = 0
  · subst n; simp
  have h := (memLp_id_gaussianReal' (μ := μ) (v := v) (n : ℝ≥0∞) (by simp)).integrable_norm_pow hn
  apply h.mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun x => by simp [norm_pow])
 theorem gaussian_polynomial_integrable (μ : ℝ) (v : ℝ≥0) (P : ℝ[X]) :
    Integrable (fun x => P.eval x) (gaussianReal μ v) := by
  classical
  simp only [Polynomial.eval_eq_sum_range]
  exact integrable_finsetSum _ (fun i _ => (gaussian_pow_integrable μ v i).const_mul _)
 theorem gaussian_polynomial_stein (P : ℝ[X]) :
    (∫ x, x*P.eval x ∂gaussianReal 0 1) = ∫ x, P.derivative.eval x ∂gaussianReal 0 1 := by
  have hi := gaussian_polynomial_integrable 0 1 (Polynomial.X * P)
  simpa only [sub_zero, NNReal.coe_one, one_mul] using gaussian_integrationByParts (by norm_num : (1 : ℝ≥0) ≠ 0)
    (fun x => P.hasDerivAt x) (gaussian_polynomial_integrable 0 1 P)
    (gaussian_polynomial_integrable 0 1 P.derivative) (by simpa using hi)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianHermite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Polynomial
open MeasureTheory ProbabilityTheory Polynomial Finset
namespace FiniteEntropySeparation
 theorem realHermite_succ (n : ℕ) : realHermite (n+1) = X * realHermite n - (realHermite n).derivative := by
  simp [realHermite, Polynomial.hermite_succ, Polynomial.derivative_map]
 theorem realHermite_derivative (n : ℕ) : (realHermite (n+1)).derivative = (n+1 : ℝ) • realHermite n := by
  induction n with
  | zero => simp [realHermite_succ]
  | succ n ih =>
    rw [realHermite_succ (n+1), derivative_sub, derivative_mul, derivative_X, one_mul, ih,
      derivative_smul, mul_smul_comm]
    calc
      _ = realHermite (n+1) + (n+1 : ℝ) • (X * realHermite n - (realHermite n).derivative) := by module
      _ = _ := by rw [← realHermite_succ]; push_cast; module
 theorem gaussianPolyIntegral_add (P Q : ℝ[X]) :
    gaussianPolyIntegral (P+Q) = gaussianPolyIntegral P + gaussianPolyIntegral Q := by
  simp only [gaussianPolyIntegral, eval_add]
  exact integral_add (gaussian_polynomial_integrable _ _ _) (gaussian_polynomial_integrable _ _ _)
 theorem gaussianPolyIntegral_sub (P Q : ℝ[X]) :
    gaussianPolyIntegral (P-Q) = gaussianPolyIntegral P - gaussianPolyIntegral Q := by
  simp only [gaussianPolyIntegral, eval_sub]
  exact integral_sub (gaussian_polynomial_integrable _ _ _) (gaussian_polynomial_integrable _ _ _)
 theorem gaussianPolyIntegral_smul (r : ℝ) (P : ℝ[X]) :
    gaussianPolyIntegral (r • P) = r * gaussianPolyIntegral P := by
  simp [gaussianPolyIntegral, eval_smul, integral_const_mul]
 theorem hermite_raising_lowering (n : ℕ) (Q : ℝ[X]) :
    gaussianPolyIntegral (realHermite (n+1) * Q) = gaussianPolyIntegral (realHermite n * Q.derivative) := by
  have hs := gaussian_polynomial_stein (realHermite n * Q)
  have hstein : gaussianPolyIntegral (X * (realHermite n * Q)) =
      gaussianPolyIntegral ((realHermite n * Q).derivative) := by
    simpa only [gaussianPolyIntegral, eval_mul, eval_X] using hs
  rw [realHermite_succ, sub_mul, gaussianPolyIntegral_sub, mul_assoc, hstein,
    derivative_mul, gaussianPolyIntegral_add]
  ring
 theorem realHermite_mean (n : ℕ) : gaussianPolyIntegral (realHermite n) = if n=0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n => simpa using hermite_raising_lowering n 1
 theorem realHermite_inner (n m : ℕ) :
    gaussianPolyIntegral (realHermite n * realHermite m) = if n=m then (n.factorial : ℝ) else 0 :=
  hermite_orthogonality n m
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorHermite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open scoped Polynomial
open MeasureTheory ProbabilityTheory Polynomial Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
theorem tensorHermite_integrable [DecidableEq ι] (a : ι → ℕ) : Integrable (tensorHermite a) (productGaussian ι) :=
  Integrable.fintype_prod (fun i => gaussian_polynomial_integrable 0 1 (realHermite (a i)))
theorem tensorHermite_mul_integrable [DecidableEq ι] (a b : ι → ℕ) :
    Integrable (fun x => tensorHermite a x * tensorHermite b x) (productGaussian ι) := by
  have h := Integrable.fintype_prod (fun i => gaussian_polynomial_integrable 0 1
    (realHermite (a i) * realHermite (b i)))
  simpa only [eval_mul, prod_mul_distrib, tensorHermite, productGaussian] using h
 theorem tensorHermite_mean [DecidableEq ι] (a : ι → ℕ) :
    (∫ x, tensorHermite a x ∂productGaussian ι) = if a=0 then 1 else 0 := by
  classical
  unfold tensorHermite productGaussian
  rw [integral_fintype_prod_eq_prod (fun i t => (realHermite (a i)).eval t)]
  change (∏ i, gaussianPolyIntegral (realHermite (a i))) = _
  simp_rw [realHermite_mean]
  by_cases ha : a=0
  · subst a; simp
  · rw [ite_eq_right ha]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by simpa only [funext_iff, Pi.zero_apply, not_forall] using ha
    apply prod_eq_zero (mem_univ i)
    simp [hi]
 theorem tensorHermite_inner [DecidableEq ι] (a b : ι → ℕ) :
    (∫ x, tensorHermite a x*tensorHermite b x ∂productGaussian ι) =
      if a=b then tensorWeight a else 0 := by
  classical
  simp only [tensorHermite, ← prod_mul_distrib]
  rw [productGaussian, integral_fintype_prod_eq_prod
    (fun i t => (realHermite (a i)).eval t * (realHermite (b i)).eval t)]
  simp only [← eval_mul]
  change (∏ i, gaussianPolyIntegral (realHermite (a i)*realHermite (b i))) = _
  simp_rw [realHermite_inner]
  by_cases ha : a=b
  · subst b; simp [tensorWeight]
  · rw [ite_eq_right ha]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by simpa only [funext_iff, not_forall] using ha
    apply prod_eq_zero (mem_univ i)
    simp [hi]
 theorem tensorWeight_pos [DecidableEq ι] (a : ι → ℕ) : 0 < tensorWeight a := by
  unfold tensorWeight
  exact prod_pos (fun i _ => by exact_mod_cast Nat.factorial_pos (a i))
 theorem tensorHermite_update [DecidableEq ι] (a : ι → ℕ) (i : ι) (k : ℕ) (x : ι → ℝ) :
    tensorHermite (Function.update a i k) x = (realHermite k).eval (x i) *
      ∏ j ∈ univ.erase i, (realHermite (a j)).eval (x j) := by
  classical
  rw [tensorHermite, ← mul_prod_erase _ _ (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (ne_of_mem_erase hj)]
 theorem tensorHermite_mul_coord [DecidableEq ι] (a : ι → ℕ) (i : ι) (x : ι → ℝ) :
    x i * tensorHermite a x = tensorHermite (Function.update a i (a i+1)) x +
      (a i : ℝ) * tensorHermite (Function.update a i (a i-1)) x := by
  classical
  have he : tensorHermite a x = (realHermite (a i)).eval (x i) *
      ∏ j ∈ univ.erase i, (realHermite (a j)).eval (x j) := by
    simpa only [Function.update_eq_self] using tensorHermite_update a i (a i) x
  rw [he, tensorHermite_update, tensorHermite_update]
  have hr : x i * (realHermite (a i)).eval (x i) =
      (realHermite (a i+1)).eval (x i) + (a i : ℝ)*(realHermite (a i-1)).eval (x i) := by
    cases h : a i with
    | zero => simp [realHermite_succ]
    | succ n =>
      rw [realHermite_succ (n+1), realHermite_derivative]
      simp only [eval_sub, eval_mul, eval_X, eval_smul, smul_eq_mul, Nat.add_sub_cancel]
      push_cast
      ring
  rw [← mul_assoc, hr]
  ring
 theorem tensorHermite_mem [DecidableEq ι] (a : ι → ℕ) : tensorHermite a ∈ tensorHermiteSpan :=
  Submodule.subset_span ⟨a,rfl⟩
 theorem tensorHermiteSpan_coord [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : f ∈ tensorHermiteSpan) (i : ι) :
    (fun x => x i*f x) ∈ tensorHermiteSpan := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a,rfl⟩ := hf
    have hfun : (fun x => x i*tensorHermite a x) =
      tensorHermite (Function.update a i (a i+1)) + (a i : ℝ) • tensorHermite (Function.update a i (a i-1)) := by
      funext x; exact tensorHermite_mul_coord a i x
    rw [hfun]
    exact Submodule.add_mem _ (tensorHermite_mem _) (Submodule.smul_mem _ _ (tensorHermite_mem _))
  | zero =>
    convert (Submodule.zero_mem tensorHermiteSpan) using 1
    funext x; simp
  | add f g hf hg ihf ihg =>
    convert Submodule.add_mem tensorHermiteSpan ihf ihg using 1
    funext x; simp [mul_add]
  | smul r f hf ih =>
    convert Submodule.smul_mem tensorHermiteSpan r ih using 1
    funext x; simp [mul_left_comm]
 theorem mvPolynomial_hermite_span [DecidableEq ι] (P : MvPolynomial ι ℝ) :
    (fun x => MvPolynomial.eval x P) ∈ tensorHermiteSpan := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    have he : (fun x : ι → ℝ => MvPolynomial.eval x (MvPolynomial.C r)) = r • tensorHermite (fun _ => 0) := by
      ext x; simp
    rw [he]; exact Submodule.smul_mem _ r (tensorHermite_mem _)
  | add P Q hP hQ =>
    convert Submodule.add_mem tensorHermiteSpan hP hQ using 1
    funext x; simp
  | mul_X P i hP => simpa only [map_mul, MvPolynomial.eval_X, mul_comm] using tensorHermiteSpan_coord hP i
 theorem mvPolynomial_hermite_expansion [DecidableEq ι] (P : MvPolynomial ι ℝ) :
    ∃ a : (ι → ℕ) →₀ ℝ, (fun x => MvPolynomial.eval x P) = a.sum (fun k r => r • tensorHermite k) := by
  obtain ⟨a,ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (mvPolynomial_hermite_span P)
  exact ⟨a,ha.symm⟩
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped Polynomial
open MeasureTheory ProbabilityTheory Polynomial Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 theorem realHermite_derivative_inner (n m : ℕ) :
    gaussianPolyIntegral ((realHermite n).derivative * (realHermite m).derivative) =
      (n : ℝ)*gaussianPolyIntegral (realHermite n*realHermite m) := by
  cases n with
  | zero => simp
  | succ n =>
    cases m with
    | zero => simp [realHermite_mean]
    | succ m =>
      rw [realHermite_derivative, realHermite_derivative, smul_mul_smul_comm,
        gaussianPolyIntegral_smul, realHermite_inner, realHermite_inner]
      by_cases h : n=m
      · subst m; simp [Nat.factorial_succ]; ring
      · simp [h]
 theorem tensorGradient_erase (a : ι → ℕ) (i : ι) (x : ι → ℝ) :
    tensorGradient a i x = (realHermite (a i)).derivative.eval (x i) *
      ∏ j ∈ univ.erase i, (realHermite (a j)).eval (x j) := by
  rw [tensorGradient, ← mul_prod_erase _ _ (mem_univ i)]
  simp only []
  congr 1
  apply prod_congr rfl
  intro j hj
  rw [ite_eq_right (ne_of_mem_erase hj)]
 theorem tensorHermite_section (a : ι → ℕ) (i : ι) (x : ι → ℝ) :
    (fun t => tensorHermite a (Function.update x i t)) =
      fun t => (realHermite (a i)).eval t * ∏ j ∈ univ.erase i, (realHermite (a j)).eval (x j) := by
  funext t
  rw [tensorHermite, ← mul_prod_erase _ _ (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (ne_of_mem_erase hj)]
 theorem tensorHermite_hasDerivAt (a : ι → ℕ) (i : ι) (x : ι → ℝ) :
    HasDerivAt (fun t => tensorHermite a (Function.update x i t)) (tensorGradient a i x) (x i) := by
  rw [tensorHermite_section, tensorGradient_erase]
  exact ((realHermite (a i)).hasDerivAt (x i)).mul_const _
 theorem tensorGradient_mul_integrable (a b : ι → ℕ) (i : ι) :
    Integrable (fun x => tensorGradient a i x * tensorGradient b i x) (productGaussian ι) := by
  have h := Integrable.fintype_prod (fun j => gaussian_polynomial_integrable 0 1
    ((if j=i then (realHermite (a j)).derivative else realHermite (a j)) *
      (if j=i then (realHermite (b j)).derivative else realHermite (b j))))
  simpa only [eval_mul, prod_mul_distrib, tensorGradient, productGaussian] using h
 theorem tensorGradient_inner (a b : ι → ℕ) (i : ι) :
    (∫ x, tensorGradient a i x*tensorGradient b i x ∂productGaussian ι) =
      if a=b then (a i : ℝ)*tensorWeight a else 0 := by
  have he : (∫ x, tensorGradient a i x*tensorGradient b i x ∂productGaussian ι) =
      (a i : ℝ) * ∫ x, tensorHermite a x*tensorHermite b x ∂productGaussian ι := by
    simp only [tensorGradient, tensorHermite, ← prod_mul_distrib, productGaussian]
    rw [integral_fintype_prod_eq_prod
      (fun j t => (if j=i then (realHermite (a j)).derivative else realHermite (a j)).eval t *
        (if j=i then (realHermite (b j)).derivative else realHermite (b j)).eval t),
      integral_fintype_prod_eq_prod
      (fun j t => (realHermite (a j)).eval t * (realHermite (b j)).eval t)]
    simp only [← eval_mul]
    change (∏ j, gaussianPolyIntegral ((if j=i then (realHermite (a j)).derivative else realHermite (a j)) *
      (if j=i then (realHermite (b j)).derivative else realHermite (b j)))) =
      (a i : ℝ) * ∏ j, gaussianPolyIntegral (realHermite (a j)*realHermite (b j))
    rw [← mul_prod_erase _ _ (mem_univ i), ← mul_prod_erase univ (fun j => gaussianPolyIntegral (realHermite (a j)*realHermite (b j))) (mem_univ i)]
    simp only [ite_true, realHermite_derivative_inner, mul_assoc]
    congr 2
    apply prod_congr rfl
    intro j hj
    simp only [ite_eq_right (ne_of_mem_erase hj)]
  rw [he, tensorHermite_inner]
  split_ifs <;> simp
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.OrthogonalExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory Finset
namespace FiniteEntropySeparation
variable {κ : Type u1} {Ω : Type u2} [MeasurableSpace Ω]
 theorem linearExpand_apply {κ : Type u1} {Ω : Type u2} [MeasurableSpace Ω] (g : κ → Ω → ℝ) (a : κ →₀ ℝ) (x : Ω) :
    linearExpand g a x = ∑ k ∈ a.support, a k*g k x := by
  simp [linearExpand, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
 theorem linearExpand_integrable {μ : Measure Ω} {g : κ → Ω → ℝ}
    (hg : ∀ k, Integrable (g k) μ) (a : κ →₀ ℝ) : Integrable (linearExpand g a) μ := by
  change Integrable (fun x => linearExpand g a x) μ
  simp only [linearExpand_apply]
  exact integrable_finsetSum _ (fun k _ => (hg k).const_mul (a k))
 theorem linearExpand_mul_integrable {μ : Measure Ω} {g h : κ → Ω → ℝ}
    (hgh : ∀ k l, Integrable (fun x => g k x*h l x) μ) (a b : κ →₀ ℝ) :
    Integrable (fun x => linearExpand g a x*linearExpand h b x) μ := by
  simp only [linearExpand_apply, sum_mul, mul_sum]
  apply integrable_finsetSum
  intro k hk
  apply integrable_finsetSum
  intro l hl
  convert (hgh l k).const_mul (a l*b k) using 1 ; try rfl
  funext x; ring
 theorem linearExpand_integral {μ : Measure Ω} {g : κ → Ω → ℝ}
    (hg : ∀ k, Integrable (g k) μ) (a : κ →₀ ℝ) :
    (∫ x, linearExpand g a x ∂μ) = ∑ k ∈ a.support, a k*∫ x, g k x ∂μ := by
  simp only [linearExpand_apply]
  rw [integral_finsetSum _ (fun k _ => (hg k).const_mul (a k))]
  simp only [integral_const_mul]
 theorem linearExpand_inner {μ : Measure Ω} {g h : κ → Ω → ℝ}
    (hgh : ∀ k l, Integrable (fun x => g k x*h l x) μ) (a b : κ →₀ ℝ) :
    (∫ x, linearExpand g a x*linearExpand h b x ∂μ) =
      ∑ k ∈ a.support, ∑ l ∈ b.support, a k*b l*∫ x, g k x*h l x ∂μ := by
  have he : (fun x => linearExpand g a x*linearExpand h b x) =
      fun x => ∑ k ∈ a.support, ∑ l ∈ b.support, (a k*b l)*(g k x*h l x) := by
    funext x
    simp only [linearExpand_apply, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro k hk
    apply sum_congr rfl
    intro l hl
    ring
  rw [he, integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => (hgh k l).const_mul _))]
  apply sum_congr rfl
  intro k hk
  rw [integral_finsetSum _ (fun l _ => (hgh k l).const_mul _)]
  simp only [integral_const_mul]
 theorem linearExpand_orthogonal [DecidableEq κ] {μ : Measure Ω} {g h : κ → Ω → ℝ}
    (hgh : ∀ k l, Integrable (fun x => g k x*h l x) μ) (w : κ → ℝ)
    (horth : ∀ k l, (∫ x, g k x*h l x ∂μ) = if k=l then w k else 0)
    (a b : κ →₀ ℝ) :
    (∫ x, linearExpand g a x*linearExpand h b x ∂μ) =
      ∑ k ∈ a.support, a k*b k*w k := by
  classical
  rw [linearExpand_inner hgh]
  apply sum_congr rfl
  intro k hk
  simp_rw [horth]
  by_cases hkb : k ∈ b.support
  · rw [sum_eq_single k]
    · simp
    · intro l hl hlk; simp [Ne.symm hlk]
    · exact fun h => (h hkb).elim
  · have hb : b k=0 := Finsupp.notMem_support_iff.mp hkb
    rw [hb, mul_zero, zero_mul]
    apply sum_eq_zero
    intro l hl
    have hkl : k ≠ l := fun h => hkb (h.symm ▸ hl)
    simp [hkl]
 theorem integral_center_sq {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hfsq : Integrable (fun x => f x*f x) μ) :
    (∫ x, (f x-∫ y, f y ∂μ)^2 ∂μ) = (∫ x, f x*f x ∂μ) - (∫ x, f x ∂μ)^2 := by
  let m := ∫ x, f x ∂μ
  have he : (fun x => (f x-m)^2) = fun x => f x*f x - (2*m)*f x + m^2 := by
    funext x; ring
  change (∫ x, (f x-m)^2 ∂μ) = _
  rw [he]
  have ha : (∫ x, f x*f x - (2*m)*f x + m^2 ∂μ) =
      (∫ x, f x*f x - (2*m)*f x ∂μ) + ∫ x, m^2 ∂μ :=
    integral_add (hfsq.sub (hf.const_mul (2*m))) (integrable_const _)
  have hs : (∫ x, f x*f x - (2*m)*f x ∂μ) =
      (∫ x, f x*f x ∂μ) - ∫ x, (2*m)*f x ∂μ := integral_sub hfsq (hf.const_mul _)
  rw [ha, hs, integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  dsimp [m]; ring
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 theorem tensorExpansion_hasDerivAt (a : (ι → ℕ) →₀ ℝ) (i : ι) (x : ι → ℝ) :
    HasDerivAt (fun t => linearExpand tensorHermite a (Function.update x i t))
      (linearExpand (fun k => tensorGradient k i) a x) (x i) := by
  simp only [linearExpand_apply]
  exact HasDerivAt.fun_sum (fun k _ => (tensorHermite_hasDerivAt k i x).const_mul (a k))
 theorem tensorExpansion_derivative (a : (ι → ℕ) →₀ ℝ) (i : ι) :
    coordinateDerivative (linearExpand tensorHermite a) i = linearExpand (fun k => tensorGradient k i) a := by
  funext x
  exact (tensorExpansion_hasDerivAt a i x).deriv
 theorem tensorExpansion_mean (a : (ι → ℕ) →₀ ℝ) :
    (∫ x, linearExpand tensorHermite a x ∂productGaussian ι) = a 0 := by
  rw [linearExpand_integral tensorHermite_integrable]
  simp_rw [tensorHermite_mean]
  simp_all
 theorem tensorExpansion_energy (a : (ι → ℕ) →₀ ℝ) (i : ι) :
    (∫ x, (coordinateDerivative (linearExpand tensorHermite a) i x)^2 ∂productGaussian ι) =
      ∑ k ∈ a.support, (k i : ℝ)*(a k)^2*tensorWeight k := by
  rw [tensorExpansion_derivative]
  simp only [pow_two]
  rw [linearExpand_orthogonal (fun k l => tensorGradient_mul_integrable k l i)
    (fun k => (k i : ℝ)*tensorWeight k) (fun k l => tensorGradient_inner k l i)]
  apply sum_congr rfl
  intro k hk
  ring
 theorem tensorExpansion_variance (a : (ι → ℕ) →₀ ℝ) :
    (∫ x, (linearExpand tensorHermite a x - ∫ y, linearExpand tensorHermite a y ∂productGaussian ι)^2
      ∂productGaussian ι) = (∑ k ∈ a.support, (a k)^2*tensorWeight k) - (a 0)^2 := by
  rw [integral_center_sq (linearExpand_integrable tensorHermite_integrable _)
    (linearExpand_mul_integrable tensorHermite_mul_integrable _ _),
    linearExpand_orthogonal tensorHermite_mul_integrable tensorWeight tensorHermite_inner,
    tensorExpansion_mean]
  simp only [pow_two]
 theorem tensorDegree_ge_one {ι : Type u1} [Fintype ι] [DecidableEq ι] {k : ι → ℕ} (hk : k ≠ 0) : (1 : ℝ) ≤ ∑ i, (k i : ℝ) := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    apply hk
    funext i
    by_contra hi
    exact h ⟨i,hi⟩
  calc
    (1 : ℝ) ≤ k i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
    _ ≤ ∑ j, (k j : ℝ) := single_le_sum (f := fun j => (k j : ℝ)) (fun j _ => by positivity) (mem_univ i)
 theorem tensorExpansion_poincare (a : (ι → ℕ) →₀ ℝ) :
    (∫ x, (linearExpand tensorHermite a x - ∫ y, linearExpand tensorHermite a y ∂productGaussian ι)^2
      ∂productGaussian ι) ≤
      ∑ i, ∫ x, (coordinateDerivative (linearExpand tensorHermite a) i x)^2 ∂productGaussian ι := by
  classical
  rw [tensorExpansion_variance]
  simp_rw [tensorExpansion_energy]
  rw [sum_comm]
  have hz : (a 0)^2 = ∑ k ∈ a.support, if k=0 then (a k)^2 else 0 := by simp
  rw [hz, ← sum_sub_distrib]
  apply sum_le_sum
  intro k hk
  by_cases hk0 : k=0
  · subst k; simp [tensorWeight]
  · rw [ite_eq_right hk0, sub_zero]
    simp only [← sum_mul]
    have hd := tensorDegree_ge_one hk0
    have hw : 0 ≤ (a k)^2*tensorWeight k := mul_nonneg (sq_nonneg _) (tensorWeight_pos k).le
    nlinarith

 theorem gaussian_mvPolynomial_poincare_core (P : MvPolynomial ι ℝ) :
    (∫ x, (MvPolynomial.eval x P - ∫ y, MvPolynomial.eval y P ∂productGaussian ι)^2 ∂productGaussian ι) ≤
      ∑ i, ∫ x, (coordinateDerivative (fun y => MvPolynomial.eval y P) i x)^2 ∂productGaussian ι := by
  obtain ⟨a,ha⟩ := mvPolynomial_hermite_expansion P
  change (fun x => MvPolynomial.eval x P) = linearExpand tensorHermite a at ha
  simpa only [← ha] using tensorExpansion_poincare a
 theorem gaussian_poincare_mvPolynomial_oai (P : MvPolynomial ι ℝ) :
    (∫ x, (MvPolynomial.eval x P -
        ∫ y, MvPolynomial.eval y P ∂Measure.pi (fun _ : ι => gaussianReal 0 1))^2
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) ≤
      ∑ i, ∫ x, (deriv (fun t => MvPolynomial.eval (Function.update x i t) P) (x i))^2
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) :=
  gaussian_mvPolynomial_poincare_core P
end FiniteEntropySeparation

end

end OAI
end

theorem solution.{u1} : type_of% @OAI.FiniteEntropySeparation.gaussian_poincare_mvPolynomial_oai.{u1} := @OAI.FiniteEntropySeparation.gaussian_poincare_mvPolynomial_oai.{u1}
