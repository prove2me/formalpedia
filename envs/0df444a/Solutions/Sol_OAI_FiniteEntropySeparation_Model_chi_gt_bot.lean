-- Prove2me | solution 1 for OAI.FiniteEntropySeparation.Model.chi_gt_bot
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:12:44.075993+00:00
-- url     : https://prove2.me/submissions/e09be6c7-4b45-4f64-a4a5-665777c42531

import Mathlib
import Definitions.Def_FiniteEntropySeparation
import Definitions.Def_OAIQWFE002
import Theorems.Thm_HighDimProb_RandomProcesses_gaussian_integration_by_parts
import Theorems.Thm_OAI_FiniteEntropySeparation_gaussian_poincare_mvPolynomial

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter

namespace FiniteEntropySeparation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem trace_add {M : VonNeumannAlgebra H} (τ : TracialVector M)
    (A B : H →L[ℂ] H) : trace τ (A + B) = trace τ A + trace τ B := by
  simp [trace]

 theorem trace_smul {M : VonNeumannAlgebra H} (τ : TracialVector M)
    (z : ℂ) (A : H →L[ℂ] H) : trace τ (z • A) = z * trace τ A := by
  simp [trace]

 theorem trace_sum {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {α : Type u1} (s : Finset α) (A : α → H →L[ℂ] H) :
    trace τ (∑ a ∈ s, A a) = ∑ a ∈ s, trace τ (A a) := by
  simp [trace]

omit [CompleteSpace H] in
 theorem commutatorKernel_cons {n : ℕ} (P : H →L[ℂ] H)
    (X : Fin n → H →L[ℂ] H) (i j : Fin n) (w : List (Fin n)) :
    commutatorKernel P X i (j :: w) =
      (if j = i then P * wordEval X w else 0) + X j * commutatorKernel P X i w := by
  simp only [commutatorKernel, List.length_cons, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
    List.take_zero, List.take_succ_cons, List.drop_succ_cons, Nat.zero_add,
    wordEval, List.map_nil, List.prod_nil, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [List.map_cons, List.prod_cons, mul_assoc]

omit [CompleteSpace H] in
 theorem commutator_word {n : ℕ} (P a : H →L[ℂ] H) (X : Fin n → H →L[ℂ] H)
    (i : Fin n) (c : ℂ)
    (h : ∀ j, a * X j = X j * a + if j = i then c • P else 0)
    (w : List (Fin n)) :
    a * wordEval X w = wordEval X w * a + c • commutatorKernel P X i w := by
  induction w with
  | nil => simp [wordEval]
  | cons j w ih =>
    have hw : wordEval X (j :: w) = X j * wordEval X w := by simp [wordEval]
    rw [hw, commutatorKernel_cons, ← mul_assoc, h, add_mul, mul_assoc, ih]
    by_cases hji : j = i <;>
      simp [hji, mul_add, mul_assoc, smul_add, _root_.add_assoc, _root_.add_comm,
        _root_.add_left_comm]

 theorem trace_vacuumRankOne_product {M : VonNeumannAlgebra H} (τ : TracialVector M)
    (A B : H →L[ℂ] H) : trace τ (A * vacuumRankOne τ * B) = trace τ A * trace τ B := by
  simp only [trace, vacuumRankOne, mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
    map_smul, inner_smul_right]
  exact mul_comm _ _

 theorem trace_commutatorKernel {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (i : Fin n) (w : List (Fin n)) :
    trace τ (commutatorKernel (vacuumRankOne τ) X i w) = derivativeMoment τ X i w := by
  rw [commutatorKernel, trace_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [trace_vacuumRankOne_product, wordMoment]

theorem commutator_integration_by_parts {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (a : H →L[ℂ] H) (i : Fin n) (c : ℂ)
    (h : ∀ j, a * X j = X j * a + if j = i then c • vacuumRankOne τ else 0)
    (hz : a τ.vacuum = 0) (w : List (Fin n)) :
    inner ℂ (star a τ.vacuum) (wordEval X w τ.vacuum) = c * derivativeMoment τ X i w := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  change trace τ (a * wordEval X w) = _
  rw [commutator_word _ _ _ _ _ h, trace_add, trace_smul, trace_commutatorKernel]
  have hzero : trace τ (wordEval X w * a) = 0 := by
    simp [trace, mul_apply_eq_comp, hz]
  rw [hzero, zero_add]

namespace Fock

open scoped lp
variable {ι : Type} [DecidableEq ι]

 theorem creation_commutes_rightCreation (i j : ι) :
    Commute (creation i) (rightCreation j) := by
  show creation i * rightCreation j = rightCreation j * creation i
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change creation i (rightCreation j (lp.single 2 w z)) =
    rightCreation j (creation i (lp.single 2 w z))
  simp

 theorem rightAnnihilation_creation (i j : ι) :
    star (rightCreation i) * creation j = creation j * star (rightCreation i) +
      if i = j then vacuumProjection else 0 := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change star (rightCreation i) (creation j (lp.single 2 w z)) =
    creation j (star (rightCreation i) (lp.single 2 w z)) +
      (if i = j then vacuumProjection else 0) (lp.single 2 w z)
  induction w using List.reverseRecOn with
  | nil =>
    rw [creation_single, show [j] = [] ++ [j] from rfl, rightAnnihilation_single_append]
    by_cases h : i = j <;> simp [h]
  | append_singleton w k _ =>
    rw [creation_single, show j :: (w ++ [k]) = (j :: w) ++ [k] from rfl,
      rightAnnihilation_single_append]
    have hp : (if i = j then vacuumProjection else 0) (lp.single 2 (w ++ [k]) z) = 0 := by
      split_ifs <;> simp
    rw [hp, rightAnnihilation_single_append]
    by_cases h : i = k <;> simp [h]

theorem rightAnnihilation_semicircular (i j : ι) :
    star (rightCreation i) * semicircular j = semicircular j * star (rightCreation i) +
      if i = j then vacuumProjection else 0 := by
  have h : star (rightCreation i) * star (creation j) =
      star (creation j) * star (rightCreation i) := by
    simpa only [star_mul] using congrArg star (creation_commutes_rightCreation j i).eq
  rw [semicircular, mul_add, add_mul, rightAnnihilation_creation, h]
  abel

 theorem derivativeKernel_cons {n : ℕ} (i j : Fin n) (w : List (Fin n)) :
    derivativeKernel i (j :: w) =
      (if j = i then vacuumProjection * wordEval semicircular w else 0) +
        semicircular j * derivativeKernel i w := by
  simp only [derivativeKernel, List.length_cons, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
    List.take_zero, List.take_succ_cons, List.drop_succ_cons, Nat.zero_add,
    wordEval, List.map_nil, List.prod_nil, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [List.map_cons, List.prod_cons, mul_assoc]

 theorem rightAnnihilation_word {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    star (rightCreation i) * wordEval semicircular w =
      wordEval semicircular w * star (rightCreation i) + derivativeKernel i w := by
  induction w with
  | nil => simp [wordEval]
  | cons j w ih =>
    have hw : wordEval semicircular (j :: w) = semicircular j * wordEval semicircular w := by
      simp [wordEval]
    rw [hw, derivativeKernel_cons, ← mul_assoc, rightAnnihilation_semicircular,
      add_mul, mul_assoc, ih, mul_add]
    by_cases h : i = j <;> simp [h, eq_comm, mul_assoc, add_assoc, add_comm, add_left_comm]

 theorem trace_projection_product (A B : Space ι →L[ℂ] Space ι) :
    trace (tracialVector ι) (A * vacuumProjection * B) =
      trace (tracialVector ι) A * trace (tracialVector ι) B := by
  simp only [trace, tracialVector, vacuumProjection, mul_apply_eq_comp,
    InnerProductSpace.rankOne_apply, map_smul, inner_smul_right]
  exact mul_comm _ _

 theorem trace_derivativeKernel {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    trace (tracialVector (Fin n)) (derivativeKernel i w) =
      derivativeMoment (tracialVector (Fin n)) semicircular i w := by
  rw [derivativeKernel, trace_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [trace_projection_product, wordMoment]

 theorem trace_semicircular_left (i : ι) (A : Space ι →L[ℂ] Space ι) :
    trace (tracialVector ι) (semicircular i * A) =
      trace (tracialVector ι) (star (rightCreation i) * A) := by
  simp only [trace, tracialVector, mul_apply_eq_comp]
  rw [← ContinuousLinearMap.adjoint_inner_left (semicircular i),
    ← ContinuousLinearMap.adjoint_inner_left (star (rightCreation i))]
  simp only [← ContinuousLinearMap.star_eq_adjoint, star_star,
    (semicircular_selfAdjoint i).star_eq, basisVector,
    semicircular_single_nil, rightCreation_single, List.nil_append]

theorem semicircular_integration_by_parts {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    trace (tracialVector (Fin n)) (semicircular i * wordEval semicircular w) =
      derivativeMoment (tracialVector (Fin n)) semicircular i w := by
  rw [trace_semicircular_left, rightAnnihilation_word, trace_add, trace_derivativeKernel]
  suffices trace (tracialVector (Fin n))
      (wordEval semicircular w * star (rightCreation i)) = 0 by rw [this, zero_add]
  simp [trace, tracialVector, basisVector, mul_apply_eq_comp]

end Fock

end FiniteEntropySeparation

end

end OAI
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
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

noncomputable section
open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
namespace FiniteEntropySeparation
 theorem measure_pi_mono {ι : Type u1} [Fintype ι] {α : ι → Type u2} [∀ i,MeasurableSpace (α i)]
    (μ ν : (i:ι) → Measure (α i)) [∀i,SigmaFinite (μ i)] (h : ∀i,μ i≤ν i) :
    Measure.pi μ ≤ Measure.pi ν := by
  have ho : (Measure.pi μ).toOuterMeasure ≤ OuterMeasure.pi (fun i => (ν i).toOuterMeasure) := by
    rw [OuterMeasure.le_pi]
    intro s _
    change Measure.pi μ (Set.pi univ s) ≤ _
    rw [Measure.pi_pi]
    exact Finset.prod_le_prod' (fun i _ => h i (s i))
  rw [Measure.le_iff]
  intro s hs
  conv_rhs => rw [Measure.pi, toMeasure_apply _ _ hs]
  exact ho s
 theorem gaussianPDF_le_one (x : ℝ) : gaussianPDF 0 1 x ≤ 1 := by
  rw [gaussianPDF]
  apply ENNReal.ofReal_le_one.mpr
  have hp : 1 ≤ Real.sqrt (2*Real.pi) := by nlinarith [Real.sq_sqrt (show 0≤2*Real.pi by positivity),Real.sqrt_nonneg (2*Real.pi),Real.pi_gt_three]
  have he : Real.exp (-(x-0)^2/(2:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (x-0)])
  dsimp [gaussianPDFReal]
  norm_num only [NNReal.coe_one, mul_one]
  calc
    _ ≤ (Real.sqrt (2*Real.pi))⁻¹ * 1 := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ ≤ 1 := by rw [mul_one]; exact (inv_le_one₀ (by positivity)).2 hp
 theorem gaussianReal_le_volume : gaussianReal 0 1 ≤ (volume : Measure ℝ) := by
  rw [Measure.le_iff']
  intro s
  rw [gaussianReal_apply 0 one_ne_zero s]
  calc
    _ ≤ ∫⁻ _ : ℝ in s, (1:ℝ≥0∞) := lintegral_mono (fun x => gaussianPDF_le_one x)
    _ = volume s := by simp
 theorem productGaussian_le_volume (ι : Type u3) [Fintype ι] :
    productGaussian ι ≤ (volume : Measure (ι → ℝ)) :=
  measure_pi_mono _ _ (fun _ => gaussianReal_le_volume)
 theorem productGaussian_toLp_le_volume (ι : Type u4) [Fintype ι] (s : Set (EuclideanSpace ℝ ι)) :
    productGaussian ι (WithLp.toLp 2 ⁻¹' s) ≤ volume s := by
  apply (productGaussian_le_volume ι _).trans
  exact (PiLp.volume_preserving_toLp ι).measure_preimage_le s
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 theorem sqrt_two_complex_sq : (Real.sqrt 2 : ℂ)^2 = 2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)
 theorem inv_sqrt_two_complex_sq : ((Real.sqrt 2 : ℂ)⁻¹)^2 = (1/2 : ℂ) := by
  rw [inv_pow, sqrt_two_complex_sq, one_div]
 theorem basis_pair_contract {d : ℕ} (j k : Fin d) (D : Matrix (Fin d) (Fin d) ℂ) :
    hermitianBasis j k * D * hermitianBasis j k + hermitianBasis k j * D * hermitianBasis k j =
      Matrix.single j k 1 * D * Matrix.single k j 1 + Matrix.single k j 1 * D * Matrix.single j k 1 := by
  by_cases hjk : j=k
  · subst k; simp [hermitianBasis]
  have hcalc (A B : Matrix (Fin d) (Fin d) ℂ) :
      (((Real.sqrt 2 : ℂ)⁻¹) • (A+B)) * D * (((Real.sqrt 2 : ℂ)⁻¹) • (A+B)) +
      ((Complex.I*(Real.sqrt 2 : ℂ)⁻¹) • (A-B)) * D * ((Complex.I*(Real.sqrt 2 : ℂ)⁻¹) • (A-B)) =
      A*D*B + B*D*A := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    have hs : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (1/2 : ℂ) := by
      simpa only [pow_two] using inv_sqrt_two_complex_sq
    have hi : (Complex.I*(Real.sqrt 2 : ℂ)⁻¹) * (Complex.I*(Real.sqrt 2 : ℂ)⁻¹) = -(1/2 : ℂ) := by
      calc
        _ = Complex.I^2 * ((Real.sqrt 2 : ℂ)⁻¹)^2 := by ring
        _ = _ := by rw [Complex.I_sq, inv_sqrt_two_complex_sq]; ring
    rw [hs,hi]
    simp only [add_mul,mul_add,sub_mul,mul_sub]
    module
  rcases lt_or_gt_of_ne hjk with h | h
  · simpa only [hermitianBasis, ite_eq_right hjk, ite_eq_right (Ne.symm hjk), ite_eq_left h,
      ite_eq_right (not_lt_of_gt h)] using hcalc (Matrix.single j k 1) (Matrix.single k j 1)
  · simpa only [hermitianBasis, ite_eq_right hjk, ite_eq_right (Ne.symm hjk), ite_eq_left h,
      ite_eq_right (not_lt_of_gt h), add_comm] using hcalc (Matrix.single k j 1) (Matrix.single j k 1)
 theorem hermitianBasis_contract {d : ℕ} (D : Matrix (Fin d) (Fin d) ℂ) :
    (∑ j, ∑ k, hermitianBasis j k * D * hermitianBasis j k) = Matrix.trace D • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have hp := congrArg (fun f : Fin d → Fin d → Matrix (Fin d) (Fin d) ℂ => ∑ j, ∑ k, f j k)
    (funext (fun j => funext (fun k => basis_pair_contract j k D)))
  simp only [sum_add_distrib] at hp
  have hswap : (∑ j : Fin d, ∑ k : Fin d, hermitianBasis k j * D * hermitianBasis k j) =
      ∑ j : Fin d, ∑ k : Fin d, hermitianBasis j k * D * hermitianBasis j k := sum_comm
  have hswap' : (∑ j : Fin d, ∑ k : Fin d, Matrix.single k j 1 * D * Matrix.single j k 1) =
      ∑ j : Fin d, ∑ k : Fin d, Matrix.single j k 1 * D * Matrix.single k j 1 := sum_comm
  rw [hswap,hswap'] at hp
  have he : (∑ j : Fin d, ∑ k : Fin d, Matrix.single j k 1 * D * Matrix.single k j 1) =
      Matrix.trace D • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    ext a b
    simp only [Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.sum_apply, Matrix.single_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hab : a=b
    · subst b; simp [Matrix.trace]
    · simp only [hab, ite_false, mul_zero]
      apply sum_eq_zero
      intro j _
      simp only [ite_eq_right (show ¬(j=a ∧ j=b) from fun h => hab (h.1.symm.trans h.2)), sum_const_zero]
  rw [he] at hp
  ext a b
  have hc := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => A a b) hp
  simp only [Matrix.add_apply] at hc
  linear_combination hc / 2
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixBasisChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 theorem hermitianMatrix_single {n d : ℕ} (i l : Fin n) (j k : Fin d) :
    hermitianMatrix (EuclideanSpace.single (i,j,k) 1 : MatrixCoordinates n d) l =
      if i=l then hermitianBasis j k else 0 := by
  ext a b
  simp only [hermitianMatrix, hermitianBasis, EuclideanSpace.single, PiLp.single_apply]
  by_cases hil : i=l
  · subst l
    by_cases hjk : j=k
    · subst k
      by_cases hab : a=b
      · subst b
        by_cases hja : j=a <;> simp [*,Prod.mk.injEq,eq_comm]
      · have hbad : ¬(j=a ∧ j=b) := fun h => hab (h.1.symm.trans h.2)
        simp [*,Prod.mk.injEq,eq_comm, and_comm]
    · rcases lt_or_gt_of_ne hjk with hjk' | hkj'
      · by_cases hab : a=b
        · subst b
          have hbad : ¬(j=a ∧ k=a) := fun h => hjk (h.1.trans h.2.symm)
          have hbad' : ¬(k=a ∧ j=a) := fun h => hjk (h.2.trans h.1.symm)
          simp [*,Prod.mk.injEq,eq_comm, and_comm]
        · by_cases hjka : j=a ∧ k=b
          · rcases hjka with ⟨rfl,rfl⟩; simp [*,Prod.mk.injEq,eq_comm,div_eq_mul_inv]
          · by_cases hkja : k=a ∧ j=b
            · rcases hkja with ⟨rfl,rfl⟩; simp [*,Prod.mk.injEq,eq_comm,Ne.symm hab,not_lt_of_gt hjk',div_eq_mul_inv]
            · have hbad : ¬(j=b ∧ k=a) := fun h => hkja ⟨h.2,h.1⟩
              simp [*,Prod.mk.injEq,eq_comm, and_comm]
      · by_cases hab : a=b
        · subst b
          have hbad : ¬(j=a ∧ k=a) := fun h => hjk (h.1.trans h.2.symm)
          have hbad' : ¬(k=a ∧ j=a) := fun h => hjk (h.2.trans h.1.symm)
          simp [*,Prod.mk.injEq,eq_comm, and_comm, not_lt_of_gt hkj']
        · by_cases hjka : j=a ∧ k=b
          · rcases hjka with ⟨rfl,rfl⟩; simp [*,Prod.mk.injEq,eq_comm,not_lt_of_gt hkj',div_eq_mul_inv]
          · by_cases hkja : k=a ∧ j=b
            · rcases hkja with ⟨rfl,rfl⟩; simp [*,Prod.mk.injEq,eq_comm,Ne.symm hab,not_lt_of_gt hkj',div_eq_mul_inv]
            · have hbad : ¬(j=b ∧ k=a) := fun h => hkja ⟨h.2,h.1⟩
              simp [*,Prod.mk.injEq,eq_comm, and_comm,not_lt_of_gt hkj']
  · simp [hil,Prod.mk.injEq,eq_comm]
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
 theorem tensorGradient_integrable (a : ι → ℕ) (i : ι) :
    Integrable (tensorGradient a i) (productGaussian ι) :=
  Integrable.fintype_prod (fun _ => gaussian_polynomial_integrable 0 1 _)
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
 theorem linearExpand_integral {μ : Measure Ω} {g : κ → Ω → ℝ}
    (hg : ∀ k, Integrable (g k) μ) (a : κ →₀ ℝ) :
    (∫ x, linearExpand g a x ∂μ) = ∑ k ∈ a.support, a k*∫ x, g k x ∂μ := by
  simp only [linearExpand_apply]
  rw [integral_finsetSum _ (fun k _ => (hg k).const_mul (a k))]
  simp only [integral_const_mul]
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
 theorem gaussian_mvPolynomial_poincare (P : MvPolynomial ι ℝ) :
    (∫ x, (MvPolynomial.eval x P - ∫ y, MvPolynomial.eval y P ∂productGaussian ι)^2 ∂productGaussian ι) ≤
      ∑ i, ∫ x, (coordinateDerivative (fun y => MvPolynomial.eval y P) i x)^2 ∂productGaussian ι :=
  gaussian_poincare_mvPolynomial P
 theorem gaussian_mvPolynomial_integrable (P : MvPolynomial ι ℝ) :
    Integrable (fun x => MvPolynomial.eval x P) (productGaussian ι) := by
  obtain ⟨a,ha⟩ := mvPolynomial_hermite_expansion P
  change (fun x => MvPolynomial.eval x P) = linearExpand tensorHermite a at ha
  rw [ha]
  exact linearExpand_integrable tensorHermite_integrable a
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianMvStein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped Polynomial
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 theorem tensorHermite_coord_eq (a : ι → ℕ) (i : ι) :
    (fun x => x i*tensorHermite a x) =
      fun x => ∏ j, (if j=i then Polynomial.X*realHermite (a j) else realHermite (a j)).eval (x j) := by
  funext x
  rw [← mul_prod_erase univ _ (mem_univ i)]
  have hh : tensorHermite a x = (realHermite (a i)).eval (x i)*∏ j ∈ univ.erase i, (realHermite (a j)).eval (x j) := by
    simpa only [Function.update_eq_self] using tensorHermite_update a i (a i) x
  rw [hh]
  simp only [ite_true, Polynomial.eval_mul, Polynomial.eval_X, mul_assoc]
  congr 2
  apply prod_congr rfl
  intro j hj
  rw [ite_eq_right (ne_of_mem_erase hj)]
 theorem tensorHermite_coord_integrable (a : ι → ℕ) (i : ι) :
    Integrable (fun x => x i*tensorHermite a x) (productGaussian ι) := by
  rw [tensorHermite_coord_eq]
  exact Integrable.fintype_prod (fun j => gaussian_polynomial_integrable 0 1 _)
 theorem tensorHermite_stein (a : ι → ℕ) (i : ι) :
    (∫ x, x i*tensorHermite a x ∂productGaussian ι) = ∫ x, tensorGradient a i x ∂productGaussian ι := by
  rw [tensorHermite_coord_eq]
  unfold tensorGradient productGaussian
  rw [integral_fintype_prod_eq_prod (fun j t => (if j=i then Polynomial.X*realHermite (a j) else realHermite (a j)).eval t),
    integral_fintype_prod_eq_prod (fun j t => (if j=i then (realHermite (a j)).derivative else realHermite (a j)).eval t)]
  apply prod_congr rfl
  intro j hj
  by_cases h : j=i
  · subst j
    simpa only [ite_true, Polynomial.eval_mul, Polynomial.eval_X] using gaussian_polynomial_stein (realHermite (a i))
  · simp [h]
 theorem linearExpand_coord {ι : Type u1} [Fintype ι] [DecidableEq ι] (a : (ι → ℕ) →₀ ℝ) (i : ι) :
    (fun x => x i*linearExpand tensorHermite a x) = linearExpand (fun k x => x i*tensorHermite k x) a := by
  funext x
  simp only [linearExpand_apply, mul_sum]
  apply sum_congr rfl
  intro k hk
  ring
 theorem tensorExpansion_stein (a : (ι → ℕ) →₀ ℝ) (i : ι) :
    (∫ x, x i*linearExpand tensorHermite a x ∂productGaussian ι) =
      ∫ x, coordinateDerivative (linearExpand tensorHermite a) i x ∂productGaussian ι := by
  rw [linearExpand_coord, tensorExpansion_derivative,
    linearExpand_integral (fun k => tensorHermite_coord_integrable k i),
    linearExpand_integral (fun k => tensorGradient_integrable k i)]
  simp_rw [tensorHermite_stein]
 theorem gaussian_mvPolynomial_stein (P : MvPolynomial ι ℝ) (i : ι) :
    (∫ x, x i*MvPolynomial.eval x P ∂productGaussian ι) =
      ∫ x, coordinateDerivative (fun y => MvPolynomial.eval y P) i x ∂productGaussian ι := by
  obtain ⟨a,ha⟩ := mvPolynomial_hermite_expansion P
  change (fun x => MvPolynomial.eval x P) = linearExpand tensorHermite a at ha
  simpa only [← ha] using tensorExpansion_stein a i
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.PolynomialFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 theorem mvPolynomial_hasCoordinateDeriv {ι : Type u1} [Fintype ι] [DecidableEq ι] (P : MvPolynomial ι ℝ) (i : ι) (x : ι → ℝ) :
    HasDerivAt (fun t => MvPolynomial.eval (Function.update x i t) P)
      (MvPolynomial.eval x (MvPolynomial.pderiv i P)) (x i) := by
  induction P using MvPolynomial.induction_on with
  | C r => simpa using hasDerivAt_const (x i) r
  | add P Q hP hQ =>
    convert hP.add hQ using 1 <;> try rfl
    · funext t; simp
    · simp
  | mul_X P j hP =>
    by_cases h : j=i
    · subst j
      convert hP.mul (hasDerivAt_id (x i)) using 1 <;> try rfl
      · funext t; simp
      · simp [mul_comm, add_comm]
    · convert hP.mul_const (x j) using 1 <;> try rfl
      · funext t; simp [Function.update_of_ne h]
      · simp [MvPolynomial.pderiv_X_of_ne h, mul_comm]
 namespace IsRealPolynomial
 theorem const {ι : Type u1} [Fintype ι] [DecidableEq ι] (r : ℝ) : IsRealPolynomial (fun _ : ι → ℝ => r) := ⟨MvPolynomial.C r, by simp⟩
 theorem coord {ι : Type u1} [Fintype ι] [DecidableEq ι] (i : ι) : IsRealPolynomial (fun x : ι → ℝ => x i) := ⟨MvPolynomial.X i, by simp⟩
 theorem add {ι : Type u1} [Fintype ι] [DecidableEq ι] {f g : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (hg : IsRealPolynomial g) :
    IsRealPolynomial (fun x => f x+g x) := by
  obtain ⟨P,rfl⟩ := hf; obtain ⟨Q,rfl⟩ := hg
  exact ⟨P+Q,by simp⟩
 theorem sub {ι : Type u1} [Fintype ι] [DecidableEq ι] {f g : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (hg : IsRealPolynomial g) :
    IsRealPolynomial (fun x => f x-g x) := by
  obtain ⟨P,rfl⟩ := hf; obtain ⟨Q,rfl⟩ := hg
  exact ⟨P-Q,by simp⟩
 theorem mul {ι : Type u1} [Fintype ι] [DecidableEq ι] {f g : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (hg : IsRealPolynomial g) :
    IsRealPolynomial (fun x => f x*g x) := by
  obtain ⟨P,rfl⟩ := hf; obtain ⟨Q,rfl⟩ := hg
  exact ⟨P*Q,by simp⟩
 theorem mul_const {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (r : ℝ) :
    IsRealPolynomial (fun x => f x*r) := hf.mul (const r)
 theorem pow {ι : Type u1} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (n : ℕ) : IsRealPolynomial (fun x => f x^n) := by
  obtain ⟨P,rfl⟩ := hf
  exact ⟨P^n,by simp⟩
 theorem finset_sum {κ : Type u2} (s : Finset κ) {f : κ → (ι → ℝ) → ℝ}
    (hf : ∀ k ∈ s, IsRealPolynomial (f k)) : IsRealPolynomial (fun x => ∑ k ∈ s, f k x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (ι := ι) 0
  | @insert k s hk ih =>
    simpa [hk] using (hf k (mem_insert_self _ _)).add (ih (fun j hj => hf j (mem_insert_of_mem hj)))
 theorem continuous {ι : Type u1} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) : Continuous f := by
  obtain ⟨P,rfl⟩ := hf
  exact P.continuous_eval
 theorem integrable {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) : Integrable f (productGaussian ι) := by
  obtain ⟨P,rfl⟩ := hf
  exact gaussian_mvPolynomial_integrable P
 theorem derivative {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (i : ι) :
    IsRealPolynomial (coordinateDerivative f i) := by
  obtain ⟨P,rfl⟩ := hf
  refine ⟨MvPolynomial.pderiv i P, ?_⟩
  funext x
  exact (mvPolynomial_hasCoordinateDeriv P i x).deriv
 theorem hasDerivAt {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (i : ι) (x : ι → ℝ) :
    HasDerivAt (fun t => f (Function.update x i t)) (coordinateDerivative f i x) (x i) := by
  obtain ⟨P,rfl⟩ := hf
  have hd := mvPolynomial_hasCoordinateDeriv P i x
  exact hd.congr_deriv hd.deriv.symm
 theorem stein {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (i : ι) :
    (∫ x, x i*f x ∂productGaussian ι) = ∫ x, coordinateDerivative f i x ∂productGaussian ι := by
  obtain ⟨P,rfl⟩ := hf
  exact gaussian_mvPolynomial_stein P i
 theorem poincare {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) :
    (∫ x, (f x-∫ y, f y ∂productGaussian ι)^2 ∂productGaussian ι) ≤
      ∑ i, ∫ x, (coordinateDerivative f i x)^2 ∂productGaussian ι := by
  obtain ⟨P,rfl⟩ := hf
  exact gaussian_mvPolynomial_poincare P
 end IsRealPolynomial
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.ComplexPolynomialFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 theorem complex_integral_re {Ω : Type u2} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℂ}
    (hf : Integrable f μ) : (∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ := (integral_re hf).symm
 theorem complex_integral_im {Ω : Type u3} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℂ}
    (hf : Integrable f μ) : (∫ x, f x ∂μ).im = ∫ x, (f x).im ∂μ := (integral_im hf).symm
 namespace IsComplexPolynomial
 theorem const (z : ℂ) : IsComplexPolynomial (fun _ : ι → ℝ => z) :=
  ⟨IsRealPolynomial.const _,IsRealPolynomial.const _⟩
 theorem ofReal {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) :
    IsComplexPolynomial (fun x => (f x : ℂ)) := by
  exact ⟨hf, IsRealPolynomial.const 0⟩
 theorem coord (i : ι) : IsComplexPolynomial (fun x : ι → ℝ => (x i : ℂ)) := ofReal (IsRealPolynomial.coord i)
 theorem add {f g : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (hg : IsComplexPolynomial g) :
    IsComplexPolynomial (fun x => f x+g x) := ⟨hf.1.add hg.1,hf.2.add hg.2⟩
 theorem sub {f g : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (hg : IsComplexPolynomial g) :
    IsComplexPolynomial (fun x => f x-g x) := ⟨hf.1.sub hg.1,hf.2.sub hg.2⟩
 theorem mul {f g : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (hg : IsComplexPolynomial g) :
    IsComplexPolynomial (fun x => f x*g x) :=
  ⟨(hf.1.mul hg.1).sub (hf.2.mul hg.2),(hf.1.mul hg.2).add (hf.2.mul hg.1)⟩
 theorem const_mul {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (z : ℂ) :
    IsComplexPolynomial (fun x => z*f x) := (const z).mul hf
 theorem mul_const {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (z : ℂ) :
    IsComplexPolynomial (fun x => f x*z) := hf.mul (const z)
 theorem finset_sum {κ : Type u4} (s : Finset κ) {f : κ → (ι → ℝ) → ℂ}
    (hf : ∀ k ∈ s, IsComplexPolynomial (f k)) : IsComplexPolynomial (fun x => ∑ k ∈ s, f k x) := by
  constructor
  · simpa using IsRealPolynomial.finset_sum s (fun k hk => (hf k hk).1)
  · simpa using IsRealPolynomial.finset_sum s (fun k hk => (hf k hk).2)
 theorem continuous {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) : Continuous f := by
  have hc := (Complex.continuous_ofReal.comp hf.1.continuous).add ((Complex.continuous_ofReal.comp hf.2.continuous).mul (continuous_const (y := Complex.I)))
  convert hc using 1
  funext x
  exact (Complex.re_add_im (f x)).symm
 theorem integrable {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) : Integrable f (productGaussian ι) := by
  have hi := hf.1.integrable.ofReal.add (hf.2.integrable.ofReal.mul_const Complex.I)
  convert hi using 1 ; try rfl
  funext x
  exact (Complex.re_add_im (f x)).symm
 theorem normSq {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) :
    IsRealPolynomial (fun x => Complex.normSq (f x)) := by
  simpa only [Complex.normSq_apply, pow_two] using (hf.1.pow 2).add (hf.2.pow 2)
 theorem norm_sq {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) :
    IsRealPolynomial (fun x => ‖f x‖^2) := by simpa only [Complex.sq_norm] using hf.normSq
 theorem hasCoordinateDeriv {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (i : ι) (x : ι → ℝ) :
    HasDerivAt (fun t => f (Function.update x i t))
      ((coordinateDerivative (fun y => (f y).re) i x : ℂ) +
        (coordinateDerivative (fun y => (f y).im) i x : ℂ)*Complex.I) (x i) := by
  have hd := (hf.1.hasDerivAt i x).ofReal_comp.add ((hf.2.hasDerivAt i x).ofReal_comp.mul_const Complex.I)
  convert hd using 1 ; try rfl
  funext t
  exact (Complex.re_add_im (f (Function.update x i t))).symm
 theorem coordinateDerivative_eq {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (i : ι) (x : ι → ℝ) :
    complexCoordinateDerivative f i x =
      (coordinateDerivative (fun y => (f y).re) i x : ℂ) +
        (coordinateDerivative (fun y => (f y).im) i x : ℂ)*Complex.I :=
  (hf.hasCoordinateDeriv i x).deriv
 theorem derivative {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (i : ι) :
    IsComplexPolynomial (complexCoordinateDerivative f i) := by
  have he : complexCoordinateDerivative f i = fun x =>
      (coordinateDerivative (fun y => (f y).re) i x : ℂ) +
        (coordinateDerivative (fun y => (f y).im) i x : ℂ)*Complex.I := by
    funext x; exact hf.coordinateDerivative_eq i x
  rw [he]
  exact (ofReal (hf.1.derivative i)).add ((ofReal (hf.2.derivative i)).mul_const Complex.I)
 theorem stein {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (i : ι) :
    (∫ x, (x i : ℂ)*f x ∂productGaussian ι) = ∫ x, complexCoordinateDerivative f i x ∂productGaussian ι := by
  have hi := ((coord i).mul hf).integrable
  have hd := (hf.derivative i).integrable
  apply Complex.ext
  · rw [complex_integral_re hi, complex_integral_re hd]
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hf.coordinateDerivative_eq, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_add, add_zero] using hf.1.stein i
  · rw [complex_integral_im hi, complex_integral_im hd]
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      hf.coordinateDerivative_eq, Complex.add_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add] using hf.2.stein i
 theorem poincare {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) :
    (∫ x, ‖f x-∫ y, f y ∂productGaussian ι‖^2 ∂productGaussian ι) ≤
      ∑ i, ∫ x, ‖complexCoordinateDerivative f i x‖^2 ∂productGaussian ι := by
  have hi := hf.integrable
  have hnorm (z : ℂ) : ‖z‖^2 = z.re^2+z.im^2 := by rw [Complex.sq_norm]; simp only [Complex.normSq_apply,pow_two]
  have hr := ((hf.1.sub (IsRealPolynomial.const (∫ y, (f y).re ∂productGaussian ι))).pow 2).integrable
  have hm := ((hf.2.sub (IsRealPolynomial.const (∫ y, (f y).im ∂productGaussian ι))).pow 2).integrable
  have he : (∫ x, ‖f x-∫ y, f y ∂productGaussian ι‖^2 ∂productGaussian ι) =
      (∫ x, ((f x).re-∫ y, (f y).re ∂productGaussian ι)^2 ∂productGaussian ι) +
      ∫ x, ((f x).im-∫ y, (f y).im ∂productGaussian ι)^2 ∂productGaussian ι := by
    simp only [hnorm, Complex.sub_re, Complex.sub_im, complex_integral_re hi, complex_integral_im hi]
    exact integral_add hr hm
  rw [he]
  calc
    _ ≤ (∑ i, ∫ x, (coordinateDerivative (fun y => (f y).re) i x)^2 ∂productGaussian ι) +
        ∑ i, ∫ x, (coordinateDerivative (fun y => (f y).im) i x)^2 ∂productGaussian ι :=
      add_le_add hf.1.poincare hf.2.poincare
    _ = _ := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      rw [← integral_add ((hf.1.derivative i).pow 2).integrable ((hf.2.derivative i).pow 2).integrable]
      apply integral_congr_ae
      filter_upwards [] with x
      simp [hnorm, hf.coordinateDerivative_eq]
 end IsComplexPolynomial
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
 theorem coordinateMatrix_polynomial {n d : ℕ} (i : Fin n) (j k : Fin d) :
    IsComplexPolynomial (fun x : MatrixIndex n d → ℝ => coordinateMatrix x i j k) := by
  unfold coordinateMatrix hermitianMatrix
  split_ifs
  · exact IsComplexPolynomial.coord _
  · simpa only [div_eq_mul_inv, mul_comm, WithLp.ofLp_toLp] using ((IsComplexPolynomial.coord (i,j,k)).add ((IsComplexPolynomial.coord (i,k,j)).const_mul Complex.I)).mul_const ((Real.sqrt 2 : ℂ)⁻¹)
  · simpa only [div_eq_mul_inv, mul_comm, WithLp.ofLp_toLp] using ((IsComplexPolynomial.coord (i,k,j)).sub ((IsComplexPolynomial.coord (i,j,k)).const_mul Complex.I)).mul_const ((Real.sqrt 2 : ℂ)⁻¹)
 theorem coordinateMatrix_update {n d : ℕ} (x : MatrixIndex n d → ℝ) (q : MatrixIndex n d) (t : ℝ) (i : Fin n) :
    coordinateMatrix (Function.update x q t) i = coordinateMatrix x i +
      (t-x q) • (if q.1=i then hermitianBasis q.2.1 q.2.2 else 0) := by
  have he : (WithLp.toLp 2 (Function.update x q t) : MatrixCoordinates n d) =
      WithLp.toLp 2 x + (t-x q) • EuclideanSpace.single q 1 := by
    ext a
    by_cases h : a=q
    · subst a; simp
    · simp [EuclideanSpace.single, h]
  unfold coordinateMatrix
  rw [he, hermitianMatrix_add, hermitianMatrix_smul, hermitianMatrix_single]
 theorem coordinateMatrix_hasDeriv {n d : ℕ} (x : MatrixIndex n d → ℝ) (q : MatrixIndex n d) (i : Fin n) (j k : Fin d) :
    HasDerivAt (fun t => coordinateMatrix (Function.update x q t) i j k)
      ((if q.1=i then hermitianBasis q.2.1 q.2.2 else 0) j k) (x q) := by
  let D : Matrix (Fin d) (Fin d) ℂ := if q.1=i then hermitianBasis q.2.1 q.2.2 else 0
  have hd : HasDerivAt (fun t : ℝ => coordinateMatrix x i j k + ((t-x q : ℝ) : ℂ)*(D j k)) (D j k) (x q) := by
    simpa using ((((hasDerivAt_id (x q)).sub_const (x q)).ofReal_comp.mul_const (D j k)).const_add (coordinateMatrix x i j k))
  convert hd using 1 ; try rfl
  funext t
  rw [coordinateMatrix_update]
  by_cases he : q.1=i <;> simp [he, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, D]
 variable {ι : Type u1} {κ : Type u2} {d : Type u3} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
 namespace IsMatrixPolynomial
 theorem const {ι : Type u1} {d : Type u3} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) : IsMatrixPolynomial (fun _ : ι → ℝ => A) := fun _ _ => IsComplexPolynomial.const _
 theorem mul {ι : Type u1} {d : Type u3} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] {A B : (ι → ℝ) → Matrix d d ℂ} (hA : IsMatrixPolynomial A) (hB : IsMatrixPolynomial B) :
    IsMatrixPolynomial (fun x => A x*B x) := by
  intro j k
  exact IsComplexPolynomial.finset_sum univ (fun l _ => (hA j l).mul (hB l k))
 theorem smul {ι : Type u1} {d : Type u3} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] {A : (ι → ℝ) → Matrix d d ℂ} (hA : IsMatrixPolynomial A) (c : ℂ) :
    IsMatrixPolynomial (fun x => c • A x) := fun j k => (hA j k).const_mul c
 theorem trace {ι : Type u1} {d : Type u3} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] {A : (ι → ℝ) → Matrix d d ℂ} (hA : IsMatrixPolynomial A) :
    IsComplexPolynomial (fun x => Matrix.trace (A x)) :=
  IsComplexPolynomial.finset_sum univ (fun j _ => hA j j)
 theorem word {A : κ → (ι → ℝ) → Matrix d d ℂ} (hA : ∀ i, IsMatrixPolynomial (A i)) (w : List κ) :
    IsMatrixPolynomial (fun x => (w.map (fun i => A i x)).prod) := by
  induction w with
  | nil => exact const 1
  | cons i w ih => exact (hA i).mul ih
 end IsMatrixPolynomial
 theorem hasDerivAt_matrix_mul {d : Type u3} [Fintype d] [DecidableEq d] {A B : ℝ → Matrix d d ℂ} {A' B' : Matrix d d ℂ} {t : ℝ}
    (hA : ∀ j k, HasDerivAt (fun s => A s j k) (A' j k) t)
    (hB : ∀ j k, HasDerivAt (fun s => B s j k) (B' j k) t) :
    ∀ j k, HasDerivAt (fun s => (A s*B s) j k) ((A'*B t+A t*B') j k) t := by
  intro j k
  have hd := HasDerivAt.sum (u := univ) (fun l _ => (hA j l).mul (hB l k))
  simpa [Matrix.mul_apply, sum_add_distrib, Matrix.add_apply, Finset.sum_fn] using hd
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal
open Finset MeasureTheory Set
namespace FiniteEntropySeparation
 theorem matrixOpNorm_continuous {d : ℕ} : Continuous (matrixOpNorm (d := d)) := by
  exact ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin d) (n := Fin d)).trans
    LinearMap.toContinuousLinearMap).toLinearMap.continuous_of_finiteDimensional.norm
 theorem matrix_column_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (k : Fin d) :
    (∑ j, Complex.normSq (A j k)) ≤ matrixOpNorm A ^ 2 := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have he : T (EuclideanSpace.single k 1) = WithLp.toLp 2 (fun j => A j k) := by
    change Matrix.toEuclideanLin A (EuclideanSpace.single k 1) = _
    rw [Matrix.toLpLin_apply]
    congr 1
    simp [EuclideanSpace.single, Matrix.mulVec_single, Matrix.col, Matrix.transpose]
    rfl
  have hb := T.le_opNorm (EuclideanSpace.single k 1)
  rw [he, PiLp.norm_single, norm_one, mul_one] at hb
  have hn : ‖WithLp.toLp 2 (fun j => A j k)‖^2 = ∑ j, Complex.normSq (A j k) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Complex.normSq_eq_norm_sq]
  rw [← hn]
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2
 theorem matrix_frobenius_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    (∑ j, ∑ k, Complex.normSq (A j k)) ≤ (d : ℝ) * matrixOpNorm A ^ 2 := by
  rw [sum_comm]
  simpa using sum_le_sum (s := (univ : Finset (Fin d))) (fun k _ => matrix_column_bound A k)
 theorem coordinates_sq_bound {n d : ℕ} (a : MatrixCoordinates n d) (R : ℝ)
    (hR : 0 ≤ R) (ha : ∀ i, matrixOpNorm (hermitianMatrix a i) ≤ R) :
    ‖a‖^2 ≤ (n : ℝ)*d*R^2 := by
  rw [← hermitianChart_normSq]
  calc
    _ ≤ ∑ i : Fin n, (d : ℝ) * matrixOpNorm (hermitianMatrix a i)^2 :=
      sum_le_sum (fun i _ => matrix_frobenius_bound _)
    _ ≤ ∑ _i : Fin n, (d : ℝ)*R^2 := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) hR).mpr (ha i)) (Nat.cast_nonneg d))
    _ = _ := by simp; ring
 theorem microstates_subset_closedBall {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
    (R : ℝ) (hR : 0 ≤ R) (m d : ℕ) (ε : ℝ) :
    microstates τ X R m d ε ⊆ Metric.closedBall 0 (Real.sqrt ((n : ℝ)*d) * R) := by
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  have hb := coordinates_sq_bound a R hR ha.1
  have he : (Real.sqrt ((n : ℝ)*d) * R)^2 = (n : ℝ)*d*R^2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hn : 0 ≤ Real.sqrt ((n : ℝ)*d) * R := by positivity
  nlinarith [norm_nonneg a]
 theorem microstates_volume_lt_top {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
    (R : ℝ) (hR : 0 ≤ R) (m d : ℕ) (ε : ℝ) : volume (microstates τ X R m d ε) < ⊤ :=
  (measure_mono (microstates_subset_closedBall τ X R hR m d ε)).trans_lt
    (isCompact_closedBall (0 : MatrixCoordinates n d) _).measure_lt_top
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixParseval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 theorem coordinateMatrix_expand {n d : ℕ} (x : MatrixIndex n d → ℝ) (i : Fin n) :
    coordinateMatrix x i = ∑ j, ∑ k, (x (i,j,k) : ℂ) • hermitianBasis j k := by
  have hx : (WithLp.toLp 2 x : MatrixCoordinates n d) = ∑ q, x q • EuclideanSpace.single q 1 := by
    ext q
    simp [EuclideanSpace.single, Pi.single_apply]
  have he := congrArg (fun a : MatrixCoordinates n d => (hermitianChart n d a) i) hx
  change coordinateMatrix x i = _ at he
  rw [he]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  change (∑ q : MatrixIndex n d, x q • hermitianMatrix (EuclideanSpace.single q 1) i) = _
  simp only [Fintype.sum_prod_type, hermitianMatrix_single]
  simp only [smul_ite, smul_zero, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro k hk
  ext a b
  exact Complex.real_smul
 theorem basis_pair_parseval {d : ℕ} (j k : Fin d) (D : Matrix (Fin d) (Fin d) ℂ) :
    Complex.normSq (Matrix.trace (hermitianBasis j k*D)) + Complex.normSq (Matrix.trace (hermitianBasis k j*D)) =
      Complex.normSq (D j k)+Complex.normSq (D k j) := by
  by_cases hjk : j=k
  · subst k; simp [hermitianBasis, Matrix.trace_single_mul]
  have hcalc (z w : ℂ) :
      Complex.normSq (((Real.sqrt 2 : ℂ)⁻¹)*(z+w)) +
      Complex.normSq (Complex.I*((Real.sqrt 2 : ℂ)⁻¹)*(w-z)) = Complex.normSq z+Complex.normSq w := by
    have hs : Complex.normSq ((Real.sqrt 2 : ℂ)⁻¹) = (1/2 : ℝ) := by
      simp [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    simp only [map_mul, hs, one_mul, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
    ring
  rcases lt_or_gt_of_ne hjk with h | h
  · simpa [hermitianBasis, hjk, Ne.symm hjk, h, not_lt_of_gt h,
      smul_mul_assoc, Matrix.trace_smul, Matrix.add_mul, Matrix.sub_mul,
      Matrix.trace_add, Matrix.trace_sub, Matrix.trace_single_mul, smul_eq_mul,
      add_comm, mul_add] using hcalc (D j k) (D k j)
  · simpa [hermitianBasis, hjk, Ne.symm hjk, h, not_lt_of_gt h,
      smul_mul_assoc, Matrix.trace_smul, Matrix.add_mul, Matrix.sub_mul,
      Matrix.trace_add, Matrix.trace_sub, Matrix.trace_single_mul, smul_eq_mul,
      add_comm, mul_add] using hcalc (D k j) (D j k)
 theorem hermitianBasis_parseval {d : ℕ} (D : Matrix (Fin d) (Fin d) ℂ) :
    (∑ j, ∑ k, Complex.normSq (Matrix.trace (hermitianBasis j k*D))) = ∑ j, ∑ k, Complex.normSq (D j k) := by
  have hp := congrArg (fun f : Fin d → Fin d → ℝ => ∑ j, ∑ k, f j k)
    (funext (fun j => funext (fun k => basis_pair_parseval j k D)))
  simp only [sum_add_distrib] at hp
  have hswap : (∑ j : Fin d, ∑ k : Fin d, Complex.normSq (Matrix.trace (hermitianBasis k j*D))) =
      ∑ j : Fin d, ∑ k : Fin d, Complex.normSq (Matrix.trace (hermitianBasis j k*D)) := sum_comm
  have hswap' : (∑ j : Fin d, ∑ k : Fin d, Complex.normSq (D k j)) = ∑ j : Fin d, ∑ k : Fin d, Complex.normSq (D j k) := sum_comm
  rw [hswap,hswap'] at hp
  linarith
 theorem hermitianBasis_trace_bound {d : ℕ} (D : Matrix (Fin d) (Fin d) ℂ) :
    (∑ j, ∑ k, ‖Matrix.trace (hermitianBasis j k*D)‖^2) ≤ (d:ℝ)*matrixOpNorm D^2 := by
  simp_rw [← Complex.normSq_eq_norm_sq, hermitianBasis_parseval]
  exact matrix_frobenius_bound D
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 theorem matrixOperator_mul {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    matrixOperator (A*B) = matrixOperator A*matrixOperator B := by
  ext x j
  simp [matrixOperator, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
 theorem matrixOperator_one {d : ℕ} : matrixOperator (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext x j
  simp [matrixOperator]
 theorem matrixOperator_add {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    matrixOperator (A+B) = matrixOperator A+matrixOperator B := by
  ext x j
  simp [matrixOperator, Matrix.toLpLin_apply]
 theorem matrixOperator_smul {d : ℕ} (c : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    matrixOperator (c • A) = c • matrixOperator A := by
  ext x j
  simp [matrixOperator, Matrix.toLpLin_apply]
 theorem matrixOpNorm_nonneg {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ matrixOpNorm A := norm_nonneg _
 theorem matrixOpNorm_mul {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    matrixOpNorm (A*B) ≤ matrixOpNorm A*matrixOpNorm B := by
  change ‖matrixOperator (A*B)‖ ≤ ‖matrixOperator A‖*‖matrixOperator B‖
  rw [matrixOperator_mul]
  exact norm_mul_le _ _
 theorem matrixOpNorm_one {d : ℕ} : matrixOpNorm (1 : Matrix (Fin d) (Fin d) ℂ) ≤ 1 := by
  change ‖matrixOperator (1 : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1
  rw [matrixOperator_one]
  exact ContinuousLinearMap.norm_id_le
 theorem matrixOpNorm_add {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    matrixOpNorm (A+B) ≤ matrixOpNorm A+matrixOpNorm B := by
  change ‖matrixOperator (A+B)‖ ≤ ‖matrixOperator A‖+‖matrixOperator B‖
  rw [matrixOperator_add]
  exact norm_add_le _ _
 theorem matrixOpNorm_smul {d : ℕ} (c : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    matrixOpNorm (c • A) = ‖c‖*matrixOpNorm A := by
  change ‖matrixOperator (c • A)‖ = ‖c‖*‖matrixOperator A‖
  rw [matrixOperator_smul, norm_smul]
 theorem matrixOpNorm_word {ι : Type u1} {d : ℕ} (A : ι → Matrix (Fin d) (Fin d) ℂ) (w : List ι)
    {K : ℝ} (hK : 0 ≤ K) (hA : ∀ i ∈ w, matrixOpNorm (A i) ≤ K) :
    matrixOpNorm (w.map A).prod ≤ K^w.length := by
  induction w with
  | nil => simpa using (matrixOpNorm_one (d := d))
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    rw [mul_comm (K^w.length) K]
    exact (matrixOpNorm_mul _ _).trans (mul_le_mul (hA i (by simp))
      (ih (fun j hj => hA j (by simp [hj]))) (matrixOpNorm_nonneg _) hK)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixWordDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 variable {α : Type u1} {d : ℕ}
 theorem matrixWord_append (A : α → Matrix (Fin d) (Fin d) ℂ) (u v : List α) : matrixWord A (u++v) = matrixWord A u*matrixWord A v := by simp [matrixWord]
 theorem matrixWordVariation_cons (A D : α → Matrix (Fin d) (Fin d) ℂ) (a : α) (w : List α) :
    matrixWordVariation A D (a::w) = D a*matrixWord A w + A a*matrixWordVariation A D w := by
  unfold matrixWordVariation
  simp only [List.length_cons]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, List.take_zero, matrixWord_nil, Nat.zero_add, List.getElem_cons_zero, one_mul,
    Fin.val_succ, List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons, matrixWord_cons]
  rw [mul_sum]
  congr 1
  apply sum_congr rfl
  intro r _
  simp [mul_assoc]
 theorem hasDerivAt_matrixWord {A : ℝ → α → Matrix (Fin d) (Fin d) ℂ} {D : α → Matrix (Fin d) (Fin d) ℂ} {t : ℝ}
    (hA : ∀ a j k, HasDerivAt (fun s => A s a j k) (D a j k) t) (w : List α) :
    ∀ j k, HasDerivAt (fun s => matrixWord (A s) w j k) (matrixWordVariation (A t) D w j k) t := by
  induction w with
  | nil => intro j k; simpa using hasDerivAt_const t ((1 : Matrix (Fin d) (Fin d) ℂ) j k)
  | cons a w ih =>
    rw [matrixWordVariation_cons]
    exact hasDerivAt_matrix_mul (hA a) ih
 theorem hasDerivAt_matrixWord_trace {A : ℝ → α → Matrix (Fin d) (Fin d) ℂ} {D : α → Matrix (Fin d) (Fin d) ℂ} {t : ℝ}
    (hA : ∀ a j k, HasDerivAt (fun s => A s a j k) (D a j k) t) (w : List α) :
    HasDerivAt (fun s => Matrix.trace (matrixWord (A s) w)) (Matrix.trace (matrixWordVariation (A t) D w)) t := by
  simpa only [Matrix.trace, Matrix.diag, Finset.sum_fn] using HasDerivAt.sum (u := univ) (fun j _ => hasDerivAt_matrixWord hA w j j)
 theorem matrixWordVariation_trace (A D : α → Matrix (Fin d) (Fin d) ℂ) (w : List α) :
    Matrix.trace (matrixWordVariation A D w) = ∑ r : Fin w.length,
      Matrix.trace (D w[r.val] * (matrixWord A (w.drop (r.val+1))*matrixWord A (w.take r.val))) := by
  rw [matrixWordVariation, Matrix.trace_sum]
  apply sum_congr rfl
  intro r _
  rw [Matrix.trace_mul_cycle]
  exact Matrix.trace_mul_comm _ _
 theorem cyclicMatrixWord_bound (A : α → Matrix (Fin d) (Fin d) ℂ) (w : List α) (r : Fin w.length)
    {K : ℝ} (hK : 0 ≤ K) (hA : ∀ i ∈ w, matrixOpNorm (A i) ≤ K) :
    matrixOpNorm (cyclicMatrixWord A w r) ≤ K^(w.length-1) := by
  rw [cyclicMatrixWord, ← matrixWord_append]
  have hb := matrixOpNorm_word A (w.drop (r.val+1)++w.take r.val) hK (by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hA i (List.mem_of_mem_drop hi)
    · exact hA i (List.mem_of_mem_take hi))
  have he : (w.drop (r.val+1)++w.take r.val).length = w.length-1 := by
    simp only [List.length_append, List.length_drop, List.length_take]
    have hr := r.isLt
    omega
  simpa only [he, matrixWord] using hb
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TracialRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem leftGenerator_mem (k : Generator B N G) : leftGenerator k ∈ algebra B N G :=
  (mem_algebra_iff _).mpr (generators_commute k)

 theorem semicircularB_mem (b : B) : semicircularB (N := N) (G := G) b ∈ algebra B N G :=
  leftGenerator_mem (.inl b)
 theorem semicircularN_mem (i : N) : semicircularN (B := B) (G := G) i ∈ algebra B N G :=
  leftGenerator_mem (.inr (.inl i))
 theorem unitaryG_mem (g : G) : unitaryG (B := B) (N := N) g ∈ algebra B N G :=
  leftGenerator_mem (.inr (.inr g))

 theorem trace_unitaryG (g : G) :
    trace (tracialVector B N G) (unitaryG g) = if g = 1 then 1 else 0 := by
  change inner ℂ (basis empty) (unitaryG g (basis empty)) = _
  rw [unitaryG_basis]
  by_cases hg : g = 1 <;> simp [basis, leftG, empty, lp.inner_single_left, lp.single_apply, hg, eq_comm]

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.HeatTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem vacuumBoundary_eq_rankOne :
    vacuumBoundary (B := B) (N := N) (G := G) = vacuumRankOne (tracialVector B N G) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change vacuumBoundary (lp.single 2 w z) = _
  rw [vacuumBoundary_single]
  by_cases hw : w = empty
  · subst w
    simp [vacuumRankOne, tracialVector, basis, lp.inner_single_left]
    simpa using (lp.single_smul (E := fun _ : Word B N G => ℂ) 2 (empty : Word B N G) z (1 : ℂ))
  · simp [hw, vacuumRankOne, tracialVector, basis, lp.inner_single_left, lp.single_apply, Ne.symm hw]

 theorem rightAnnihilationN_semicircularN (i j : N) :
    star (rightCreationN (B := B) (G := G) i) * semicircularN j =
      semicircularN j * star (rightCreationN i) + if i = j then
        vacuumRankOne (tracialVector B N G) else 0 := by
  have h : Commute (creationN (B := B) (G := G) j) (rightCreationN i) :=
    LabelHilbert.lift_commute _ _ _ _ (leftN_rightN j i)
  have hs := h.star_star.symm.eq
  rw [semicircularN, mul_add, add_mul, rightAnnihilationN_creationN, hs,
    vacuumBoundary_eq_rankOne]
  abel

 theorem rightAnnihilationN_commutes_semicircularB (i : N) (b : B) :
    Commute (star (rightCreationN (G := G) i)) (semicircularB b) := by
  have h : Commute (creationB (G := G) b) (rightCreationN i) :=
    LabelHilbert.lift_commute _ _ _ _ (leftB_rightN b i)
  exact (creationB_commutes_rightAnnihilationN b i).symm.add_right h.star_star.symm

 theorem rightAnnihilationN_background {i : N} {J : Set N} (hi : i ∉ J)
    {T : Space B N G →L[ℂ] Space B N G} (hT : T ∈ backgroundAlgebra J) :
    Commute (star (rightCreationN i)) T := by
  induction hT using Algebra.adjoin_induction with
  | mem T hT =>
    rcases hT with ((⟨b,rfl⟩ | ⟨g,rfl⟩) | ⟨j,hj,rfl⟩)
    · exact rightAnnihilationN_commutes_semicircularB i b
    · exact (unitaryG_commutes_rightAnnihilationN g i).symm
    · have hij : i ≠ j := fun h => hi (h ▸ hj)
      show _ * _ = _ * _
      simpa [hij] using rightAnnihilationN_semicircularN (B := B) (G := G) i j
  | algebraMap z => exact (Algebra.commute_algebraMap_left z _).symm
  | add T U _ _ hT hU => exact hT.add_right hU
  | mul T U _ _ hT hU => exact hT.mul_right hU

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.VolumetricNet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory Metric Set
open scoped ENNReal NNReal
namespace FiniteEntropySeparation
 variable {E : Type u1} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 theorem separated_card_bound (s : Finset E) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hs : ∀ c ∈ s, ‖c‖ ≤ R) (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → ε ≤ ‖c-d‖) :
    (s.card : ℝ) ≤ (1+2*R/ε)^Module.finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := ε/2
  let ρ : ℝ := R+δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let A := ⋃ c ∈ s, ball c δ
  have hD : Set.Pairwise (s : Set E) (fun c d => Disjoint (ball c δ) (ball d δ)) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    simpa [δ] using hsep c hc d hd hcd
  have hA : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ball_subset_ball' ?_
    rw [dist_zero_right]
    dsimp [ρ]
    linarith [hs x hx]
  have hI : (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^Module.finrank ℝ E)*μ (ball 0 1) ≤
      ENNReal.ofReal (ρ^Module.finrank ℝ E)*μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [show A = ⋃ c ∈ s, ball c δ from rfl, measure_biUnion_finset hD (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hA
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have hJ : (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^Module.finrank ℝ E) ≤ ENNReal.ofReal (ρ^Module.finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 hI
  have hK : (s.card : ℝ)*δ^Module.finrank ℝ E ≤ ρ^Module.finrank ℝ E := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using
      ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hJ
  have he : (1+2*R/ε)*δ = ρ := by dsimp [δ,ρ]; field_simp; ring
  apply (mul_le_mul_iff_left₀ (pow_pos hδ _)).mp
  rw [← mul_pow, he]
  exact hK
 theorem compact_finite_net (A : Set E) (hA : IsCompact A) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hAR : ∀ x ∈ A, ‖x‖ ≤ R) :
    ∃ s : Finset E, (∀ x ∈ s, x ∈ A) ∧ (∀ x ∈ A, ∃ y ∈ s, dist x y ≤ ε) ∧
      (s.card : ℝ) ≤ (1+2*R/ε)^Module.finrank ℝ E := by
  classical
  let e : ℝ≥0 := ⟨ε,hε.le⟩
  have he : e/2 ≠ 0 := ne_of_gt (div_pos (show 0 < e from hε) (by norm_num))
  obtain ⟨N,hNA,hNfin,hNcov⟩ := Metric.exists_finite_isCover_of_isCompact (ε := (e/2 : ℝ≥0)) he hA
  have hpn : packingNumber e A ≠ ⊤ := by
    have hb := packingNumber_two_mul_le_externalCoveringNumber (e/2) A
    rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ≥0) ≠ 0)] at hb
    exact ne_top_of_le_ne_top hNfin.encard_lt_top.ne (hb.trans hNcov.externalCoveringNumber_le_encard)
  let K := maximalSeparatedSet e A
  have hKfin : K.Finite := Set.encard_ne_top_iff.mp (by simpa [K, encard_maximalSeparatedSet hpn] using hpn)
  refine ⟨hKfin.toFinset, ?_, ?_, ?_⟩
  · intro x hx; exact maximalSeparatedSet_subset (by simpa using hx)
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := isCover_maximalSeparatedSet hpn hx
    refine ⟨y, by simpa using hy, ?_⟩
    exact (edist_le_coe).mp hxy
  · apply separated_card_bound _ hR hε
    · intro x hx; exact hAR x (maximalSeparatedSet_subset (by simpa using hx))
    · intro x hx y hy hxy
      have hh := isSeparated_maximalSeparatedSet (ε := e) (A := A) (by simpa using hx) (by simpa using hy) hxy
      have hh' : e < nndist x y := by simpa only [edist_nndist, ENNReal.coe_lt_coe] using hh
      have hh'' : ε < dist x y := hh'
      simpa only [dist_eq_norm] using hh''.le
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianLinearTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped NNReal
open MeasureTheory ProbabilityTheory Finset Set
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem gaussianLinear_exp_eq (c : ι → ℝ) (t : ℝ) :
    (fun x => Real.exp (t*gaussianLinear c x)) = fun x => ∏ i, Real.exp ((t*c i)*x i) := by
  funext x
  rw [← Real.exp_sum]
  congr 1
  simp [gaussianLinear, mul_sum, mul_assoc]
 theorem gaussianLinear_exp_integrable (c : ι → ℝ) (t : ℝ) :
    Integrable (fun x => Real.exp (t*gaussianLinear c x)) (productGaussian ι) := by
  rw [gaussianLinear_exp_eq]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (t*c i))
 theorem gaussianLinear_mgf (c : ι → ℝ) (t : ℝ) :
    mgf (gaussianLinear c) (productGaussian ι) t = Real.exp ((∑ i, c i^2)*t^2/2) := by
  unfold mgf
  rw [gaussianLinear_exp_eq]
  unfold productGaussian
  rw [integral_fintype_prod_eq_prod (fun i s => Real.exp ((t*c i)*s))]
  have hi (i : ι) : (∫ s, Real.exp ((t*c i)*s) ∂gaussianReal 0 1) = Real.exp ((t*c i)^2/2) := by
    simpa only [mgf, NNReal.coe_one, zero_mul, zero_add, one_mul] using congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) (t*c i)
  simp_rw [hi]
  rw [← Real.exp_sum]
  congr 1
  simp [mul_pow, sum_div, sum_mul]
  ring_nf
 theorem gaussianLinear_subgaussian (c : ι → ℝ) (K : ℝ≥0) (hK : (∑ i, c i^2) ≤ K) :
    HasSubgaussianMGF (gaussianLinear c) K (productGaussian ι) where
  integrable_exp_mul := gaussianLinear_exp_integrable c
  mgf_le t := by rw [gaussianLinear_mgf]; apply Real.exp_le_exp.mpr; gcongr
 theorem gaussianLinear_tail (c : ι → ℝ) (K : ℝ≥0) (hK : (∑ i, c i^2) ≤ K) {u : ℝ} (hu : 0 ≤ u) :
    (productGaussian ι).real {x | u ≤ |gaussianLinear c x|} ≤ 2*Real.exp (-u^2/(2*K)) := by
  have h := gaussianLinear_subgaussian c K hK
  have hp := h.measure_ge_le hu
  have hm := h.neg.measure_ge_le hu
  have he : {x | u ≤ |gaussianLinear c x|} = {x | u ≤ gaussianLinear c x} ∪ {x | u ≤ -gaussianLinear c x} := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_union]; exact le_abs
  rw [he]
  calc
    _ ≤ (productGaussian ι).real {x | u ≤ gaussianLinear c x} + (productGaussian ι).real {x | u ≤ -gaussianLinear c x} := measureReal_union_le _ _
    _ ≤ _ := by simpa only [Pi.neg_apply] using add_le_add hp hm |>.trans_eq (two_mul _).symm
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate NNReal
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
 theorem matrixBilinear_trace {d : ℕ} (v w : EuclideanSpace ℂ (Fin d)) (A : Matrix (Fin d) (Fin d) ℂ) :
    matrixBilinear v w A = Matrix.trace (A * Matrix.vecMulVec (WithLp.ofLp w) (star (WithLp.ofLp v))) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  rfl
 theorem matrixBilinear_expand {n d : ℕ} (x : MatrixIndex n d → ℝ) (i : Fin n) (v w : EuclideanSpace ℂ (Fin d)) :
    matrixBilinear v w (coordinateMatrix x i) = ∑ j, ∑ k, (x (i,j,k) : ℂ)*matrixBilinear v w (hermitianBasis j k) := by
  simp_rw [matrixBilinear_trace]
  rw [coordinateMatrix_expand]
  simp [Finset.sum_mul, Matrix.trace_sum, Matrix.trace_smul]
 theorem matrixBilinear_parseval {d : ℕ} (v w : EuclideanSpace ℂ (Fin d)) :
    (∑ j, ∑ k, Complex.normSq (matrixBilinear v w (hermitianBasis j k))) = ‖v‖^2*‖w‖^2 := by
  simp_rw [matrixBilinear_trace, hermitianBasis_parseval]
  simp only [Matrix.vecMulVec_apply, map_mul, Pi.star_apply, Complex.star_def, Complex.normSq_conj]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp_rw [Complex.normSq_eq_norm_sq]
  rw [sum_comm]
  simp only [← sum_mul, ← mul_sum]
  ring
 theorem matrixBilinear_re_coeff {n d : ℕ} (i : Fin n) (v w : EuclideanSpace ℂ (Fin d)) :
    (∑ q : MatrixIndex n d, (if q.1=i then (matrixBilinear v w (hermitianBasis q.2.1 q.2.2)).re else 0)^2) ≤ ‖v‖^2*‖w‖^2 := by
  rw [Fintype.sum_prod_type]
  simp only [ite_pow, zero_pow (by norm_num : 2 ≠ 0), Fintype.sum_prod_type, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  rw [← matrixBilinear_parseval]
  apply sum_le_sum; intro j _
  apply sum_le_sum; intro k _
  rw [Complex.normSq_apply]
  nlinarith [sq_nonneg (matrixBilinear v w (hermitianBasis j k)).im]
 theorem matrixBilinear_im_coeff {n d : ℕ} (i : Fin n) (v w : EuclideanSpace ℂ (Fin d)) :
    (∑ q : MatrixIndex n d, (if q.1=i then (matrixBilinear v w (hermitianBasis q.2.1 q.2.2)).im else 0)^2) ≤ ‖v‖^2*‖w‖^2 := by
  rw [Fintype.sum_prod_type]
  simp only [ite_pow, zero_pow (by norm_num : 2 ≠ 0), Fintype.sum_prod_type, sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  rw [← matrixBilinear_parseval]
  apply sum_le_sum; intro j _
  apply sum_le_sum; intro k _
  rw [Complex.normSq_apply]
  nlinarith [sq_nonneg (matrixBilinear v w (hermitianBasis j k)).re]
 theorem matrixBilinear_re_linear {n d : ℕ} (x : MatrixIndex n d → ℝ) (i : Fin n) (v w : EuclideanSpace ℂ (Fin d)) :
    (matrixBilinear v w (coordinateMatrix x i)).re = gaussianLinear (fun q : MatrixIndex n d => if q.1=i then (matrixBilinear v w (hermitianBasis q.2.1 q.2.2)).re else 0) x := by
  rw [matrixBilinear_expand]
  simp [gaussianLinear, Fintype.sum_prod_type, Complex.mul_re, mul_comm]
 theorem matrixBilinear_im_linear {n d : ℕ} (x : MatrixIndex n d → ℝ) (i : Fin n) (v w : EuclideanSpace ℂ (Fin d)) :
    (matrixBilinear v w (coordinateMatrix x i)).im = gaussianLinear (fun q : MatrixIndex n d => if q.1=i then (matrixBilinear v w (hermitianBasis q.2.1 q.2.2)).im else 0) x := by
  rw [matrixBilinear_expand]
  simp [gaussianLinear, Fintype.sum_prod_type, Complex.mul_im, mul_comm]
 theorem matrixBilinear_gaussian_tail {n d : ℕ} (i : Fin n) (v w : EuclideanSpace ℂ (Fin d))
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) {u : ℝ} (hu : 0 ≤ u) :
    (productGaussian (MatrixIndex n d)).real {x | u ≤ ‖matrixBilinear v w (coordinateMatrix x i)‖} ≤ 4*Real.exp (-u^2/8) := by
  let cr : MatrixIndex n d → ℝ := fun q => if q.1=i then (matrixBilinear v w (hermitianBasis q.2.1 q.2.2)).re else 0
  let ci : MatrixIndex n d → ℝ := fun q => if q.1=i then (matrixBilinear v w (hermitianBasis q.2.1 q.2.2)).im else 0
  have hr : (∑ q, cr q^2) ≤ (1:ℝ≥0) := by simpa [cr,hv,hw] using matrixBilinear_re_coeff i v w
  have hi : (∑ q, ci q^2) ≤ (1:ℝ≥0) := by simpa [ci,hv,hw] using matrixBilinear_im_coeff i v w
  have hsub : {x | u ≤ ‖matrixBilinear v w (coordinateMatrix x i)‖} ⊆ {x | u/2 ≤ |gaussianLinear cr x|} ∪ {x | u/2 ≤ |gaussianLinear ci x|} := by
    intro x hx
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    by_contra! hh
    have hn := Complex.norm_le_abs_re_add_abs_im (matrixBilinear v w (coordinateMatrix x i))
    rw [matrixBilinear_re_linear, matrixBilinear_im_linear] at hn
    change u ≤ _ at hx
    change |gaussianLinear cr x|+|gaussianLinear ci x| ≥ _ at hn
    linarith
  calc
    _ ≤ (productGaussian (MatrixIndex n d)).real ({x | u/2 ≤ |gaussianLinear cr x|} ∪ {x | u/2 ≤ |gaussianLinear ci x|}) := measureReal_mono hsub
    _ ≤ _ + _ := measureReal_union_le _ _
    _ ≤ 2*Real.exp (-(u/2)^2/(2*(1:ℝ≥0))) + 2*Real.exp (-(u/2)^2/(2*(1:ℝ≥0))) := add_le_add (gaussianLinear_tail cr 1 hr (by positivity)) (gaussianLinear_tail ci 1 hi (by positivity))
    _ = _ := by norm_num only [NNReal.coe_one]; ring_nf
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.BilinearNet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ComplexConjugate
open Finset Metric Set
namespace FiniteEntropySeparation
 variable {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
 theorem norm_le_of_unit_inner (z : E) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v : E, ‖v‖ = 1 → ‖inner ℂ v z‖ ≤ C) : ‖z‖ ≤ C := by
  by_cases hz : z=0
  · simpa [hz] using hC
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hv : ‖(‖z‖⁻¹ : ℝ) • z‖ = 1 := by rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]
  have hh := h ((‖z‖⁻¹ : ℝ) • z) hv
  simpa [inner_smul_real_left, norm_smul, inner_self_eq_norm_sq_to_K, norm_pow,
    Real.norm_eq_abs, abs_inv, abs_norm, sq, ← mul_assoc, inv_mul_cancel₀ hn] using hh
 theorem opNorm_le_of_bilinear (T : E →L[ℂ] E) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → ‖inner ℂ x (T y)‖ ≤ C) : ‖T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro y hy
  exact norm_le_of_unit_inner _ hC (fun x hx => h x y hx hy)
 theorem bilinear_net_bound (T : E →L[ℂ] E) (s : Finset E)
    (hs : ∀ x ∈ s, ‖x‖ = 1)
    (hcov : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, dist x y ≤ 1/4)
    {M : ℝ} (hM : 0 ≤ M) (hB : ∀ x ∈ s, ∀ y ∈ s, ‖inner ℂ x (T y)‖ ≤ M) : ‖T‖ ≤ 2*M := by
  have hb : ‖T‖ ≤ M + ‖T‖/2 := by
    apply opNorm_le_of_bilinear T (by positivity)
    intro x y hx hy
    obtain ⟨u,hu,hxu⟩ := hcov x hx
    obtain ⟨v,hv,hyv⟩ := hcov y hy
    have he : inner ℂ x (T y) = inner ℂ u (T v) + inner ℂ (x-u) (T y) + inner ℂ u (T (y-v)) := by
      simp only [map_sub, inner_sub_left, inner_sub_right]; abel
    have h1 : ‖inner ℂ (x-u) (T y)‖ ≤ ‖T‖/4 := by
      calc
        _ ≤ ‖x-u‖*‖T y‖ := norm_inner_le_norm _ _
        _ ≤ (1/4)*(‖T‖*‖y‖) := mul_le_mul (by simpa [dist_eq_norm] using hxu) (T.le_opNorm y) (norm_nonneg _) (by norm_num)
        _ = _ := by rw [hy]; ring
    have h2 : ‖inner ℂ u (T (y-v))‖ ≤ ‖T‖/4 := by
      calc
        _ ≤ ‖u‖*‖T (y-v)‖ := norm_inner_le_norm _ _
        _ ≤ ‖u‖*(‖T‖*‖y-v‖) := mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
        _ ≤ 1*(‖T‖*(1/4)) := by rw [hs u hu]; gcongr; simpa [dist_eq_norm] using hyv
        _ = _ := by ring
    rw [he]
    exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hB u hu v hv) h1)) h2)).trans_eq (by ring)
  linarith
 theorem sphere_finite_net [FiniteDimensional ℝ E] :
    ∃ s : Finset E, (∀ x ∈ s, ‖x‖ = 1) ∧
    (∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, dist x y ≤ 1/4) ∧
    (s.card : ℝ) ≤ 9^Module.finrank ℝ E := by
  obtain ⟨s,hs,hc,hb⟩ := compact_finite_net (sphere (0:E) 1) (isCompact_sphere 0 1)
    (R := 1) (ε := 1/4) (by norm_num) (by norm_num) (by intro x hx; exact (mem_sphere_zero_iff_norm.mp hx).le)
  refine ⟨s,?_,?_,?_⟩
  · intro x hx; exact mem_sphere_zero_iff_norm.mp (hs x hx)
  · intro x hx; exact hc x (mem_sphere_zero_iff_norm.mpr hx)
  · norm_num at hb ⊢; exact hb
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUEOperatorTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Set Metric
namespace FiniteEntropySeparation
 theorem coordinateMatrix_norm_tail {n d : ℕ} (i : Fin n) {u : ℝ} (hu : 0 ≤ u) :
    (productGaussian (MatrixIndex n d)).real {x | 2*u < matrixOpNorm (coordinateMatrix x i)} ≤
      4*9^(4*d)*Real.exp (-u^2/8) := by
  classical
  obtain ⟨s,hs,hcov,hcard⟩ := sphere_finite_net (E := EuclideanSpace ℂ (Fin d))
  have hdim : Module.finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2*d := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace_fin]
  rw [hdim] at hcard
  let E : EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin d) → Set (MatrixIndex n d → ℝ) :=
    fun q => {x | u ≤ ‖matrixBilinear q.1 q.2 (coordinateMatrix x i)‖}
  have hsub : {x | 2*u < matrixOpNorm (coordinateMatrix x i)} ⊆ ⋃ q ∈ s ×ˢ s, E q := by
    intro x hx
    by_contra hh
    have hall : ∀ v ∈ s, ∀ w ∈ s, ‖matrixBilinear v w (coordinateMatrix x i)‖ ≤ u := by
      intro v hv w hw
      have hn : x ∉ E (v,w) := fun h => hh (mem_iUnion₂.mpr ⟨(v,w), mem_product.mpr ⟨hv,hw⟩, h⟩)
      exact (not_le.mp hn).le
    have hb := bilinear_net_bound (matrixOperator (coordinateMatrix x i)) s hs hcov hu hall
    exact (not_lt_of_ge hb) hx
  calc
    _ ≤ (productGaussian (MatrixIndex n d)).real (⋃ q ∈ s ×ˢ s, E q) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ q ∈ s ×ˢ s, (productGaussian (MatrixIndex n d)).real (E q) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ s ×ˢ s, 4*Real.exp (-u^2/8) := by
      apply sum_le_sum
      intro q hq
      exact matrixBilinear_gaussian_tail i q.1 q.2 (hs _ (mem_product.mp hq).1) (hs _ (mem_product.mp hq).2) hu
    _ = (s.card:ℝ)^2*(4*Real.exp (-u^2/8)) := by simp [sq]
    _ ≤ (9^(2*d))^2*(4*Real.exp (-u^2/8)) := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) (by positivity)
    _ = _ := by rw [← pow_mul, show 2*d*2=4*d by omega]; ring
 theorem gueMatrix_norm {n d : ℕ} (x : MatrixIndex n d → ℝ) (i : Fin n) :
    matrixOpNorm (gueMatrix x i) = (Real.sqrt d)⁻¹ * matrixOpNorm (coordinateMatrix x i) := by
  rw [gueMatrix, matrixOpNorm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
 theorem gueMatrix_norm_tail {n d : ℕ} (hd : 0 < d) (i : Fin n) {L : ℝ} (hL : 0 ≤ L) :
    (productGaussian (MatrixIndex n d)).real {x | L < matrixOpNorm (gueMatrix x i)} ≤
      4*9^(4*d)*Real.exp (-((d:ℝ)*L^2)/32) := by
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd'
  have he : {x : MatrixIndex n d → ℝ | L < matrixOpNorm (gueMatrix x i)} =
      {x | 2*(L*Real.sqrt d/2) < matrixOpNorm (coordinateMatrix x i)} := by
    ext x
    simp only [mem_ofPred_eq, gueMatrix_norm, ← div_eq_inv_mul, lt_div_iff₀ hs]
    ring_nf
  rw [he]
  convert coordinateMatrix_norm_tail i (u := L*Real.sqrt d/2) (by positivity) using 1
  congr 2
  rw [div_pow, mul_pow, Real.sq_sqrt hd'.le]
  ring
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUEDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ComplexConjugate Classical
open Finset
namespace FiniteEntropySeparation
 variable {α : Type u1} {n d : ℕ}
 theorem jointMatrix_polynomial (A : α → Matrix (Fin d) (Fin d) ℂ) (a : α ⊕ Fin n) :
    IsMatrixPolynomial (fun x : MatrixIndex n d → ℝ => jointMatrix A x a) := by
  cases a with
  | inl a => exact IsMatrixPolynomial.const (A a)
  | inr i => exact (show IsMatrixPolynomial (fun x : MatrixIndex n d → ℝ => coordinateMatrix x i) from fun j k => coordinateMatrix_polynomial i j k).smul _
 theorem jointMatrix_hasDeriv (A : α → Matrix (Fin d) (Fin d) ℂ) (x : MatrixIndex n d → ℝ) (q : MatrixIndex n d)
    (a : α ⊕ Fin n) (j k : Fin d) :
    HasDerivAt (fun t => jointMatrix A (Function.update x q t) a j k) (noiseDirection (α := α) q a j k) (x q) := by
  classical
  cases a with
  | inl a => simpa [jointMatrix, noiseDirection] using hasDerivAt_const (x q) (A a j k)
  | inr i =>
    have hh := (coordinateMatrix_hasDeriv x q i j k).const_mul ((Real.sqrt d:ℂ)⁻¹)
    by_cases h : q.1=i
    · simpa [jointMatrix, gueMatrix, noiseDirection, h] using hh
    · simpa [jointMatrix, gueMatrix, noiseDirection, h, Ne.symm h] using hh
 theorem matrixTraceWord_polynomial (A : α → Matrix (Fin d) (Fin d) ℂ) (w : List (α ⊕ Fin n)) :
    IsComplexPolynomial (fun x : MatrixIndex n d → ℝ => matrixTraceWord (jointMatrix A x) w) :=
  ((IsMatrixPolynomial.word (jointMatrix_polynomial A) w).trace).const_mul _
 theorem matrixTraceWord_derivative (A : α → Matrix (Fin d) (Fin d) ℂ) (w : List (α ⊕ Fin n))
    (q : MatrixIndex n d) (x : MatrixIndex n d → ℝ) :
    complexCoordinateDerivative (fun y => matrixTraceWord (jointMatrix A y) w) q x =
      ((d:ℂ)⁻¹ * (Real.sqrt d:ℂ)⁻¹) * ∑ r : Fin w.length,
        if w[r.val]=Sum.inr q.1 then Matrix.trace (hermitianBasis q.2.1 q.2.2 * cyclicMatrixWord (jointMatrix A x) w r) else 0 := by
  classical
  have hd := (hasDerivAt_matrixWord_trace (jointMatrix_hasDeriv A x q) w).const_mul ((d:ℂ)⁻¹)
  have he := hd.deriv
  change complexCoordinateDerivative (fun y => matrixTraceWord (jointMatrix A y) w) q x = _ at he
  simp only [Function.update_eq_self] at he
  rw [he, matrixWordVariation_trace]
  simp only [noiseDirection, cyclicMatrixWord]
  rw [mul_assoc]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro r _
  split_ifs <;> simp [Matrix.trace_smul]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUEGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped Classical
namespace FiniteEntropySeparation
 theorem norm_sum_sq_le {ι : Type u1} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖^2 ≤ (s.card:ℝ)*∑ i ∈ s, ‖f i‖^2 := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s f) 2).trans (sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖f i‖))
 theorem basisNoise_trace_bound {α : Type u2} {n d : ℕ} (a : α ⊕ Fin n) (D : Matrix (Fin d) (Fin d) ℂ) :
    (∑ q : MatrixIndex n d, ‖(if a=Sum.inr q.1 then Matrix.trace (hermitianBasis q.2.1 q.2.2*D) else 0 : ℂ)‖^2) ≤
      (d:ℝ)*matrixOpNorm D^2 := by
  cases a with
  | inl a => simp; positivity
  | inr i =>
    simpa [Fintype.sum_prod_type, apply_ite, sum_ite_irrel, sum_ite_eq] using hermitianBasis_trace_bound D
 theorem matrixTraceWord_gradient_bound {α : Type u3} {n d : ℕ} (hd : 0 < d)
    (A : α → Matrix (Fin d) (Fin d) ℂ) (w : List (α ⊕ Fin n))
    (x : MatrixIndex n d → ℝ) {K : ℝ} (hK : 0 ≤ K) (hA : ∀ i ∈ w, matrixOpNorm (jointMatrix A x i) ≤ K) :
    (∑ q, ‖complexCoordinateDerivative (fun y => matrixTraceWord (jointMatrix A y) w) q x‖^2) ≤
      (w.length:ℝ)^2/(d:ℝ)^2 * K^(2*(w.length-1)) := by
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hc : ‖((d:ℂ)⁻¹*(Real.sqrt d:ℂ)⁻¹)‖^2 = (d:ℝ)⁻¹^3 := by
    simp only [norm_mul, mul_pow, norm_inv, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    field_simp
  simp only [norm_mul, mul_pow] at hc
  simp_rw [matrixTraceWord_derivative, norm_mul, mul_pow, hc]
  rw [← mul_sum]
  calc
    _ ≤ (d:ℝ)⁻¹^3 * ∑ q : MatrixIndex n d, (w.length:ℝ)*∑ r : Fin w.length,
          ‖(if w[r.val]=Sum.inr q.1 then Matrix.trace (hermitianBasis q.2.1 q.2.2*cyclicMatrixWord (jointMatrix A x) w r) else 0 : ℂ)‖^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro q _
      simpa using norm_sum_sq_le univ (fun r : Fin w.length => if w[r.val]=Sum.inr q.1 then Matrix.trace (hermitianBasis q.2.1 q.2.2*cyclicMatrixWord (jointMatrix A x) w r) else 0)
    _ = (d:ℝ)⁻¹^3 * ((w.length:ℝ)*∑ r : Fin w.length, ∑ q : MatrixIndex n d,
          ‖(if w[r.val]=Sum.inr q.1 then Matrix.trace (hermitianBasis q.2.1 q.2.2*cyclicMatrixWord (jointMatrix A x) w r) else 0 : ℂ)‖^2) := by rw [← mul_sum, sum_comm]
    _ ≤ (d:ℝ)⁻¹^3 * ((w.length:ℝ)*∑ _r : Fin w.length, (d:ℝ)*(K^(w.length-1))^2) := by
      gcongr with r
      exact (basisNoise_trace_bound _ _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (matrixOpNorm_nonneg _) (cyclicMatrixWord_bound _ _ _ hK hA) 2) (Nat.cast_nonneg _))
    _ = _ := by
      simp only [sum_const, card_fin, nsmul_eq_mul, ← pow_mul]
      rw [Nat.mul_comm (w.length-1) 2]
      field_simp
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUEMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
namespace FiniteEntropySeparation
 theorem gueMatrix_norm_tail_uniform {n d : ℕ} (hd : 0 < d) (i : Fin n) {L : ℝ} (hL : 0 ≤ L) :
    (productGaussian (MatrixIndex n d)).real {x | L < matrixOpNorm (gueMatrix x i)} ≤
      (4*Real.exp 64)*Real.exp (-L^2/64) := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  by_cases hlarge : 64 ≤ L
  · have hlog : 4*Real.log 9 ≤ L^2/64 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<9)
      nlinarith [sq_nonneg (L-64)]
    have he : (4*(d:ℝ))*Real.log 9 - (d:ℝ)*L^2/32 ≤ -L^2/64 := by
      calc
        _ = (d:ℝ)*(4*Real.log 9-L^2/32) := by ring
        _ ≤ (d:ℝ)*(-L^2/64) := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
        _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (sq_nonneg L)]
    calc
      _ ≤ 4*9^(4*d)*Real.exp (-((d:ℝ)*L^2)/32) := gueMatrix_norm_tail hd i hL
      _ = 4*Real.exp ((4*(d:ℝ))*Real.log 9 - (d:ℝ)*L^2/32) := by
        rw [show (9:ℝ)^(4*d)=Real.exp ((4*(d:ℝ))*Real.log 9) by rw [show 4*(d:ℝ)=((4*d:ℕ):ℝ) by push_cast; rfl, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<9)]]
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ 4*Real.exp (-L^2/64) := by gcongr
      _ ≤ _ := by
        have hh : 1 ≤ Real.exp (64:ℝ) := by simp
        nlinarith [Real.exp_pos (-L^2/64)]
  · have hL2 : L^2/64 ≤ 64 := by nlinarith
    have hh : 1 ≤ Real.exp 64*Real.exp (-L^2/64) := by
      rw [← Real.exp_add]; simpa using Real.exp_le_exp.mpr (show 0 ≤ 64 + -L^2/64 by linarith)
    exact (measureReal_le_one).trans (by nlinarith)
 theorem gueMatrix_norm_measurable {n d : ℕ} (i : Fin n) :
    Measurable (fun x : MatrixIndex n d → ℝ => matrixOpNorm (gueMatrix x i)) := by
  unfold gueMatrix
  apply (matrixOpNorm_continuous.comp ?_).measurable
  exact (continuous_const (y := (Real.sqrt d:ℂ)⁻¹)).smul (show Continuous (fun x : MatrixIndex n d → ℝ => coordinateMatrix x i) from
    continuous_pi (fun j => continuous_pi (fun k => (coordinateMatrix_polynomial i j k).continuous)))
 theorem gaussianMomentMajorant_nonneg (m : ℕ) : 0 ≤ gaussianMomentMajorant m := by
  apply mul_nonneg (by positivity)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  positivity
 theorem tail_power_integral {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : Measurable Z) (hZ0 : ∀ x, 0 ≤ Z x)
    (htail : ∀ t ≥ 0, μ.real {x | t < Z x} ≤ (4*Real.exp 64)*Real.exp (-t^2/64)) (m : ℕ) :
    Integrable (fun x => Z x^(m+1)) μ ∧ (∫ x, Z x^(m+1) ∂μ) ≤ gaussianMomentMajorant m := by
  have hi : IntegrableOn (fun t : ℝ => t^m*Real.exp (-t^2/64)) (Ioi 0) := by
    convert integrableOn_rpow_mul_exp_neg_mul_sq (b := (1:ℝ)/64) (by norm_num) (s := (m:ℝ)) (by have := Nat.cast_nonneg (α := ℝ) m; linarith) using 1
    simp only [Real.rpow_natCast]
    funext t
    congr 1
    congr 1
    ring
  have hi' := hi.const_mul ((4*Real.exp 64)*(m+1))
  have hpos : 0 ≤ᵐ[volume.restrict (Ioi 0)] (fun t : ℝ => ((4*Real.exp 64)*(m+1))*(t^m*Real.exp (-t^2/64))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    positivity
  have hbound : (∫⁻ x, ENNReal.ofReal (Z x^(m+1)) ∂μ) ≤ ENNReal.ofReal (gaussianMomentMajorant m) := by
    have he := lintegral_rpow_eq_lintegral_meas_lt_mul μ (ae_of_all _ hZ0) hZ.aemeasurable (p := (m+1:ℕ)) (by positivity)
    simp only [Real.rpow_natCast] at he
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at he
    rw [he]
    calc
      _ ≤ ENNReal.ofReal ((m:ℝ)+1) * ∫⁻ t : ℝ in Ioi 0,
          ENNReal.ofReal ((4*Real.exp 64)*Real.exp (-t^2/64))*ENNReal.ofReal (t^(m:ℝ)) := by
        apply mul_le_mul' le_rfl
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        apply mul_le_mul' _ le_rfl
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
        exact ENNReal.ofReal_le_ofReal (htail t ht.le)
      _ = ENNReal.ofReal (gaussianMomentMajorant m) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp only [Real.rpow_natCast]
        simp only [← ENNReal.ofReal_mul (by positivity : 0 ≤ (4:ℝ)*Real.exp 64*Real.exp _)]
        simp only [← ENNReal.ofReal_mul (by positivity : 0 ≤ (m:ℝ)+1)]
        have heq : ∀ t : ℝ, ((m:ℝ)+1)*((4*Real.exp 64*Real.exp (-t^2/64))*t^m) =
            ((4*Real.exp 64)*(m+1))*(t^m*Real.exp (-t^2/64)) := by intro t; ring
        simp_rw [heq]
        rw [ ← ofReal_integral_eq_lintegral_ofReal hi' hpos]
        congr 1
        exact integral_const_mul _ _
  have hint : Integrable (fun x => Z x^(m+1)) μ := ⟨(hZ.pow_const _).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => pow_nonneg (hZ0 x) _))).mpr (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  have hnn : 0 ≤ ∫ x, Z x^(m+1) ∂μ := integral_nonneg (fun x => pow_nonneg (hZ0 x) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun x => pow_nonneg (hZ0 x) _))] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (gaussianMomentMajorant_nonneg m)).mp hbound
 theorem gueMatrix_norm_moment {n d : ℕ} (hd : 0 < d) (i : Fin n) (m : ℕ) :
    Integrable (fun x => matrixOpNorm (gueMatrix x i)^(m+1)) (productGaussian (MatrixIndex n d)) ∧
    (∫ x, matrixOpNorm (gueMatrix x i)^(m+1) ∂productGaussian (MatrixIndex n d)) ≤ gaussianMomentMajorant m :=
  tail_power_integral _ (gueMatrix_norm_measurable i) (fun _ => norm_nonneg _) (fun _ ht => gueMatrix_norm_tail_uniform hd i ht) m
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUEBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped Classical
namespace FiniteEntropySeparation
 theorem jointNoiseBound_nonneg {n d : ℕ} {R : ℝ} (hR : 0 ≤ R) (x : MatrixIndex n d → ℝ) :
    0 ≤ jointNoiseBound R x := add_nonneg hR (sum_nonneg (fun _ _ => norm_nonneg _))
 theorem jointNoiseBound_measurable {n d : ℕ} (R : ℝ) : Measurable (jointNoiseBound (n := n) (d := d) R) :=
   measurable_const.add (Finset.measurable_sum _ (fun i _ => gueMatrix_norm_measurable i))
 theorem jointMatrix_norm_bound {α : Type u1} {n d : ℕ} (A : α → Matrix (Fin d) (Fin d) ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ a, matrixOpNorm (A a) ≤ R) (x : MatrixIndex n d → ℝ) (a : α ⊕ Fin n) :
    matrixOpNorm (jointMatrix A x a) ≤ jointNoiseBound R x := by
  cases a with
  | inl a =>
    change matrixOpNorm (A a) ≤ R + ∑ i, matrixOpNorm (gueMatrix x i)
    exact (hA a).trans (le_add_of_nonneg_right (sum_nonneg (fun i _ => matrixOpNorm_nonneg (gueMatrix x i))))
  | inr i =>
    change matrixOpNorm (gueMatrix x i) ≤ R + ∑ j, matrixOpNorm (gueMatrix x j)
    have hl : matrixOpNorm (gueMatrix x i) ≤ ∑ j, matrixOpNorm (gueMatrix x j) :=
      single_le_sum (fun j _ => matrixOpNorm_nonneg (gueMatrix x j)) (mem_univ i)
    exact hl.trans (le_add_of_nonneg_left hR)
 theorem jointNoiseBound_power {n d : ℕ} {R : ℝ} (hR : 0 ≤ R) (x : MatrixIndex n d → ℝ) (m : ℕ) :
    jointNoiseBound R x^(m+1) ≤ (n+1:ℝ)^m * (R^(m+1)+∑ i, matrixOpNorm (gueMatrix x i)^(m+1)) := by
  let f : Option (Fin n) → ℝ := Option.elim' R (fun i => matrixOpNorm (gueMatrix x i))
  have hf : ∀ i ∈ (univ : Finset (Option (Fin n))), 0 ≤ f i := by
    intro i _; cases i <;> simp [f,hR,matrixOpNorm_nonneg]
  simpa [f, Fintype.sum_option, jointNoiseBound, add_comm] using pow_sum_le_card_mul_sum_pow hf m
 theorem jointNoiseBound_moment {n d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 ≤ R) (m : ℕ) :
    Integrable (fun x => jointNoiseBound R x^m) (productGaussian (MatrixIndex n d)) ∧
    (∫ x, jointNoiseBound R x^m ∂productGaussian (MatrixIndex n d)) ≤ jointMomentBound n R m := by
  cases m with
  | zero => simp [jointMomentBound]
  | succ m =>
    have hi (i : Fin n) := (gueMatrix_norm_moment hd i m).1
    have hsum : Integrable (fun x => ∑ i : Fin n, matrixOpNorm (gueMatrix x i)^(m+1)) (productGaussian (MatrixIndex n d)) := integrable_finsetSum _ (fun i _ => hi i)
    have hbig := ((integrable_const (R^(m+1))).add hsum).const_mul ((n+1:ℝ)^m)
    have hsmall : Integrable (fun x : MatrixIndex n d → ℝ => jointNoiseBound R x^(m+1)) (productGaussian (MatrixIndex n d)) := by
      apply hbig.mono' ((jointNoiseBound_measurable R).pow_const _).aestronglyMeasurable
      exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (jointNoiseBound_nonneg hR x) _)]; exact jointNoiseBound_power hR x m)
    refine ⟨hsmall, ?_⟩
    calc
      _ ≤ ∫ x : MatrixIndex n d → ℝ, ((n+1:ℝ)^m)*(R^(m+1)+∑ i, matrixOpNorm (gueMatrix x i)^(m+1)) ∂productGaussian (MatrixIndex n d) :=
        integral_mono hsmall hbig (fun x => jointNoiseBound_power hR x m)
      _ = (n+1:ℝ)^m*(R^(m+1)+∑ i, ∫ x, matrixOpNorm (gueMatrix x i)^(m+1) ∂productGaussian (MatrixIndex n d)) := by
        rw [integral_const_mul, integral_add (integrable_const _) hsum, integral_finsetSum _ (fun i _ => hi i)]; simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add_right
        calc
          _ ≤ ∑ _i : Fin n, gaussianMomentMajorant m := sum_le_sum (fun i _ => (gueMatrix_norm_moment hd i m).2)
          _ = _ := by simp
 theorem matrixTraceWord_variance_bound {α : Type u2} {n d : ℕ} (hd : 0 < d)
    (A : α → Matrix (Fin d) (Fin d) ℂ) {R : ℝ} (hR : 0 ≤ R) (hA : ∀ a, matrixOpNorm (A a) ≤ R)
    (w : List (α ⊕ Fin n)) :
    (∫ x, ‖matrixTraceWord (jointMatrix A x) w - ∫ y, matrixTraceWord (jointMatrix A y) w ∂productGaussian (MatrixIndex n d)‖^2 ∂productGaussian (MatrixIndex n d)) ≤
      (w.length:ℝ)^2/(d:ℝ)^2 * jointMomentBound n R (2*(w.length-1)) := by
  let f := fun x : MatrixIndex n d → ℝ => matrixTraceWord (jointMatrix A x) w
  have hf : IsComplexPolynomial f := matrixTraceWord_polynomial A w
  have hi (q : MatrixIndex n d) := ((hf.derivative q).norm_sq).integrable
  calc
    _ ≤ ∑ q, ∫ x, ‖complexCoordinateDerivative f q x‖^2 ∂productGaussian (MatrixIndex n d) := hf.poincare
    _ = ∫ x, ∑ q, ‖complexCoordinateDerivative f q x‖^2 ∂productGaussian (MatrixIndex n d) := (integral_finsetSum _ (fun q _ => hi q)).symm
    _ ≤ ∫ x, ((w.length:ℝ)^2/(d:ℝ)^2)*jointNoiseBound R x^(2*(w.length-1)) ∂productGaussian (MatrixIndex n d) := by
      apply integral_mono (integrable_finsetSum _ (fun q _ => hi q)) ((jointNoiseBound_moment hd hR _).1.const_mul _)
      intro x
      exact matrixTraceWord_gradient_bound hd A w x (jointNoiseBound_nonneg hR x) (fun a _ => jointMatrix_norm_bound A hR hA x a)
    _ = ((w.length:ℝ)^2/(d:ℝ)^2)*(∫ x, jointNoiseBound R x^(2*(w.length-1)) ∂productGaussian (MatrixIndex n d)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (jointNoiseBound_moment hd hR _).2 (by positivity)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUEStein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped Classical
namespace FiniteEntropySeparation
 variable {α : Type u1} {n d : ℕ}
 theorem basis_trace_contract (P Q : Matrix (Fin d) (Fin d) ℂ) :
    (∑ j, ∑ k, Matrix.trace (hermitianBasis j k*P*hermitianBasis j k*Q)) = Matrix.trace P*Matrix.trace Q := by
  simp_rw [← Matrix.trace_sum, ← sum_mul]
  rw [hermitianBasis_contract, smul_mul_assoc, one_mul, Matrix.trace_smul, smul_eq_mul]
 theorem fixedTraceWord_polynomial (A : α → Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin d) (Fin d) ℂ) (w : List (α ⊕ Fin n)) :
    IsComplexPolynomial (fun x : MatrixIndex n d → ℝ => Matrix.trace (B*matrixWord (jointMatrix A x) w)) :=
   ((IsMatrixPolynomial.const B).mul (IsMatrixPolynomial.word (jointMatrix_polynomial A) w)).trace
 theorem fixedTraceWord_derivative (A : α → Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin d) (Fin d) ℂ) (w : List (α ⊕ Fin n)) (q : MatrixIndex n d) (x : MatrixIndex n d → ℝ) :
    complexCoordinateDerivative (fun y => Matrix.trace (B*matrixWord (jointMatrix A y) w)) q x =
      (Real.sqrt d:ℂ)⁻¹ * ∑ r : Fin w.length, if w[r.val]=Sum.inr q.1 then
        Matrix.trace (B*matrixWord (jointMatrix A x) (w.take r.val)*hermitianBasis q.2.1 q.2.2*matrixWord (jointMatrix A x) (w.drop (r.val+1))) else 0 := by
  have hm := hasDerivAt_matrix_mul (fun j k => hasDerivAt_const (x q) (B j k)) (hasDerivAt_matrixWord (jointMatrix_hasDeriv A x q) w)
  have ht := HasDerivAt.sum (u := univ) (fun j _ => hm j j)
  have htrace : HasDerivAt (fun y => Matrix.trace (B*matrixWord (jointMatrix A (Function.update x q y)) w))
      (Matrix.trace (B*matrixWordVariation (jointMatrix A (Function.update x q (x q))) (noiseDirection q) w)) (x q) := by
    simpa only [Finset.sum_fn, Matrix.trace, Matrix.diag, show (fun _ _ : Fin d => (0:ℂ)) = (0:Matrix (Fin d) (Fin d) ℂ) from rfl, Matrix.zero_mul, zero_add] using ht
  have he := htrace.deriv
  change complexCoordinateDerivative (fun y => Matrix.trace (B*matrixWord (jointMatrix A y) w)) q x = _ at he
  simp only [Function.update_eq_self] at he
  rw [he]
  change Matrix.trace (B*matrixWordVariation (jointMatrix A x) (noiseDirection q) w) = _
  simp only [matrixWordVariation, mul_sum, Matrix.trace_sum]
  apply sum_congr rfl
  intro r _
  simp only [noiseDirection]
  split_ifs <;> simp [Matrix.trace_smul, mul_assoc]
 theorem gueTraceWord_expand (A : α → Matrix (Fin d) (Fin d) ℂ) (i : Fin n) (w : List (α ⊕ Fin n)) (x : MatrixIndex n d → ℝ) :
    matrixTraceWord (jointMatrix A x) (Sum.inr i::w) =
      ((d:ℂ)⁻¹*(Real.sqrt d:ℂ)⁻¹)*∑ j, ∑ k, (x (i,j,k):ℂ)*Matrix.trace (hermitianBasis j k*matrixWord (jointMatrix A x) w) := by
  simp only [matrixTraceWord, matrixWord_cons, jointMatrix, Sum.elim_inr, gueMatrix, coordinateMatrix_expand,
    smul_mul_assoc, sum_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, mul_sum]
  ring_nf
 theorem gueTraceWord_stein (_hd : 0 < d) (A : α → Matrix (Fin d) (Fin d) ℂ) (i : Fin n) (w : List (α ⊕ Fin n)) :
    (∫ x, matrixTraceWord (jointMatrix A x) (Sum.inr i::w) ∂productGaussian (MatrixIndex n d)) =
      ∑ r : Fin w.length, if w[r.val]=Sum.inr i then
        ∫ x, matrixTraceWord (jointMatrix A x) (w.take r.val)*matrixTraceWord (jointMatrix A x) (w.drop (r.val+1)) ∂productGaussian (MatrixIndex n d) else 0 := by
  let F := fun (j k : Fin d) (x : MatrixIndex n d → ℝ) => Matrix.trace (hermitianBasis j k*matrixWord (jointMatrix A x) w)
  have hF (j k : Fin d) : IsComplexPolynomial (F j k) := fixedTraceWord_polynomial A _ w
  have hi (j k : Fin d) := ((IsComplexPolynomial.coord (i,j,k)).mul (hF j k)).integrable
  have hdF (j k : Fin d) := ((hF j k).derivative (i,j,k)).integrable
  simp_rw [gueTraceWord_expand]
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi j k))]
  simp_rw [integral_finsetSum _ (fun k _ => hi _ k)]
  change ((d:ℂ)⁻¹*(Real.sqrt d:ℂ)⁻¹)*(∑ j, ∑ k, ∫ x, (x (i,j,k):ℂ)*F j k x ∂productGaussian (MatrixIndex n d)) = _
  simp_rw [(hF _ _).stein]
  simp_rw [← integral_finsetSum _ (fun k _ => hdF _ k)]
  rw [← integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hdF j k))]
  have hcalc (x : MatrixIndex n d → ℝ) : (∑ j, ∑ k, complexCoordinateDerivative (F j k) (i,j,k) x) =
      (Real.sqrt d:ℂ)⁻¹ * ∑ r : Fin w.length, if w[r.val]=Sum.inr i then
        Matrix.trace (matrixWord (jointMatrix A x) (w.take r.val))*Matrix.trace (matrixWord (jointMatrix A x) (w.drop (r.val+1))) else 0 := by
    simp only [F, fixedTraceWord_derivative]
    simp_rw [← mul_sum]
    congr 1
    have hs : ∀ j : Fin d, (∑ k : Fin d, ∑ r : Fin w.length, if w[r.val]=Sum.inr i then
        Matrix.trace (hermitianBasis j k*matrixWord (jointMatrix A x) (w.take r.val)*hermitianBasis j k*matrixWord (jointMatrix A x) (w.drop (r.val+1))) else 0) =
        ∑ r : Fin w.length, ∑ k : Fin d, if w[r.val]=Sum.inr i then
        Matrix.trace (hermitianBasis j k*matrixWord (jointMatrix A x) (w.take r.val)*hermitianBasis j k*matrixWord (jointMatrix A x) (w.drop (r.val+1))) else 0 := fun _ => sum_comm
    simp_rw [hs]
    rw [sum_comm]
    apply sum_congr rfl
    intro r _
    simp only [sum_ite_irrel, sum_const_zero]
    split_ifs
    · exact basis_trace_contract _ _
    · rfl
  simp_rw [hcalc]
  rw [integral_const_mul, ← mul_assoc]
  have hc : (d:ℂ)⁻¹*(Real.sqrt d:ℂ)⁻¹*(Real.sqrt d:ℂ)⁻¹=(d:ℂ)⁻¹*(d:ℂ)⁻¹ := by
    rw [mul_assoc, ← pow_two, inv_pow]
    have hs : (Real.sqrt d:ℂ)^2=(d:ℂ) := by norm_cast; exact Real.sq_sqrt (Nat.cast_nonneg _)
    rw [hs]
  rw [hc]
  have hp (r : Fin w.length) := ((IsMatrixPolynomial.word (jointMatrix_polynomial A) (w.take r.val)).trace.mul
    (IsMatrixPolynomial.word (jointMatrix_polynomial A) (w.drop (r.val+1))).trace).integrable
  rw [integral_finsetSum _ (fun r _ => by split_ifs <;> first | exact hp r | exact integrable_const 0)]
  rw [mul_sum]
  apply sum_congr rfl
  intro r _
  split_ifs with h
  · simp only [matrixTraceWord]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  · simp
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUECovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Classical Topology
namespace FiniteEntropySeparation
 theorem complex_polynomial_covariance {ι : Type u1} [Fintype ι] [DecidableEq ι]
    {f g : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (hg : IsComplexPolynomial g) :
    ‖(∫ x, f x*g x ∂productGaussian ι)-(∫ x, f x ∂productGaussian ι)*(∫ x, g x ∂productGaussian ι)‖ ≤
      ((∫ x, ‖f x-∫ y, f y ∂productGaussian ι‖^2 ∂productGaussian ι)+
        (∫ x, ‖g x-∫ y, g y ∂productGaussian ι‖^2 ∂productGaussian ι))/2 := by
  let a := ∫ x, f x ∂productGaussian ι
  let b := ∫ x, g x ∂productGaussian ι
  have hf' := hf.sub (IsComplexPolynomial.const a)
  have hg' := hg.sub (IsComplexPolynomial.const b)
  have he : (∫ x, (f x-a)*(g x-b) ∂productGaussian ι) = (∫ x, f x*g x ∂productGaussian ι)-a*b := by
    have heq : (fun x => (f x-a)*(g x-b)) = fun x => f x*g x-f x*b-a*g x+a*b := by funext x; ring
    rw [heq, integral_add ((hf.mul hg).sub (hf.mul_const b) |>.sub (hg.const_mul a)).integrable (integrable_const _),
      integral_sub ((hf.mul hg).sub (hf.mul_const b)).integrable (hg.const_mul a).integrable,
      integral_sub (hf.mul hg).integrable (hf.mul_const b).integrable,
      integral_mul_const, integral_const_mul]
    simp only [a,b,integral_const,probReal_univ,one_smul]
    ring
  rw [← he]
  calc
    _ ≤ ∫ x, ‖(f x-a)*(g x-b)‖ ∂productGaussian ι := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (‖f x-a‖^2+‖g x-b‖^2)/2 ∂productGaussian ι := by
      apply integral_mono (hf'.mul hg').integrable.norm (((hf'.norm_sq).add (hg'.norm_sq)).integrable.div_const 2)
      intro x
      dsimp only
      rw [norm_mul]
      nlinarith [sq_nonneg (‖f x-a‖-‖g x-b‖)]
    _ = _ := by rw [integral_div, integral_add hf'.norm_sq.integrable hg'.norm_sq.integrable]
 theorem matrixTraceWord_covariance_bound {α : Type u2} {n d : ℕ} (hd : 0 < d)
    (A : α → Matrix (Fin d) (Fin d) ℂ) {R : ℝ} (hR : 0 ≤ R) (hA : ∀ a, matrixOpNorm (A a) ≤ R)
    (u v : List (α ⊕ Fin n)) :
    ‖(∫ x, matrixTraceWord (jointMatrix A x) u*matrixTraceWord (jointMatrix A x) v ∂productGaussian (MatrixIndex n d))-
      (∫ x, matrixTraceWord (jointMatrix A x) u ∂productGaussian (MatrixIndex n d))*(∫ x, matrixTraceWord (jointMatrix A x) v ∂productGaussian (MatrixIndex n d))‖ ≤
      ((u.length:ℝ)^2*jointMomentBound n R (2*(u.length-1))+(v.length:ℝ)^2*jointMomentBound n R (2*(v.length-1)))/(2*(d:ℝ)^2) := by
  have h := complex_polynomial_covariance (matrixTraceWord_polynomial A u) (matrixTraceWord_polynomial A v)
  have hu := matrixTraceWord_variance_bound hd A hR hA u
  have hv := matrixTraceWord_variance_bound hd A hR hA v
  calc
    _ ≤ _ := h
    _ ≤ (((u.length:ℝ)^2/(d:ℝ)^2)*jointMomentBound n R (2*(u.length-1))+((v.length:ℝ)^2/(d:ℝ)^2)*jointMomentBound n R (2*(v.length-1)))/2 := by linarith
    _ = _ := by ring
 theorem tendsto_zero_of_norm_bound_inv_sq {D : ℕ → ℕ} (hD : Tendsto D atTop atTop)
    {f : ℕ → ℂ} {C : ℝ} (hf : ∀ k, ‖f k‖ ≤ C/(D k:ℝ)^2) : Tendsto f atTop (𝓝 0) := by
  have ht : Tendsto (fun k => C/(D k:ℝ)^2) atTop (𝓝 0) := by
    have hc : Tendsto (fun k => (D k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hD
    have hi := tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0) |>.comp hc)
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hi
  exact squeeze_zero_norm hf ht
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUELimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Classical Topology
namespace FiniteEntropySeparation
 theorem matrixTraceWord_cyclic {α : Type u1} {d : ℕ} (A : α → Matrix (Fin d) (Fin d) ℂ) (u v : List α) :
    matrixTraceWord A (u++v) = matrixTraceWord A (v++u) := by
  simp only [matrixTraceWord, matrixWord_append]
  rw [Matrix.trace_mul_comm]
 theorem matrixWord_map {α : Type u2} {β : Type u3} {d : ℕ} (A : β → Matrix (Fin d) (Fin d) ℂ) (f : α → β) (w : List α) :
    matrixWord A (w.map f) = matrixWord (A ∘ f) w := by simp [matrixWord,List.map_map]
 theorem matrixTraceWord_map {α : Type u4} {β : Type u5} {d : ℕ} (A : β → Matrix (Fin d) (Fin d) ℂ) (f : α → β) (w : List α) :
    matrixTraceWord A (w.map f) = matrixTraceWord (A ∘ f) w := by simp [matrixTraceWord,matrixWord_map]
 theorem sum_word_left_or_noise {α : Type u6} {β : Type u7} (w : List (α ⊕ β)) :
    (∃ u : List α, w=u.map Sum.inl) ∨ (∃ u i v, w=u++Sum.inr i::v) := by
  induction w with
  | nil => exact Or.inl ⟨[],rfl⟩
  | cons a w ih =>
    cases a with
    | inl a =>
      rcases ih with ⟨u,rfl⟩ | ⟨u,i,v,rfl⟩
      · exact Or.inl ⟨a::u,rfl⟩
      · exact Or.inr ⟨Sum.inl a::u,i,v,rfl⟩
    | inr i => exact Or.inr ⟨[],i,w,rfl⟩
 theorem tendsto_of_sub_zero {f g : ℕ → ℂ} {z : ℂ} (hfg : Tendsto (fun k => f k-g k) atTop (𝓝 0))
    (hg : Tendsto g atTop (𝓝 z)) : Tendsto f atTop (𝓝 z) := by
  simpa only [sub_add_cancel, zero_add] using hfg.add hg
 variable {α : Type u8} {n : ℕ} {D : ℕ → ℕ}
 theorem matrixTraceWord_covariance_tendsto (hD0 : ∀ k, 0 < D k) (hD : Tendsto D atTop atTop)
    (A : (k : ℕ) → α → Matrix (Fin (D k)) (Fin (D k)) ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ k a, matrixOpNorm (A k a) ≤ R) (u v : List (α ⊕ Fin n)) :
    Tendsto (fun k => (∫ x, matrixTraceWord (jointMatrix (A k) x) u*matrixTraceWord (jointMatrix (A k) x) v ∂productGaussian (MatrixIndex n (D k)))-
      expectedMatrixWord A k u*expectedMatrixWord A k v) atTop (𝓝 0) := by
  apply tendsto_zero_of_norm_bound_inv_sq hD (C := ((u.length:ℝ)^2*jointMomentBound n R (2*(u.length-1))+(v.length:ℝ)^2*jointMomentBound n R (2*(v.length-1)))/2)
  intro k
  convert matrixTraceWord_covariance_bound (hD0 k) (A k) hR (hA k) u v using 1
  · rfl
  · ring
 theorem expectedMatrixWord_tendsto (hD0 : ∀ k, 0 < D k) (hD : Tendsto D atTop atTop)
    (A : (k : ℕ) → α → Matrix (Fin (D k)) (Fin (D k)) ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ k a, matrixOpNorm (A k a) ≤ R) (M : List (α ⊕ Fin n) → ℂ)
    (hcyclic : ∀ u v, M (u++v)=M (v++u))
    (hbase : ∀ u : List α, Tendsto (fun k => matrixTraceWord (A k) u) atTop (𝓝 (M (u.map Sum.inl))))
    (hrec : ∀ (i : Fin n) (w : List (α ⊕ Fin n)), M (Sum.inr i::w) =
      ∑ r : Fin w.length, if w[r.val]=Sum.inr i then M (w.take r.val)*M (w.drop (r.val+1)) else 0)
    (w : List (α ⊕ Fin n)) : Tendsto (fun k => expectedMatrixWord A k w) atTop (𝓝 (M w)) := by
  induction w using (measure List.length).wf.induction with
  | h w ih =>
    rcases sum_word_left_or_noise w with ⟨u,rfl⟩ | ⟨u,i,v,rfl⟩
    · simpa [expectedMatrixWord,matrixTraceWord_map,jointMatrix,Function.comp_def] using hbase u
    · have hrecLimit : Tendsto (fun k => expectedMatrixWord A k (Sum.inr i::(v++u))) atTop (𝓝 (M (Sum.inr i::(v++u)))) := by
        simp only [expectedMatrixWord, gueTraceWord_stein (hD0 _), hrec]
        apply tendsto_finsetSum
        intro r _
        split_ifs with hr
        · apply tendsto_of_sub_zero (matrixTraceWord_covariance_tendsto hD0 hD A hR hA _ _)
          apply Tendsto.mul
          · exact ih ((v++u).take r.val) (by change ((v++u).take r.val).length < (u++Sum.inr i::v).length; have hh:=r.isLt; simp only [List.length_take,List.length_append,List.length_cons] at *; omega)
          · exact ih ((v++u).drop (r.val+1)) (by change ((v++u).drop (r.val+1)).length < (u++Sum.inr i::v).length; simp only [List.length_drop,List.length_append,List.length_cons]; omega)
        · exact tendsto_const_nhds
      convert hrecLimit using 1
      · funext k
        exact congrArg (fun f => ∫ x, f x ∂productGaussian (MatrixIndex n (D k))) (funext (fun x => matrixTraceWord_cyclic (jointMatrix (A k) x) u (Sum.inr i::v)))
      · exact congrArg (fun z : ℂ => 𝓝 z) (hcyclic u (Sum.inr i::v))
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WordSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type u1}

 theorem conv_sum_splits (f g : Series α) (w : List α) :
    conv f g w = ∑ k ∈ range (w.length+1), f (w.take k) * g (w.drop k) := by
  induction w generalizing f with
  | nil => simp
  | cons a w ih =>
    rw [conv_cons, ih, List.length_cons]
    conv_rhs => rw [sum_range_succ']
    simp only [List.take_zero, List.drop_zero, List.take_succ_cons, List.drop_succ_cons, deriv_apply]
    ring

@[simp] theorem conv_zero_left (f : Series α) : conv 0 f = 0 := by
  funext w
  simp [conv_sum_splits]
@[simp] theorem conv_zero_right (f : Series α) : conv f 0 = 0 := by
  funext w
  simp [conv_sum_splits]

@[simp] theorem conv_unit_left (f : Series α) : conv unit f = f := by
  funext w
  cases w <;> simp [conv, deriv_unit]

theorem length_induction {P : List α → Prop} (w : List α)
    (h : ∀ w, (∀ v, v.length < w.length → P v) → P w) : P w :=
  (measure List.length).wf.induction w h

 theorem subst_cons (M f : Series α) (a : α) (w : List α) :
    subst M f (a::w) = conv M (subst M (deriv a f)) w := by
  rw [subst, conv_sum_splits]

 theorem subst_smul (M f : Series α) (c : ℂ) : subst M (c • f) = c • subst M f := by
  funext w
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a w =>
      simp only [subst, Pi.smul_apply, smul_eq_mul]
      simp_rw [show deriv a (c • f) = c • deriv a f from rfl]
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [ih _ (by simp)]
      simp [mul_left_comm]

@[simp] theorem subst_zero (M : Series α) : subst M 0 = 0 := by
  have h := subst_smul M 0 0
  simpa using h
@[simp] theorem subst_unit (M : Series α) : subst M unit = unit := by
  funext w
  cases w with
  | nil => simp
  | cons a w => simp [subst_cons]

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SemicircularSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [DecidableEq α]

 theorem deriv_letter (i j : α) : deriv j (letter i) = if j=i then unit else 0 := by
  funext w
  cases w with
  | nil => by_cases h : j=i <;> simp [deriv, letter, unit, h]
  | cons a w => cases w <;> by_cases h : j=i <;> simp [deriv, letter, unit, h]
 theorem subst_letter_cons (M : Series α) (i j : α) (w : List α) :
    subst M (letter i) (j::w) = if j=i then M w else 0 := by
  rw [subst_cons, deriv_letter]
  split_ifs <;> simp
 theorem deriv_quadratic (i : α) : deriv i (quadratic : Series α) = letter i := by
  funext w
  cases w with
  | nil => rfl
  | cons a w => cases w <;> rfl

 theorem quadratic_subst_derivative {n : ℕ} (M : Series (Fin n)) (i : Fin n) (w : List (Fin n)) :
    subst M quadratic (i::w) = ∑ r : Fin w.length, if w[r.val] = i then
      M (w.take r.val) * M (w.drop (r.val+1)) else 0 := by
  rw [subst_cons, deriv_quadratic, conv_sum_splits, sum_range_succ]
  simp only [List.take_length, List.drop_length, subst_nil, letter_nil, mul_zero, add_zero]
  rw [← Fin.sum_univ_eq_sum_range (fun k => M (w.take k) * subst M (letter i) (w.drop k))]
  apply sum_congr rfl
  intro k hk
  rw [List.drop_eq_getElem_cons k.isLt, subst_letter_cons]
  split_ifs <;> simp

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.LinearSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α β γ : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

 theorem reparam_cons {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (f : Series α) (b : β) (w : List β) :
    reparam c f (b::w) = ∑ a, c a b * reparam c (deriv a f) w := rfl
end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EmbeddedSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α β γ : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

variable [DecidableEq γ] [Fintype γ]

 theorem Cyclic.append {α : Type} [DecidableEq α] [Fintype α] {f : Series α} (hf : Cyclic f) (u v : List α) :
    f (u++v) = f (v++u) := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
    have hh := congrFun (hf a) (u++v)
    change f (a::(u++v)) = f ((u++v)++[a]) at hh
    simp only [List.cons_append, hh, List.append_assoc]
    rw [ih]
    simp

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WordLinearLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation
open Finset FreeSeries
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem wordEval_mem {M : VonNeumannAlgebra H} {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (hX : ∀ i, X i ∈ M) (w : List (Fin n)) : wordEval X w ∈ M := by
  induction w with
  | nil => simp [wordEval]
  | cons i w ih => simpa [wordEval] using M.mul_mem (hX i) ih
 theorem wordMoment_cyclic {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (hX : ∀ i, X i ∈ M) : Cyclic (wordMoment τ X) := by
  intro i
  funext w
  change trace τ ((i::w).map X).prod = trace τ ((w++[i]).map X).prod
  simpa [trace, wordEval, List.map_cons, List.prod_cons, List.map_append, List.prod_append] using
    τ.tracial (X i) (hX i) (wordEval X w) (wordEval_mem X hX w)

 theorem reparam_wordMoment {M : VonNeumannAlgebra H} (τ : TracialVector M) {n m : ℕ}
    (X : Fin n → H →L[ℂ] H) (c : Fin n → Fin m → ℂ) :
    reparam c (wordMoment τ X) = wordMoment τ (fun b => ∑ a, c a b • X a) := by
  let Y := fun b => ∑ a, c a b • X a
  have hh (w : List (Fin m)) (A : H →L[ℂ] H) :
      reparam c (fun v => trace τ (A * wordEval X v)) w = trace τ (A * wordEval Y w) := by
    induction w generalizing A with
    | nil => simp [wordEval]
    | cons b w ih =>
      rw [reparam_cons]
      have hf (a : Fin n) : deriv a (fun v => trace τ (A * wordEval X v)) =
          (fun v => trace τ ((A * X a) * wordEval X v)) := by
        funext v; simp [FreeSeries.deriv, wordEval, mul_assoc]
      simp only [hf, ih]
      change _ = trace τ (A * (Y b * wordEval Y w))
      rw [← mul_assoc]
      dsimp only [Y]
      rw [Finset.mul_sum, Finset.sum_mul, trace_sum]
      apply sum_congr rfl
      intro a _
      simp only [mul_smul_comm, smul_mul_assoc, trace_smul]
  funext w
  change reparam c (fun v => trace τ (wordEval X v)) w = trace τ (wordEval Y w)
  simpa only [one_mul] using hh w 1

 theorem pairDerivative_eq {n : ℕ} (M : Series (Fin n)) (i : Fin n) (w : List (Fin n)) :
    conv M (subst M (letter i)) w = ∑ r : Fin w.length, if w[r.val] = i then
      M (w.take r.val) * M (w.drop (r.val+1)) else 0 := by
  rw [← deriv_quadratic i, ← subst_cons]
  exact quadratic_subst_derivative M i w
 theorem derivativeMoment_series {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (i : Fin n) :
    (fun w => derivativeMoment τ X i w) =
      conv (wordMoment τ X) (subst (wordMoment τ X) (letter i)) := by
  funext w
  rw [pairDerivative_eq]
  rfl

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Signal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation

namespace FreeTensor

variable {B N A : Type} [DecidableEq B] [DecidableEq N] [AddCommGroup A]
  [Fintype A] [DecidableEq A]

omit [Fintype A] in
 theorem groupUnitary_add (a b : A) :
    groupUnitary (B := B) (N := N) (a + b) = groupUnitary a * groupUnitary b :=
  unitaryG_mul _ _

 theorem groupUnitary_mul_characterProjection (a : A) (ψ : AddChar A ℂ) :
    groupUnitary (B := B) (N := N) a * characterProjection ψ = ψ a • characterProjection ψ := by
  unfold characterProjection
  rw [mul_smul_comm, Finset.mul_sum, smul_comm (ψ a)]
  congr 1
  rw [Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.addLeft a)
  intro b
  rw [mul_smul_comm]
  change ψ (-b) • (groupUnitary (B := B) (N := N) a * groupUnitary b) =
    ψ a • (ψ (-(a + b)) • groupUnitary (a + b))
  simp only [← groupUnitary_add, smul_smul]
  congr 1
  rw [neg_add, AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel]
  simp

 theorem characterProjection_mul (ψ φ : AddChar A ℂ) :
    characterProjection (B := B) (N := N) ψ * characterProjection φ =
      if ψ = φ then characterProjection ψ else 0 := by
  classical
  rw [characterProjection, smul_mul_assoc, Finset.sum_mul]
  simp only [smul_mul_assoc, groupUnitary_mul_characterProjection, smul_smul,
    ← Finset.sum_smul]
  have hs : (∑ a : A, ψ (-a) * φ a) = if ψ = φ then (Fintype.card A : ℂ) else 0 := by
    have he (a : A) : ψ (-a) * φ a = (-ψ + φ) a := by
      simp [AddChar.add_apply, AddChar.neg_apply, AddChar.map_neg_eq_inv]
    simp_rw [he]
    rw [AddChar.sum_eq_ite]
    congr 1
    exact propext neg_add_eq_zero
  rw [hs]
  by_cases h : ψ = φ
  · subst φ
    simp [Fintype.card_ne_zero, characterProjection]
  · simp only [h, ↓reduceIte, mul_zero,
      zero_smul ℂ (characterProjection (B := B) (N := N) φ)]

 theorem sum_characterProjection :
    ∑ ψ : AddChar A ℂ, characterProjection (B := B) (N := N) ψ = 1 := by
  classical
  unfold characterProjection
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [← Finset.sum_smul, AddChar.sum_apply_eq_ite, neg_eq_zero]
  simp [smul_smul, Fintype.card_ne_zero]

omit [Fintype A] in
 theorem trace_groupUnitary (a : A) :
    trace (tracialVector B N (Multiplicative A)) (groupUnitary a) = if a = 0 then 1 else 0 := by
  rw [trace_unitaryG]
  rfl

 theorem trace_characterProjection (ψ : AddChar A ℂ) :
    trace (tracialVector B N (Multiplicative A)) (characterProjection ψ) =
      (Fintype.card A : ℂ)⁻¹ := by
  rw [characterProjection, trace_smul, trace_sum]
  simp [trace_smul, trace_groupUnitary]

 theorem spectralSignal_pow (y : AddChar A ℂ → ℝ) (k : ℕ) :
    spectralSignal (B := B) (N := N) y ^ k = ∑ ψ, ((y ψ : ℂ) ^ k) • characterProjection ψ := by
  classical
  induction k with
  | zero => simpa using (sum_characterProjection (B := B) (N := N) (A := A)).symm
  | succ k ih =>
    rw [pow_succ, ih, spectralSignal, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ψ _
    rw [smul_mul_assoc, Finset.mul_sum]
    simp only [mul_smul_comm, characterProjection_mul]
    simp only [smul_ite, smul_zero (M := ℂ) (A := Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A)),
      Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, smul_smul, pow_succ]

 theorem trace_spectralSignal_pow (y : AddChar A ℂ → ℝ) (k : ℕ) :
    trace (tracialVector B N (Multiplicative A)) (spectralSignal y ^ k) =
      (Fintype.card A : ℂ)⁻¹ * ∑ ψ, (y ψ : ℂ) ^ k := by
  rw [spectralSignal_pow, trace_sum]
  simp only [trace_smul, trace_characterProjection, ← Finset.sum_mul]
  exact mul_comm _ _

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

omit [Group G] in
theorem signalSlice_semicircular [Group G] (g : G) (b : B) :
    (semicircularB b).comp (signalSlice (N := N) g) =
      (signalSlice g).comp (Fock.semicircular b) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change semicircularB b (signalSlice g (lp.single 2 w z)) =
    signalSlice g (Fock.semicircular b (lp.single 2 w z))
  rw [signalSlice_single]
  cases w with
  | nil => simp [semicircularB, creationB_single, annihilationB_single, removeB, leftB]
  | cons c w =>
    simp only [semicircularB, add_apply, creationB_single, annihilationB_single, removeB,
      Fock.semicircular_single_cons, map_add, signalSlice_single, leftB]
    by_cases h : b = c <;> simp [h]

 theorem signalSlice_word (g : G) (w : List B) :
    ((w.map (semicircularB (N := N) (G := G))).prod).comp (signalSlice g) =
      (signalSlice g).comp ((w.map Fock.semicircular).prod) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    apply ContinuousLinearMap.ext
    intro x
    have hi := congrArg (fun T : Fock.Space B →L[ℂ] Space B N G => T x) ih
    have hc := congrArg (fun T : Fock.Space B →L[ℂ] Space B N G =>
      T ((w.map Fock.semicircular).prod x)) (signalSlice_semicircular (N := N) g b)
    simp only [ContinuousLinearMap.comp_apply] at hi hc
    simpa only [ContinuousLinearMap.comp_apply, List.map_cons, List.prod_cons,
      mul_apply_eq_comp, hi] using hc

 theorem signalSlice_vacuum_coefficient (g : G) (x : Fock.Space B) :
    inner ℂ (basis (empty : Word B N G)) (signalSlice g x) =
      if g = 1 then inner ℂ (Fock.basisVector []) x else 0 := by
  have h : (innerSL ℂ (basis (empty : Word B N G))).comp (signalSlice g) =
      if g = 1 then innerSL ℂ (Fock.basisVector ([] : List B)) else 0 := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro v
    apply ContinuousLinearMap.ext
    intro z
    by_cases hg : g = 1 <;> by_cases hv : v = [] <;>
      simp [hg, hv, basis, empty, Fock.basisVector, lp.inner_single_left, lp.single_apply, eq_comm]
  have hx := congrArg (fun f : Fock.Space B →L[ℂ] ℂ => f x) h
  by_cases hg : g = 1 <;> simpa [hg] using hx

theorem tensor_word_moment (w : List B) (g : G) :
    trace (tracialVector B N G) ((w.map semicircularB).prod * unitaryG g) =
      trace (Fock.tracialVector B) ((w.map Fock.semicircular).prod) *
        (if g = 1 then 1 else 0) := by
  change inner ℂ (basis (empty : Word B N G))
    (((w.map (semicircularB (N := N) (G := G))).prod * unitaryG (B := B) (N := N) g) (basis empty)) = _
  rw [mul_apply_eq_comp, unitaryG_basis]
  have hv : basis (leftG g (empty : Word B N G)) = signalSlice g (Fock.basisVector []) := by
    simp [leftG, empty]
  rw [hv, ← ContinuousLinearMap.comp_apply, signalSlice_word,
    ContinuousLinearMap.comp_apply, signalSlice_vacuum_coefficient]
  by_cases hg : g = 1 <;> simp [hg, trace, Fock.tracialVector]

 theorem unitaryG_commutes_creationB (g : G) (b : B) :
    Commute (unitaryG (N := N) g) (creationB b) := by
  apply LabelHilbert.lift_commute
  intro w
  rfl

 theorem unitaryG_commutes_semicircularB (g : G) (b : B) :
    Commute (unitaryG (N := N) g) (semicircularB b) := by
  apply (unitaryG_commutes_creationB g b).add_right
  simpa using (unitaryG_commutes_creationB (N := N) g⁻¹ b).star_star

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EquidiscreteSignal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation

 theorem equidiscreteAtom_abs_le {p : ℕ} (hp : 2 ≤ p) (l : Fin p) :
    |equidiscreteAtom p l| ≤ 1 := by
  have hd : 0 < (p : ℝ) - 1 := by
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hl : (l.val : ℝ) ≤ (p : ℝ) - 1 := by
    have hn : l.val + 1 ≤ p := l.isLt
    exact_mod_cast (show (l.val : ℤ) ≤ (p : ℤ) - 1 by omega)
  rw [abs_le, equidiscreteAtom]
  constructor
  · have h := div_nonneg (show 0 ≤ 2 * (l.val : ℝ) by positivity) hd.le
    linarith
  · have h : 2 * (l.val : ℝ) / ((p : ℝ) - 1) ≤ 2 := (div_le_iff₀ hd).mpr (by linarith)
    linarith

namespace FreeTensor
variable {B N : Type} [DecidableEq B] [DecidableEq N] (p : ℕ) [NeZero p]

 theorem equidiscreteSignal_moments (k : ℕ) :
    trace (tracialVector B N (Multiplicative (ZMod p))) (equidiscreteSignal p ^ k) =
      (p : ℂ)⁻¹ * ∑ l : Fin p, (equidiscreteAtom p l : ℂ) ^ k := by
  rw [equidiscreteSignal, trace_spectralSignal_pow]
  simp only [ZMod.card]
  congr 1
  exact (dualIndex p).sum_comp (fun l => (equidiscreteAtom p l : ℂ) ^ k)

 theorem characterProjection_mem_background {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (J : Set N) (ψ : AddChar A ℂ) :
    characterProjection (B := B) (N := N) ψ ∈ backgroundAlgebra J := by
  apply (backgroundAlgebra J).smul_mem
  apply (backgroundAlgebra J).sum_mem
  intro a _
  apply (backgroundAlgebra J).smul_mem
  exact Algebra.subset_adjoin (Or.inl (Or.inr ⟨Multiplicative.ofAdd a,rfl⟩))

 theorem equidiscreteSignal_mem_background (J : Set N) :
    equidiscreteSignal (B := B) (N := N) p ∈ backgroundAlgebra J := by
  apply (backgroundAlgebra J).sum_mem
  intro ψ _
  exact (backgroundAlgebra J).smul_mem (characterProjection_mem_background J ψ) _

 theorem characterProjection_commutes_B {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (ψ : AddChar A ℂ) (b : B) :
    Commute (characterProjection (B := B) (N := N) ψ) (semicircularB b) := by
  apply Commute.smul_left
  apply Commute.sum_left
  intro a _
  exact (unitaryG_commutes_semicircularB (Multiplicative.ofAdd a) b).smul_left _

 theorem equidiscreteSignal_commutes_B (b : B) :
    Commute (equidiscreteSignal (B := B) (N := N) p) (semicircularB b) := by
  apply Commute.sum_left
  intro ψ _
  exact (characterProjection_commutes_B ψ b).smul_left _

 theorem tensor_characterProjection_moment {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (w : List B) (ψ : AddChar A ℂ) :
    trace (tracialVector B N (Multiplicative A))
      ((w.map semicircularB).prod * characterProjection ψ) =
      trace (Fock.tracialVector B) ((w.map Fock.semicircular).prod) * (Fintype.card A : ℂ)⁻¹ := by
  simp only [characterProjection, mul_smul_comm, Finset.mul_sum, trace_smul, trace_sum,
    groupUnitary, tensor_word_moment]
  have hi (a : A) : (Multiplicative.ofAdd a = (1 : Multiplicative A)) ↔ a = 0 := Iff.rfl
  simp only [hi]
  simp
  ring

 theorem tensor_equidiscrete_moment (w : List B) (k : ℕ) :
    trace (tracialVector B N (Multiplicative (ZMod p)))
      ((w.map semicircularB).prod * equidiscreteSignal p ^ k) =
      trace (Fock.tracialVector B) ((w.map Fock.semicircular).prod) *
        ((p : ℂ)⁻¹ * ∑ l : Fin p, (equidiscreteAtom p l : ℂ) ^ k) := by
  rw [equidiscreteSignal, spectralSignal_pow, Finset.mul_sum, trace_sum]
  simp only [mul_smul_comm, trace_smul, tensor_characterProjection_moment, ZMod.card]
  rw [← Finset.sum_mul]
  have hs := (dualIndex p).sum_comp (fun l => (equidiscreteAtom p l : ℂ) ^ k)
  change _ = _ at hs
  rw [hs]
  ring

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.ActualTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem semicircularN_selfAdjoint (i : N) : IsSelfAdjoint (semicircularN (B := B) (G := G) i) :=
  IsSelfAdjoint.add_star_self (creationN (B := B) (G := G) i)

 theorem backgroundAlgebra_le (J : Set N) :
    backgroundAlgebra (B := B) (G := G) J ≤ (algebra B N G).toStarSubalgebra.toSubalgebra := by
  apply Algebra.adjoin_le
  rintro _ ((⟨b,rfl⟩ | ⟨g,rfl⟩) | ⟨i,_,rfl⟩)
  · exact semicircularB_mem b
  · exact unitaryG_mem g
  · exact semicircularN_mem i

 theorem semicircularB_mem_background (J : Set N) (b : B) :
    semicircularB (N := N) (G := G) b ∈ backgroundAlgebra J :=
  Algebra.subset_adjoin (Or.inl (Or.inl ⟨b,rfl⟩))

end FreeTensor

namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]

omit [NeZero p] in
theorem initialIndex_injective [NeZero p] : Function.Injective (initialIndex p) := Fin.castAdd_injective (p+1) (p+1)

 theorem C_mem_background (J : Set (Fin ((p+1)+(p+1)))) (i : Fin (p+1)) :
    C p i ∈ backgroundAlgebra J := by
  induction i using Fin.lastCases with
  | last => rw [C_last]; exact equidiscreteSignal_mem_background p J
  | cast i => rw [C_castSucc]; exact semicircularB_mem_background J i

end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MixedGaussianSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {n : ℕ}
 theorem rightIndex_injective : Function.Injective (rightIndex (n := n)) := Fin.natAdd_injective n n
 theorem leftIndex_ne_rightIndex (i j : Fin n) : leftIndex i ≠ rightIndex j := by
  intro h
  have hh := congrArg Fin.val h
  simp [leftIndex, rightIndex] at hh
  have hi := i.isLt
  omega
 theorem joint_cases (j : Fin (n+n)) : (∃i, j=leftIndex i) ∨ (∃i, j=rightIndex i) := by
  induction j using Fin.addCases with
  | left i => exact Or.inl ⟨i,rfl⟩
  | right i => exact Or.inr ⟨i,rfl⟩
end FreeSeries

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {n : ℕ}
 theorem jointTuple_mem (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J) (σ : Fin n → N) (j : Fin (n+n)) :
    jointTuple X σ j ∈ algebra B N G := by
  rcases joint_cases j with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · rw [jointTuple_left]; exact backgroundAlgebra_le J (hX i)
  · rw [jointTuple_right]; exact semicircularN_mem _
 theorem jointTuple_noise_deriv (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) (i : Fin n) :
    FreeSeries.deriv (rightIndex i) (wordMoment (tracialVector B N G) (jointTuple X σ)) =
      conv (wordMoment (tracialVector B N G) (jointTuple X σ))
        (subst (wordMoment (tracialVector B N G) (jointTuple X σ)) (letter (rightIndex i))) := by
  let Z := jointTuple X σ
  let τ := tracialVector B N G
  have hc (j : Fin (n+n)) : star (rightCreationN (σ i)) * Z j =
      Z j * star (rightCreationN (σ i)) + if j=rightIndex i then (1:ℂ) • vacuumRankOne τ else 0 := by
    rcases joint_cases j with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · simpa [Z, leftIndex_ne_rightIndex] using (rightAnnihilationN_background (hs i) (hX k)).eq
    · have he : σ i = σ k ↔ rightIndex k = rightIndex i := by
        rw [hσ.eq_iff, rightIndex_injective.eq_iff, eq_comm]
      simpa [Z, he] using rightAnnihilationN_semicircularN (B := B) (G := G) (σ i) (σ k)
  funext w
  rw [← derivativeMoment_series]
  have h := commutator_integration_by_parts τ Z (star (rightCreationN (σ i)))
    (rightIndex i) 1 hc (by simp [τ, tracialVector, basis, empty]) w
  simp only [star_star, one_mul] at h
  have hv : rightCreationN (σ i) τ.vacuum = semicircularN (σ i) τ.vacuum := by
    simp [τ, tracialVector, semicircularN, basis, rightCreationN_single, creationN_single,
      annihilationN_single, removeN, rightN_eq_append, empty, append, leftN, push]
  rw [hv, ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    (semicircularN_selfAdjoint (B := B) (G := G) (σ i)).star_eq] at h
  change trace τ (semicircularN (σ i) * wordEval Z w) = _ at h
  simpa [FreeSeries.deriv, wordMoment, wordEval, Z] using h

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.HeatCumulants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {n : ℕ}
 theorem heat_linear_tuple (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (σ : Fin n → N) (u : ℝ) :
    (fun i => ∑ j, heatCoefficients u j i • jointTuple X σ j) =
      heatTuple X (fun i => semicircularN (σ i)) u := by
  funext i
  rw [Fin.sum_univ_add]
  change (∑ j : Fin n, heatCoefficients u (leftIndex j) i • jointTuple X σ (leftIndex j)) +
    (∑ j : Fin n, heatCoefficients u (rightIndex j) i • jointTuple X σ (rightIndex j)) = _
  simp only [heatCoefficients_left, heatCoefficients_right, jointTuple_left,
    jointTuple_right, ite_smul, one_smul,
    zero_smul ℂ (A := Space B N G →L[ℂ] Space B N G), Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, heatTuple]

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixReparam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
namespace FiniteEntropySeparation
open FreeSeries
 theorem reparam_matrixTraceWord {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {d : ℕ}
    (X : α → Matrix (Fin d) (Fin d) ℂ) (c : α → β → ℂ) :
    reparam c (matrixTraceWord X) = matrixTraceWord (fun b => ∑ a, c a b • X a) := by
  let Y := fun b => ∑ a, c a b • X a
  have hh (w : List β) (A : Matrix (Fin d) (Fin d) ℂ) :
      reparam c (fun v => (d:ℂ)⁻¹*Matrix.trace (A * matrixWord X v)) w = (d:ℂ)⁻¹*Matrix.trace (A * matrixWord Y w) := by
    induction w generalizing A with
    | nil => simp [matrixWord]
    | cons b w ih =>
      rw [reparam_cons]
      have hf (a : α) : deriv a (fun v => (d:ℂ)⁻¹*Matrix.trace (A * matrixWord X v)) =
          (fun v => (d:ℂ)⁻¹*Matrix.trace ((A * X a) * matrixWord X v)) := by
        funext v; simp [FreeSeries.deriv, matrixWord, mul_assoc]
      simp only [hf, ih]
      change _ = (d:ℂ)⁻¹*Matrix.trace (A * (Y b * matrixWord Y w))
      rw [← mul_assoc]
      dsimp only [Y]
      rw [Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum,Finset.mul_sum]
      apply sum_congr rfl
      intro a _
      simp only [mul_smul_comm, smul_mul_assoc, Matrix.trace_smul,smul_eq_mul]
      ring
  funext w
  change reparam c (fun v => (d:ℂ)⁻¹*Matrix.trace (matrixWord X v)) w = _
  simpa only [one_mul,Y,matrixTraceWord] using hh w 1
 theorem jointFinMatrix_trace {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (x : MatrixIndex n d → ℝ) (w : List (Fin (n+n))) :
    matrixTraceWord (jointFinMatrix A x) w = matrixTraceWord (jointMatrix A x) (w.map finSumFinEquiv.symm) := by
  rw [matrixTraceWord_map]
  congr 1
  funext j
  obtain ⟨a,rfl⟩ := finSumFinEquiv.surjective j
  cases a with
  | inl i => simp only [Function.comp_apply,finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_apply_left,jointFinMatrix,Fin.addCases_left,jointMatrix,Sum.elim_inl]
  | inr i => simp only [Function.comp_apply,finSumFinEquiv_symm_apply_natAdd,finSumFinEquiv_apply_right,jointFinMatrix,Fin.addCases_right,jointMatrix,Sum.elim_inr]
 theorem heatMatrix_linear {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (u : ℝ) (x : MatrixIndex n d → ℝ) :
    (fun i => ∑ j, heatCoefficients u j i • jointFinMatrix A x j)=heatMatrix A u x := by
  funext i
  rw [Fin.sum_univ_add]
  simp only [jointFinMatrix,Fin.addCases_left,Fin.addCases_right]
  change (∑ j:Fin n,heatCoefficients u (leftIndex j) i • A j)+
    (∑ j:Fin n,heatCoefficients u (rightIndex j) i • gueMatrix x j)=_
  simp [heatMatrix,ite_smul]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUEConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Classical Topology
namespace FiniteEntropySeparation
 theorem complex_mean_square_bound {ι : Type u1} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (z : ℂ) :
    (∫ x, ‖f x-z‖^2 ∂productGaussian ι) ≤
        2*(∫ x, ‖f x-∫ y, f y ∂productGaussian ι‖^2 ∂productGaussian ι)+2*‖(∫ y, f y ∂productGaussian ι)-z‖^2 := by
  let a := ∫ y, f y ∂productGaussian ι
  have hg := (hf.sub (IsComplexPolynomial.const a)).norm_sq.integrable
  calc
    _ ≤ ∫ x, 2*‖f x-a‖^2+2*‖a-z‖^2 ∂productGaussian ι := by
      apply integral_mono ((hf.sub (IsComplexPolynomial.const z)).norm_sq.integrable) ((hg.const_mul 2).add (integrable_const _))
      intro x
      have ht : ‖f x-z‖ ≤ ‖f x-a‖+‖a-z‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (f x-a) (a-z)
      have hp := pow_le_pow_left₀ (norm_nonneg _) ht 2
      change ‖f x-z‖^2 ≤ 2*‖f x-a‖^2+2*‖a-z‖^2
      nlinarith [sq_nonneg (‖f x-a‖-‖a-z‖)]
    _ = _ := by rw [integral_add (hg.const_mul _) (integrable_const _),integral_const_mul]; simp [a]
 theorem real_tendsto_zero_of_inv_sq {D : ℕ → ℕ} (hD : Tendsto D atTop atTop) (C : ℝ) :
    Tendsto (fun k => C/(D k:ℝ)^2) atTop (𝓝 0) := by
  have hc : Tendsto (fun k => (D k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hD
  have hi := tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0) |>.comp hc)
  simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hi
 theorem matrixTraceWord_mean_square_tendsto {α : Type u2} {n : ℕ} {D : ℕ → ℕ}
    (hD0 : ∀ k,0<D k) (hD : Tendsto D atTop atTop)
    (A : (k : ℕ) → α → Matrix (Fin (D k)) (Fin (D k)) ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ k a, matrixOpNorm (A k a) ≤ R) (w : List (α ⊕ Fin n)) {z : ℂ}
    (hm : Tendsto (fun k => expectedMatrixWord A k w) atTop (𝓝 z)) :
    Tendsto (fun k => ∫ x, ‖matrixTraceWord (jointMatrix (A k) x) w-z‖^2 ∂productGaussian (MatrixIndex n (D k))) atTop (𝓝 0) := by
  have hvar : Tendsto (fun k => ∫ x, ‖matrixTraceWord (jointMatrix (A k) x) w-expectedMatrixWord A k w‖^2 ∂productGaussian (MatrixIndex n (D k))) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => integral_nonneg (fun _ => sq_nonneg _))
      (fun k => (matrixTraceWord_variance_bound (hD0 k) (A k) hR (hA k) w).trans_eq (by ring))
      (real_tendsto_zero_of_inv_sq hD ((w.length:ℝ)^2*jointMomentBound n R (2*(w.length-1))))
  have hb : Tendsto (fun k => 2*(∫ x, ‖matrixTraceWord (jointMatrix (A k) x) w-expectedMatrixWord A k w‖^2 ∂productGaussian (MatrixIndex n (D k)))+2*‖expectedMatrixWord A k w-z‖^2) atTop (𝓝 0) := by
    have hh := (hvar.const_mul 2).add (((hm.sub_const z).norm.pow 2).const_mul 2)
    simpa using hh
  exact squeeze_zero (fun k => integral_nonneg (fun _ => sq_nonneg _))
    (fun k => complex_mean_square_bound (matrixTraceWord_polynomial (A k) w) z) hb
 theorem probability_error_le_mean_square {Ω : Type u3} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℂ} {z : ℂ} {ε : ℝ} (hε : 0 < ε) (hi : Integrable (fun x => ‖f x-z‖^2) μ) :
    μ.real {x | ε ≤ ‖f x-z‖} ≤ (∫ x, ‖f x-z‖^2 ∂μ)/ε^2 := by
  have he : {x | ε ≤ ‖f x-z‖} = {x | ε^2 ≤ ‖f x-z‖^2} := by
    ext x; simp only [Set.mem_ofPred_eq]; exact (sq_le_sq₀ hε.le (norm_nonneg _)).symm
  rw [he]
  exact (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by
    simpa [mul_comm] using mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (fun x => sq_nonneg ‖f x-z‖)) hi (ε^2))
 theorem matrixTraceWord_probability_tendsto {α : Type u4} {n : ℕ} {D : ℕ → ℕ}
    (hD0 : ∀ k,0<D k) (hD : Tendsto D atTop atTop)
    (A : (k : ℕ) → α → Matrix (Fin (D k)) (Fin (D k)) ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ k a, matrixOpNorm (A k a) ≤ R) (w : List (α ⊕ Fin n)) {z : ℂ}
    (hm : Tendsto (fun k => expectedMatrixWord A k w) atTop (𝓝 z)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (productGaussian (MatrixIndex n (D k))).real {x | ε ≤ ‖matrixTraceWord (jointMatrix (A k) x) w-z‖}) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => measureReal_nonneg)
    (fun k => probability_error_le_mean_square _ hε ((matrixTraceWord_polynomial (A k) w).sub (IsComplexPolynomial.const z)).norm_sq.integrable)
  simpa using (matrixTraceWord_mean_square_tendsto hD0 hD A hR hA w hm).div_const (ε^2)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianL2Limit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Topology
namespace FiniteEntropySeparation
 theorem norm_sum_sq_le_card {ι : Type u1} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖^2 ≤ (s.card:ℝ) * ∑ i ∈ s, ‖f i‖^2 := by
  calc
    _ ≤ (∑ i ∈ s, ‖f i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖f i‖))
 theorem polynomial_sum_L2_tendsto {I : ℕ → Type} [∀ k,Fintype (I k)] [∀ k,DecidableEq (I k)]
    {α : Type u2} (s : Finset α) (F : (k:ℕ) → α → (I k → ℝ) → ℂ)
    (hF : ∀ k a,IsComplexPolynomial (F k a))
    (hlim : ∀ a ∈ s,Tendsto (fun k => ∫ x, ‖F k a x‖^2 ∂productGaussian (I k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖∑ a ∈ s,F k a x‖^2 ∂productGaussian (I k)) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => integral_nonneg (fun _ => sq_nonneg _))
    (fun k => ?_) (by simpa using (tendsto_finsetSum s hlim).const_mul (s.card:ℝ))
  rw [← integral_finsetSum s (fun a _ => (hF k a).norm_sq.integrable),← integral_const_mul]
  apply integral_mono ((IsComplexPolynomial.finset_sum s (fun a _ => hF k a)).norm_sq.integrable)
    ((integrable_finsetSum s (fun a _ => (hF k a).norm_sq.integrable)).const_mul _)
  intro x
  exact norm_sum_sq_le_card s _
 theorem polynomial_const_mul_L2_tendsto {I : ℕ → Type} [∀ k,Fintype (I k)] [∀ k,DecidableEq (I k)]
    (F : (k:ℕ) → (I k → ℝ) → ℂ) (c : ℂ)
    (hlim : Tendsto (fun k => ∫ x, ‖F k x‖^2 ∂productGaussian (I k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖c*F k x‖^2 ∂productGaussian (I k)) atTop (𝓝 0) := by
  simp only [norm_mul,mul_pow,integral_const_mul]
  simpa using hlim.const_mul (‖c‖^2)
namespace FreeSeries
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem reparam_polynomial [DecidableEq α] [Fintype β] [DecidableEq β] {ι : Type u3} [Fintype ι] [DecidableEq ι]
    (c : α → β → ℂ) (F : (ι → ℝ) → Series α) (hF : ∀ w,IsComplexPolynomial (fun x => F x w))
    (w : List β) : IsComplexPolynomial (fun x => reparam c (F x) w) := by
  induction w generalizing F with
  | nil => exact hF []
  | cons b w ih =>
    exact IsComplexPolynomial.finset_sum univ (fun a _ => (ih (fun x => deriv a (F x)) (fun v => hF (a::v))).const_mul (c a b))
 theorem reparam_L2_tendsto {I : ℕ → Type} [∀ k,Fintype (I k)] [∀ k,DecidableEq (I k)]
    (c : α → β → ℂ) (F : (k:ℕ) → (I k → ℝ) → Series α) (M : Series α)
    (hF : ∀ k w,IsComplexPolynomial (fun x => F k x w))
    (hlim : ∀ w,Tendsto (fun k => ∫ x, ‖F k x w-M w‖^2 ∂productGaussian (I k)) atTop (𝓝 0))
    (w : List β) :
    Tendsto (fun k => ∫ x, ‖reparam c (F k x) w-reparam c M w‖^2 ∂productGaussian (I k)) atTop (𝓝 0) := by
  induction w generalizing F M with
  | nil => exact hlim []
  | cons b w ih =>
    simp only [reparam_cons,← Finset.sum_sub_distrib,← mul_sub]
    apply polynomial_sum_L2_tendsto
    · intro k a
      exact ((reparam_polynomial c (fun x => deriv a (F k x)) (fun v => hF k (a::v)) w).sub (IsComplexPolynomial.const _)).const_mul _
    · intro a _
      apply polynomial_const_mul_L2_tendsto
      exact ih (fun k x => deriv a (F k x)) (deriv a M) (fun k v => hF k (a::v)) (fun v => hlim (a::v))
end FreeSeries
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUEFreeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Classical Topology
namespace FiniteEntropySeparation
open FreeSeries
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {n : ℕ}
 theorem sumJointMoment_cyclic (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J) (σ : Fin n → N) (u v : List (Fin n ⊕ Fin n)) :
    sumJointMoment X σ (u++v)=sumJointMoment X σ (v++u) := by
  simp only [sumJointMoment,List.map_append]
  exact (wordMoment_cyclic (tracialVector B N G) _ (jointTuple_mem J X hX σ)).append _ _
 theorem sumJointMoment_left (X : Fin n → Space B N G →L[ℂ] Space B N G) (σ : Fin n → N) (u : List (Fin n)) :
    sumJointMoment X σ (u.map Sum.inl)=wordMoment (tracialVector B N G) X u := by
  simp only [sumJointMoment,wordMoment,wordEval,List.map_map]
  congr 3
  funext i
  exact jointTuple_left X σ i
 theorem sumJointMoment_noise (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J) (σ : Fin n → N) (hσ : Function.Injective σ)
    (hs : ∀ i, σ i ∉ J) (i : Fin n) (w : List (Fin n ⊕ Fin n)) :
    sumJointMoment X σ (Sum.inr i::w)= ∑ r : Fin w.length,
      if w[r.val]=Sum.inr i then sumJointMoment X σ (w.take r.val)*sumJointMoment X σ (w.drop (r.val+1)) else 0 := by
  have h := congrFun (jointTuple_noise_deriv J X hX σ hσ hs i) (w.map finSumFinEquiv)
  rw [← derivativeMoment_series] at h
  change wordMoment (tracialVector B N G) (jointTuple X σ) (rightIndex i::w.map finSumFinEquiv)=_ at h
  change wordMoment (tracialVector B N G) (jointTuple X σ) (rightIndex i::w.map finSumFinEquiv) = _
  rw [h]
  dsimp only
  simp only [derivativeMoment]
  apply Fintype.sum_equiv (finCongr (List.length_map (as := w) finSumFinEquiv))
  intro r
  simp only [finCongr_apply, Fin.val_cast, List.getElem_map, ← List.map_take, ← List.map_drop]
  have he : finSumFinEquiv w[r.val] = rightIndex i ↔ w[r.val]=Sum.inr i :=
    by change finSumFinEquiv w[r.val] = finSumFinEquiv (Sum.inr i) ↔ _; exact finSumFinEquiv.injective.eq_iff
  simp only [he,sumJointMoment]
 theorem expectedMatrixWord_free_tendsto {D : ℕ → ℕ} (hD0 : ∀ k,0<D k) (hD : Tendsto D atTop atTop)
    (A : (k : ℕ) → Fin n → Matrix (Fin (D k)) (Fin (D k)) ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ k i, matrixOpNorm (A k i) ≤ R)
    (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (hbase : ∀ u, Tendsto (fun k => matrixTraceWord (A k) u) atTop (𝓝 (wordMoment (tracialVector B N G) X u)))
    (w : List (Fin n ⊕ Fin n)) :
    Tendsto (fun k => expectedMatrixWord A k w) atTop (𝓝 (sumJointMoment X σ w)) := by
  apply expectedMatrixWord_tendsto hD0 hD A hR hA _ (sumJointMoment_cyclic J X hX σ)
  · intro u
    simpa only [sumJointMoment_left] using hbase u
  · intro i v
    classical
    exact (sumJointMoment_noise J X hX σ hσ hs i v).trans (by
      apply sum_congr rfl
      intro r _
      split_ifs <;> rfl)
end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixHeatLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology
namespace FiniteEntropySeparation
open FreeSeries
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G] {n : ℕ}
 theorem heatMatrix_meanSquare_tendsto {D : ℕ → ℕ} (hD0 : ∀ k,0<D k) (hD : Tendsto D atTop atTop)
    (A : (k:ℕ) → Fin n → Matrix (Fin (D k)) (Fin (D k)) ℂ) {R : ℝ} (hR : 0≤R)
    (hA : ∀ k i,matrixOpNorm (A k i)≤R)
    (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i,X i∈backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i,σ i∉J)
    (hbase : ∀ w,Tendsto (fun k => matrixTraceWord (A k) w) atTop (𝓝 (wordMoment (tracialVector B N G) X w)))
    (u : ℝ) (w : List (Fin n)) :
    Tendsto (fun k => ∫ x, ‖matrixTraceWord (heatMatrix (A k) u x) w-
      wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) w‖^2 ∂productGaussian (MatrixIndex n (D k))) atTop (𝓝 0) := by
  have hj (v : List (Fin (n+n))) :
      Tendsto (fun k => ∫ x, ‖matrixTraceWord (jointFinMatrix (A k) x) v-
        wordMoment (tracialVector B N G) (jointTuple X σ) v‖^2 ∂productGaussian (MatrixIndex n (D k))) atTop (𝓝 0) := by
    have hm := expectedMatrixWord_free_tendsto hD0 hD A hR hA J X hX σ hσ hs hbase (v.map finSumFinEquiv.symm)
    have h := matrixTraceWord_mean_square_tendsto hD0 hD A hR hA (v.map finSumFinEquiv.symm) hm
    simpa only [← jointFinMatrix_trace,sumJointMoment,List.map_map,Function.comp_def,Equiv.apply_symm_apply,List.map_id',List.map_id_fun] using h
  have hpoly (k:ℕ) (v : List (Fin (n+n))) : IsComplexPolynomial (fun x : MatrixIndex n (D k) → ℝ => matrixTraceWord (jointFinMatrix (A k) x) v) := by
    simpa only [jointFinMatrix_trace] using matrixTraceWord_polynomial (A k) (v.map finSumFinEquiv.symm)
  have h := reparam_L2_tendsto (heatCoefficients u) (fun k x => matrixTraceWord (jointFinMatrix (A k) x))
    (wordMoment (tracialVector B N G) (jointTuple X σ)) hpoly hj w
  simpa only [reparam_matrixTraceWord,heatMatrix_linear,reparam_wordMoment,heat_linear_tuple] using h
 theorem heatMatrix_probability_tendsto {D : ℕ → ℕ} (hD0 : ∀ k,0<D k) (hD : Tendsto D atTop atTop)
    (A : (k:ℕ) → Fin n → Matrix (Fin (D k)) (Fin (D k)) ℂ) {R : ℝ} (hR : 0≤R)
    (hA : ∀ k i,matrixOpNorm (A k i)≤R)
    (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i,X i∈backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i,σ i∉J)
    (hbase : ∀ w,Tendsto (fun k => matrixTraceWord (A k) w) atTop (𝓝 (wordMoment (tracialVector B N G) X w)))
    (u : ℝ) (w : List (Fin n)) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun k => (productGaussian (MatrixIndex n (D k))).real {x | ε ≤ ‖matrixTraceWord (heatMatrix (A k) u x) w-
      wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) w‖}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun k => probability_error_le_mean_square _ hε ?_)
    (by simpa using (heatMatrix_meanSquare_tendsto hD0 hD A hR hA J X hX σ hσ hs hbase u w).div_const (ε^2))
  apply IsComplexPolynomial.norm_sq
    (IsComplexPolynomial.sub ?_ (IsComplexPolynomial.const _)) |>.integrable
  have hp := reparam_polynomial (heatCoefficients u) (fun x => matrixTraceWord (jointFinMatrix (A k) x)) (fun v => by
    simpa only [jointFinMatrix_trace] using matrixTraceWord_polynomial (A k) (v.map finSumFinEquiv.symm)) w
  simpa only [reparam_matrixTraceWord,heatMatrix_linear] using hp
end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUEFock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Classical Topology
namespace FiniteEntropySeparation
open FreeSeries
variable {n d : ℕ}
 theorem matrixTraceWord_gue_map (x : MatrixIndex n d → ℝ) (w : List (Fin n)) :
    matrixTraceWord (jointMatrix (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ)) x) (w.map Sum.inr) = matrixTraceWord (gueMatrix x) w := by
  rw [matrixTraceWord_map]
  rfl
 theorem gueTraceWord_stein_pure (hd : 0 < d) (i : Fin n) (w : List (Fin n)) :
    (∫ x, matrixTraceWord (gueMatrix x) (i::w) ∂productGaussian (MatrixIndex n d)) =
      ∑ r : Fin w.length, if w[r.val]=i then
        ∫ x, matrixTraceWord (gueMatrix x) (w.take r.val)*matrixTraceWord (gueMatrix x) (w.drop (r.val+1)) ∂productGaussian (MatrixIndex n d) else 0 := by
  have h := gueTraceWord_stein hd (fun _ : Empty => (0 : Matrix (Fin d) (Fin d) ℂ)) i (w.map Sum.inr)
  have he : Sum.inr i::w.map (Sum.inr (α := Empty)) = (i::w).map Sum.inr := rfl
  rw [he] at h
  simp only [matrixTraceWord_gue_map] at h
  rw [h]
  apply Fintype.sum_equiv (finCongr (List.length_map (as := w) (Sum.inr (α := Empty))))
  intro r
  simp only [finCongr_apply,Fin.val_cast,List.getElem_map,Sum.inr.injEq,← List.map_take,← List.map_drop,matrixTraceWord_gue_map]
 theorem gueTraceWord_expected_tendsto {D : ℕ → ℕ} (hD0 : ∀ k,0<D k) (hD : Tendsto D atTop atTop) (w : List (Fin n)) :
    Tendsto (fun k => ∫ x, matrixTraceWord (gueMatrix x) w ∂productGaussian (MatrixIndex n (D k))) atTop (𝓝 (fockMoments n w)) := by
  induction w using FreeSeries.length_induction with
  | h w ih =>
    cases w with
    | nil =>
      have he (k : ℕ) (x : MatrixIndex n (D k) → ℝ) : matrixTraceWord (gueMatrix x) [] = 1 := by
        simp [matrixTraceWord,matrixWord,ne_of_gt (hD0 k)]
      simp [he,fockMoments]
    | cons i w =>
      have hf : fockMoments n (i::w) = ∑ r : Fin w.length, if w[r.val]=i then fockMoments n (w.take r.val)*fockMoments n (w.drop (r.val+1)) else 0 :=
        Fock.semicircular_integration_by_parts i w
      simp only [gueTraceWord_stein_pure (hD0 _), hf]
      apply tendsto_finsetSum
      intro r _
      split_ifs with hr
      · have hc := matrixTraceWord_covariance_tendsto hD0 hD (fun k (_ : Empty) => (0 : Matrix (Fin (D k)) (Fin (D k)) ℂ)) (R := 0) le_rfl (by intro k a; exact a.elim) ((w.take r.val).map Sum.inr) ((w.drop (r.val+1)).map Sum.inr)
        simp only [matrixTraceWord_gue_map,expectedMatrixWord] at hc
        apply tendsto_of_sub_zero hc
        exact (ih (w.take r.val) (by simp)).mul (ih (w.drop (r.val+1)) (by simp))
      · exact tendsto_const_nhds
 theorem gueTraceWord_probability_tendsto {D : ℕ → ℕ} (hD0 : ∀ k,0<D k) (hD : Tendsto D atTop atTop)
    (w : List (Fin n)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (productGaussian (MatrixIndex n (D k))).real {x | ε ≤ ‖matrixTraceWord (gueMatrix x) w-fockMoments n w‖}) atTop (𝓝 0) := by
  have hm : Tendsto (fun k => expectedMatrixWord (fun k (_ : Empty) => (0 : Matrix (Fin (D k)) (Fin (D k)) ℂ)) k (w.map Sum.inr)) atTop (𝓝 (fockMoments n w)) := by
    simpa only [expectedMatrixWord,matrixTraceWord_gue_map] using gueTraceWord_expected_tendsto hD0 hD w
  simpa only [matrixTraceWord_gue_map] using matrixTraceWord_probability_tendsto hD0 hD _ (R := 0) le_rfl (by intro k a; exact a.elim) (w.map Sum.inr) hm hε
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GUESelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped Classical Topology
namespace FiniteEntropySeparation
 theorem gueMatrix_norm_tail64 {n d : ℕ} (hd : 0<d) (i : Fin n) :
    (productGaussian (MatrixIndex n d)).real {x | 64 < matrixOpNorm (gueMatrix x i)} ≤ 4*Real.exp (-64*(d:ℝ)) := by
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<9)
  calc
    _ ≤ 4*9^(4*d)*Real.exp (-((d:ℝ)*64^2)/32) := gueMatrix_norm_tail hd i (by norm_num)
    _ = 4*Real.exp ((4*(d:ℝ))*Real.log 9 - (d:ℝ)*64^2/32) := by
      rw [show (9:ℝ)^(4*d)=Real.exp ((4*(d:ℝ))*Real.log 9) by rw [show 4*(d:ℝ)=((4*d:ℕ):ℝ) by push_cast; rfl, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<9)]]
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ _ := by
      gcongr
      have hd' : 0 ≤ (d:ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonneg hd' (show 0 ≤ 8-Real.log 9 by linarith)]
 theorem gueMatrix_norm_probability_tendsto {n : ℕ} {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop) (i : Fin n) :
    Tendsto (fun k => (productGaussian (MatrixIndex n (D k))).real {x | 64 < matrixOpNorm (gueMatrix x i)}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun k => gueMatrix_norm_tail64 (hD0 k) i)
  have ht : Tendsto (fun k => (64:ℝ)*(D k:ℝ)) atTop atTop := (tendsto_natCast_atTop_atTop.comp hD).const_mul_atTop (by norm_num)
  simpa only [neg_mul, mul_zero,Function.comp_def] using (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul 4
 theorem gueBad_probability_tendsto (n m : ℕ) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun k => (productGaussian (MatrixIndex n (k+1))).real (gueBad n m (k+1) ε)) atTop (𝓝 0) := by
  let W := (List.finite_length_le (Fin n) m).toFinset
  have hD : Tendsto (fun k : ℕ => k+1) atTop atTop := tendsto_add_atTop_nat 1
  have hn : Tendsto (fun k => ∑ i : Fin n, (productGaussian (MatrixIndex n (k+1))).real {x | 64 < matrixOpNorm (gueMatrix x i)}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum univ (fun i _ => gueMatrix_norm_probability_tendsto (fun _ => Nat.succ_pos _) hD i)
  have hw : Tendsto (fun k => ∑ w ∈ W, (productGaussian (MatrixIndex n (k+1))).real {x | ε ≤ ‖matrixTraceWord (gueMatrix x) w-FreeSeries.fockMoments n w‖}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum W (fun w _ => gueTraceWord_probability_tendsto (fun _ => Nat.succ_pos _) hD w hε)
  apply squeeze_zero (fun k => measureReal_nonneg) _ (by simpa using hn.add hw)
  intro k
  have he : gueBad n m (k+1) ε =
      (⋃ i ∈ (univ : Finset (Fin n)), {x | 64 < matrixOpNorm (gueMatrix x i)}) ∪
      (⋃ w ∈ W, {x | ε ≤ ‖matrixTraceWord (gueMatrix x) w-FreeSeries.fockMoments n w‖}) := by
    ext x
    simp [gueBad,W]
  rw [he]
  exact (measureReal_union_le _ _).trans (add_le_add (measureReal_biUnion_finset_le _ _) (measureReal_biUnion_finset_le _ _))
 theorem exists_gue_model (n m K : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ d, K<d ∧ ∃ x : MatrixIndex n d → ℝ, (∀ i,matrixOpNorm (gueMatrix x i) ≤ 64) ∧
      ∀ w : List (Fin n), w.length ≤ m → ‖matrixTraceWord (gueMatrix x) w-FreeSeries.fockMoments n w‖ < ε := by
  have ht := (gueBad_probability_tendsto n m hε).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨k,hp⟩ := (eventually_atTop.mp ht)
  let q := max k K
  have hq : (productGaussian (MatrixIndex n (q+1))).real (gueBad n m (q+1) ε)<1 := hp q (le_max_left _ _)
  have hx : ∃ x : MatrixIndex n (q+1) → ℝ, x ∉ gueBad n m (q+1) ε := by
    by_contra hh
    have he : gueBad n m (q+1) ε = univ := by ext x; simp only [mem_univ,iff_true]; exact not_not.mp (not_exists.mp hh x)
    simp [he] at hq
  obtain ⟨x,hx⟩ := hx
  refine ⟨q+1,by dsimp [q]; omega,x,?_,?_⟩
  · intro i; by_contra hi; exact hx (Or.inl ⟨i,not_le.mp hi⟩)
  · intro w hw; by_contra hh; exact hx (Or.inr ⟨w,hw,not_lt.mp hh⟩)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MicrostatesHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped Classical Topology ENNReal
namespace FiniteEntropySeparation
 theorem hermitianMatrix_heatCoordinates {n d : ℕ} (a : MatrixCoordinates n d) (u : ℝ) (x : MatrixIndex n d → ℝ) (i : Fin n) :
    hermitianMatrix (heatCoordinates a u x) i = heatMatrix (hermitianMatrix a) u x i := by
  rw [heatCoordinates,hermitianMatrix_add,hermitianMatrix_smul]
  simp only [heatMatrix,gueMatrix,← smul_assoc,smul_eq_mul,coordinateMatrix]
  congr 1
  ext j k
  simp [Matrix.smul_apply,smul_eq_mul,Complex.real_smul,div_eq_mul_inv]
 theorem matrixMoment_heatCoordinates {n d : ℕ} (a : MatrixCoordinates n d) (u : ℝ) (x : MatrixIndex n d → ℝ) (w : List (Fin n)) :
    matrixMoment (heatCoordinates a u x) w = matrixTraceWord (heatMatrix (hermitianMatrix a) u x) w := by
  simp only [matrixMoment,matrixTraceWord,matrixWord]
  rw [show hermitianMatrix (heatCoordinates a u x)=heatMatrix (hermitianMatrix a) u x from funext (hermitianMatrix_heatCoordinates a u x)]
 theorem heatMatrix_norm_le {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) {R : ℝ}
    (hA : ∀i,matrixOpNorm (A i)≤R) (u : ℝ) (x : MatrixIndex n d → ℝ)
    (hx : ∀i,matrixOpNorm (gueMatrix x i)≤64) (i : Fin n) :
    matrixOpNorm (heatMatrix A u x i)≤R+Real.sqrt u*64 := by
  apply (matrixOpNorm_add _ _).trans
  rw [matrixOpNorm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact add_le_add (hA i) (mul_le_mul_of_nonneg_left (hx i) (Real.sqrt_nonneg _))
 variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
 theorem heat_microstates_probability {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
    (a : (k:ℕ) → MatrixCoordinates n (D k)) {R : ℝ} (hA : ∀k i,matrixOpNorm (hermitianMatrix (a k) i)≤R)
    (u : ℝ) (hMom : ∀w (ε:ℝ), 0<ε → Tendsto (fun k => (productGaussian (MatrixIndex n (D k))).real
      {x | ε≤‖matrixTraceWord (heatMatrix (hermitianMatrix (a k)) u x) w-wordMoment τ X w‖}) atTop (𝓝 0))
    (m : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k in atTop, (1/2:ℝ≥0∞) ≤ productGaussian (MatrixIndex n (D k))
      (heatCoordinates (a k) u ⁻¹' microstates τ X (R+Real.sqrt u*64) m (D k) ε) := by
  let W := (List.finite_length_le (Fin n) m).toFinset
  let E (k : ℕ) : Set (MatrixIndex n (D k) → ℝ) :=
    (⋃ i ∈ (univ : Finset (Fin n)), {x | 64 < matrixOpNorm (gueMatrix x i)}) ∪
    (⋃ w ∈ W, {x | ε≤‖matrixTraceWord (heatMatrix (hermitianMatrix (a k)) u x) w-wordMoment τ X w‖})
  have hn : Tendsto (fun k => ∑ i : Fin n, (productGaussian (MatrixIndex n (D k))).real {x | 64 < matrixOpNorm (gueMatrix x i)}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum univ (fun i _ => gueMatrix_norm_probability_tendsto hD0 hD i)
  have hw : Tendsto (fun k => ∑ w ∈ W, (productGaussian (MatrixIndex n (D k))).real {x | ε ≤ ‖matrixTraceWord (heatMatrix (hermitianMatrix (a k)) u x) w-wordMoment τ X w‖}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum W (fun w _ => hMom w ε hε)
  have ht : Tendsto (fun k => (productGaussian (MatrixIndex n (D k))).real (E k)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) _ (by simpa using hn.add hw)
    intro k
    exact (measureReal_union_le _ _).trans (add_le_add (measureReal_biUnion_finset_le _ _) (measureReal_biUnion_finset_le _ _))
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with k hk
  have hb : (E k)ᶜ ⊆ heatCoordinates (a k) u ⁻¹' microstates τ X (R+Real.sqrt u*64) m (D k) ε := by
    intro x hx
    simp only [mem_compl_iff,E,Set.mem_union,mem_iUnion,Finset.mem_univ,exists_prop,true_and,not_or,not_exists] at hx
    refine ⟨?_,?_⟩
    · intro i
      rw [hermitianMatrix_heatCoordinates]
      exact heatMatrix_norm_le _ (hA k) u x (fun i => le_of_not_gt (hx.1 i)) i
    · intro w hw
      rw [matrixMoment_heatCoordinates]
      exact lt_of_not_ge (fun hh => hx.2 w ⟨by simpa [W] using hw,hh⟩)
  apply le_trans _ (measure_mono hb)
  have hu : (1:ℝ) ≤ (productGaussian (MatrixIndex n (D k))).real (E k)+(productGaussian (MatrixIndex n (D k))).real ((E k)ᶜ) := by
    simpa [measureReal_def] using measureReal_union_le (μ := productGaussian (MatrixIndex n (D k))) (E k) (E k)ᶜ
  have hc : (1/2:ℝ) ≤ (productGaussian (MatrixIndex n (D k))).real ((E k)ᶜ) := by linarith
  rw [← ENNReal.toReal_le_toReal (by norm_num) (measure_ne_top _ _)]
  simpa [measureReal_def] using hc
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SignalSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries

section Product
variable {α A : Type} [DecidableEq α] [Monoid A]
 theorem option_word_product (B : α → A) (Y : A) (h : ∀ i, Commute Y (B i)) (w : List (Option α)) :
    (w.map (optionTuple B Y)).prod = ((w.filterMap id).map B).prod * Y^(w.count none) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    cases a with
    | none =>
      simp only [List.map_cons, List.prod_cons, optionTuple, List.filterMap_cons, id_eq, ih]
      have hc := Commute.list_prod_right ((w.filterMap id).map B) Y (by
        intro x hx
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
        exact h i)
      simp only [List.count_cons_self]
      change Y * (((w.filterMap id).map B).prod * Y ^ w.count none) = _
      rw [← mul_assoc, hc.eq, mul_assoc, pow_succ']
      rfl
    | some i => simp [optionTuple, ih, mul_assoc]
end Product

namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem signal_option_product (w : List (Option (Fin p))) :
    wordEval (C p) (w.map (optionFin p)) =
      ((w.filterMap id).map (semicircularB (N := Fin ((p+1)+(p+1))) (G := Multiplicative (ZMod p)))).prod *
        equidiscreteSignal p ^ (w.count none) := by
  unfold wordEval
  rw [List.map_map]
  have hf : (fun a => C p (optionFin p a)) = optionTuple semicircularB (equidiscreteSignal p) := by
    funext a
    cases a <;> simp [optionTuple]
  change (w.map (fun a => C p (optionFin p a))).prod = _
  rw [hf]
  exact option_word_product _ _ (equidiscreteSignal_commutes_B p) w
 theorem signal_option_moments (w : List (Option (Fin p))) :
    signalMoments p (w.map (optionFin p)) = fockMoments p (w.filterMap id) *
      trace (τ p) (equidiscreteSignal p ^ (w.count none)) := by
  unfold signalMoments wordMoment
  rw [signal_option_product, tensor_equidiscrete_moment, equidiscreteSignal_moments]
  rfl
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianAffineVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace FiniteEntropySeparation
 theorem gaussian_affine_volume {ι : Type u1} [Fintype ι] (a : EuclideanSpace ℝ ι) {r : ℝ} (hr : 0<r)
    (s : Set (EuclideanSpace ℝ ι))
    (h : (1/2:ℝ≥0∞) ≤ productGaussian ι ((fun x => a+r • WithLp.toLp 2 x) ⁻¹' s)) :
    ENNReal.ofReal (r^(Fintype.card ι)/2) ≤ volume s := by
  have hp : productGaussian ι ((fun x => a+r • WithLp.toLp 2 x) ⁻¹' s) ≤
      ENNReal.ofReal ((r^(Fintype.card ι))⁻¹)*volume s := by
    have hh := productGaussian_toLp_le_volume ι ((fun x => a+r • x) ⁻¹' s)
    have he : ((fun x : EuclideanSpace ℝ ι => a+r • x) ⁻¹' s) =
        (fun x => r • x) ⁻¹' ((fun x => a+x) ⁻¹' s) := rfl
    rw [he,Measure.addHaar_preimage_smul volume hr.ne', measure_preimage_add] at hh
    simpa only [finrank_euclideanSpace,Set.preimage_preimage,Function.comp_def,abs_of_pos (inv_pos.mpr (pow_pos hr _))] using hh
  have hm : ENNReal.ofReal (r^(Fintype.card ι)) * (1/2:ℝ≥0∞) ≤
      ENNReal.ofReal (r^(Fintype.card ι)) * (ENNReal.ofReal ((r^(Fintype.card ι))⁻¹)*volume s) := by
    gcongr; exact h.trans hp
  rw [← mul_assoc,← ENNReal.ofReal_mul (pow_nonneg hr.le _),mul_inv_cancel₀ (pow_ne_zero _ hr.ne'),ENNReal.ofReal_one,one_mul] at hm
  simpa only [div_eq_mul_inv,ENNReal.ofReal_mul (pow_nonneg hr.le _),ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2),ENNReal.ofReal_ofNat,one_mul] using hm
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MicrostatesLogLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace FiniteEntropySeparation
 theorem normalized_log_lower (n d : ℕ) (hd : 0<d) {u : ℝ} (hu : 0<u) {v : ℝ≥0∞}
    (hvtop : v≠⊤) (hv : ENNReal.ofReal ((Real.sqrt u/Real.sqrt d)^(n*d*d)/2)≤v) :
    (((n:ℝ)/2*Real.log u-Real.log 2 : ℝ):EReal) ≤
      ((((d:ℝ)^2)⁻¹:ℝ):EReal)*v.log+(((n:ℝ)/2*Real.log d:ℝ):EReal) := by
  have hd' : 0<(d:ℝ) := Nat.cast_pos.mpr hd
  have hr : 0<Real.sqrt u/Real.sqrt d := div_pos (Real.sqrt_pos.mpr hu) (Real.sqrt_pos.mpr hd')
  let q := (Real.sqrt u/Real.sqrt d)^(n*d*d)/2
  have hq : 0<q := by dsimp [q]; positivity
  have hqv : q≤v.toReal := by
    have h := ENNReal.toReal_mono hvtop hv
    rwa [ENNReal.toReal_ofReal hq.le] at h
  have hvpos : 0<v.toReal := hq.trans_le hqv
  rw [ENNReal.log_pos_real' hvpos,← EReal.coe_mul,← EReal.coe_add,EReal.coe_le_coe_iff]
  have hl : Real.log q ≤ Real.log v.toReal := Real.log_le_log hq hqv
  have he : Real.log q = (n:ℝ)*(d:ℝ)^2/2*(Real.log u-Real.log d)-Real.log 2 := by
    dsimp [q]
    rw [Real.log_div (pow_ne_zero _ hr.ne') (by norm_num),Real.log_pow,
      Real.log_div (Real.sqrt_pos.mpr hu).ne' (Real.sqrt_pos.mpr hd').ne',Real.log_sqrt hu.le,Real.log_sqrt hd'.le]
    push_cast
    ring
  rw [he] at hl
  have hmul := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr (sq_nonneg (d:ℝ)))
  have hcalc : ((d:ℝ)^2)⁻¹*((n:ℝ)*(d:ℝ)^2/2*(Real.log u-Real.log d)-Real.log 2)+
      (n:ℝ)/2*Real.log d=(n:ℝ)/2*Real.log u-Real.log 2/((d:ℝ)^2) := by
    field_simp; ring
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hh : Real.log 2/((d:ℝ)^2) ≤ Real.log 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hd')).2
    nlinarith [sq_nonneg ((d:ℝ)-1),mul_nonneg hlog (show 0≤(d:ℝ)^2-1 by nlinarith)]
  linarith
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FreeMatrixModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace FiniteEntropySeparation
 theorem gueMatrix_isHermitian {n d : ℕ} (x : MatrixIndex n d → ℝ) (i : Fin n) : (gueMatrix x i).IsHermitian := by
  change (((Real.sqrt d:ℂ)⁻¹) • hermitianMatrix (WithLp.toLp 2 x) i).IsHermitian
  simp only [Matrix.IsHermitian,Matrix.conjTranspose_smul,map_inv₀,Complex.star_def,Complex.conj_ofReal]
  rw [show (hermitianMatrix (WithLp.toLp 2 x) i).conjTranspose=hermitianMatrix (WithLp.toLp 2 x) i from hermitianMatrix_isHermitian _ _]
 theorem exists_free_matrix_models (n : ℕ) :
    ∃ (D : ℕ → ℕ) (A : (k : ℕ) → Fin n → Matrix (Fin (D k)) (Fin (D k)) ℂ),
      (∀ k,0<D k) ∧ Tendsto D atTop atTop ∧
      (∀ k i,matrixOpNorm (A k i)≤64) ∧ (∀ k i,(A k i).IsHermitian) ∧
      ∀ w : List (Fin n), Tendsto (fun k => matrixTraceWord (A k) w) atTop (𝓝 (FreeSeries.fockMoments n w)) := by
  have hex (k : ℕ) := exists_gue_model n k k (ε := 1/((k:ℝ)+1)) (by positivity)
  choose D hD x hx hm using hex
  refine ⟨D,fun k => gueMatrix (x k),fun k => lt_of_le_of_lt (Nat.zero_le _) (hD k),?_,hx,fun k i => gueMatrix_isHermitian _ _,?_⟩
  · exact tendsto_atTop_mono (fun k => (hD k).le) tendsto_id
  · intro w
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ (tendsto_one_div_add_atTop_nhds_zero_nat)
    filter_upwards [eventually_ge_atTop w.length] with k hk
    exact (hm k w hk).le
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
namespace FiniteEntropySeparation
 theorem matrixBlocks_apply {d p : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ) (j k : Fin d) (l r : Fin p) :
    matrixBlocks A (finProdFinEquiv (j,l)) (finProdFinEquiv (k,r)) = if l=r then A l j k else 0 := by
  change Matrix.blockDiagonal A (finProdFinEquiv.symm (finProdFinEquiv (j,l))) (finProdFinEquiv.symm (finProdFinEquiv (k,r))) = _
  simp only [Equiv.symm_apply_apply,Matrix.blockDiagonal]
  rfl
 theorem trace_matrixBlocks {d p : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (matrixBlocks A) = ∑ l, Matrix.trace (A l) := by
  rw [Matrix.trace]
  rw [← finProdFinEquiv.sum_comp]
  simp only [Fintype.sum_prod_type,Matrix.diag,matrixBlocks_apply,ite_true]
  rw [Finset.sum_comm]
  rfl
 theorem blockVector_normSq {d p : ℕ} (v : EuclideanSpace ℂ (Fin (d*p))) :
    ∑ l : Fin p, ‖blockVector v l‖^2 = ‖v‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,blockVector]
  rw [← finProdFinEquiv.sum_comp]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
 theorem matrixBlocks_mulVec {d p : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ)
    (v : EuclideanSpace ℂ (Fin (d*p))) (l : Fin p) :
    blockVector (matrixOperator (matrixBlocks A) v) l = matrixOperator (A l) (blockVector v l) := by
  ext j
  change (matrixBlocks A).mulVec v.ofLp (finProdFinEquiv (j,l)) = (A l).mulVec (fun k => v (finProdFinEquiv (k,l))) j
  simp only [Matrix.mulVec,dotProduct]
  rw [← finProdFinEquiv.sum_comp]
  simp [Fintype.sum_prod_type,matrixBlocks_apply]
 theorem matrixBlocks_norm_le {d p : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ)
    {K : ℝ} (hK : 0≤K) (hA : ∀ l, matrixOpNorm (A l)≤K) : matrixOpNorm (matrixBlocks A)≤K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro v
  have he : ‖matrixOperator (matrixBlocks A) v‖^2 ≤ K^2*‖v‖^2 := by
    rw [← blockVector_normSq,← blockVector_normSq v,Finset.mul_sum]
    apply sum_le_sum
    intro l _
    rw [matrixBlocks_mulVec,← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((matrixOperator (A l)).le_opNorm (blockVector v l) |>.trans (mul_le_mul_of_nonneg_right (hA l) (norm_nonneg _))) 2
  change ‖matrixOperator (matrixBlocks A) v‖ ≤ K*‖v‖
  nlinarith [norm_nonneg (matrixOperator (matrixBlocks A) v),mul_nonneg hK (norm_nonneg v)]
 theorem matrixBlocks_isHermitian {d p : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ l,(A l).IsHermitian) : (matrixBlocks A).IsHermitian := by
  ext j k
  obtain ⟨⟨j,l⟩,rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨k,r⟩,rfl⟩ := finProdFinEquiv.surjective k
  simp only [Matrix.conjTranspose_apply,matrixBlocks_apply]
  by_cases h:l=r
  · subst r; simp only [ite_true]; exact congrFun (congrFun (hA l) j) k
  · simp [h,Ne.symm h]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
namespace FiniteEntropySeparation
open FreeSeries FreeTensor
 theorem tensorMatrixTuple_norm_le {p d : ℕ} (hp : 2≤p) (A : Fin p → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i,matrixOpNorm (A i)≤64) (a : Option (Fin p)) : matrixOpNorm (tensorMatrixTuple A a)≤64 := by
  apply matrixBlocks_norm_le _ (by norm_num)
  intro l
  cases a with
  | some i => exact hA i
  | none =>
    change matrixOpNorm ((equidiscreteAtom p l:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))≤64
    rw [matrixOpNorm_smul,Complex.norm_real,Real.norm_eq_abs]
    have h := mul_le_mul (equidiscreteAtom_abs_le hp l) (matrixOpNorm_one (d:=d)) (matrixOpNorm_nonneg _) (by norm_num : (0:ℝ)≤1)
    norm_num at h ⊢
    linarith
 theorem tensorMatrixTuple_isHermitian {p d : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i,(A i).IsHermitian) (a : Option (Fin p)) : (tensorMatrixTuple A a).IsHermitian := by
  apply matrixBlocks_isHermitian
  intro l
  cases a with
  | some i => exact hA i
  | none =>
    change (((equidiscreteAtom p l:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))).IsHermitian
    simp [Matrix.IsHermitian,Matrix.conjTranspose_smul]
 theorem tensorMatrixTuple_word {p d : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ) (w : List (Option (Fin p))) :
    matrixWord (tensorMatrixTuple A) w = matrixBlocks (fun l : Fin p => (equidiscreteAtom p l:ℂ)^(w.count none) • matrixWord A (w.filterMap id)) := by
  let F : Option (Fin p) → (Fin p → Matrix (Fin d) (Fin d) ℂ) :=
    fun a l => optionTuple A ((equidiscreteAtom p l:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) a
  have hmap : matrixWord (tensorMatrixTuple A) w = matrixBlocks (w.map F).prod := by
    change (w.map (fun a => matrixBlocks (F a))).prod = matrixBlocks (w.map F).prod
    rw [map_list_prod,List.map_map]
    rfl
  rw [hmap]
  clear hmap
  congr 1
  funext l
  have he : (w.map F).prod l = (w.map (optionTuple A ((equidiscreteAtom p l:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)))).prod := by
    induction w with
    | nil => rfl
    | cons a w ih => simp only [List.map_cons,List.prod_cons,Pi.mul_apply,ih]; rfl
  rw [he,option_word_product _ _ (fun i => (Commute.one_left (A i)).smul_left _)]
  rw [smul_pow,one_pow,mul_smul_comm,mul_one]
  rfl
 theorem tensorMatrixTuple_moment {p d : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ) (w : List (Option (Fin p))) :
    matrixTraceWord (tensorMatrixTuple A) w = matrixTraceWord A (w.filterMap id) *
      ((p:ℂ)⁻¹ * ∑ l : Fin p, (equidiscreteAtom p l:ℂ)^(w.count none)) := by
  simp only [matrixTraceWord,tensorMatrixTuple_word,trace_matrixBlocks,Matrix.trace_smul,smul_eq_mul,Nat.cast_mul,mul_inv_rev]
  rw [← Finset.sum_mul]
  ring
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorMatrixModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace FiniteEntropySeparation
open FreeSeries FreeTensor
 theorem exists_tensor_matrix_models (p : ℕ) [NeZero p] (hp : 2≤p) :
    ∃ (D : ℕ → ℕ) (A : (k : ℕ) → Fin (p+1) → Matrix (Fin (D k)) (Fin (D k)) ℂ),
      (∀ k,0<D k) ∧ Tendsto D atTop atTop ∧
      (∀ k i,matrixOpNorm (A k i)≤64) ∧ (∀ k i,(A k i).IsHermitian) ∧
      ∀ w : List (Fin (p+1)), Tendsto (fun k => matrixTraceWord (A k) w) atTop (𝓝 (Model.signalMoments p w)) := by
  obtain ⟨D,A,hD0,hD,hA,hAH,hM⟩ := exists_free_matrix_models p
  let E := fun k => D k*p
  let T := fun k (i : Fin (p+1)) => tensorMatrixTuple (A k) ((optionFin p).symm i)
  refine ⟨E,T,fun k => Nat.mul_pos (hD0 k) (by omega),?_,?_,?_,?_⟩
  · apply tendsto_atTop_mono _ hD
    intro k
    dsimp [E]
    exact Nat.le_mul_of_pos_right _ (by omega)
  · intro k i; exact tensorMatrixTuple_norm_le hp (A k) (hA k) _
  · intro k i; exact tensorMatrixTuple_isHermitian (A k) (hAH k) _
  · intro w
    let v := w.map (optionFin p).symm
    have he : v.map (optionFin p)=w := by simp [v,List.map_map]
    have ht (k : ℕ) : matrixTraceWord (T k) w = matrixTraceWord (tensorMatrixTuple (A k)) v := by
      rw [matrixTraceWord_map]; rfl
    have hm : Model.signalMoments p w = FreeSeries.fockMoments p (v.filterMap id) *
        ((p:ℂ)⁻¹ * ∑ l : Fin p, (equidiscreteAtom p l:ℂ)^(v.count none)) := by
      rw [← he,Model.signal_option_moments, equidiscreteSignal_moments]
    simp only [ht,tensorMatrixTuple_moment,hm]
    exact (hM (v.filterMap id)).mul_const _
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MicrostatesLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace FiniteEntropySeparation
 section Generic
 variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
 theorem chiCutoff_lower_of_heat_models {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
    (a : (k:ℕ) → MatrixCoordinates n (D k)) {R : ℝ} (hR : 0≤R)
    (hA : ∀k i,matrixOpNorm (hermitianMatrix (a k) i)≤R)
    {u : ℝ} (hu : 0<u) (hMom : ∀w (ε:ℝ), 0<ε → Tendsto (fun k => (productGaussian (MatrixIndex n (D k))).real
      {x | ε≤‖matrixTraceWord (heatMatrix (hermitianMatrix (a k)) u x) w-wordMoment τ X w‖}) atTop (𝓝 0)) :
    (((n:ℝ)/2*Real.log u-Real.log 2:ℝ):EReal) ≤ chiCutoff τ X (R+Real.sqrt u*64) := by
  apply le_iInf
  intro m
  apply le_iInf
  intro ε
  have hp := heat_microstates_probability τ X hD0 hD a hA u hMom m ε.property
  let F : ℕ → EReal := fun d => ((((d+1:ℕ):ℝ)^2)⁻¹:ℝ)*
    (volume (microstates τ X (R+Real.sqrt u*64) m (d+1) ε.val)).log+((n:ℝ)/2*Real.log (d+1):ℝ)
  have hD' := (tendsto_sub_atTop_nat 1).comp hD
  apply le_trans _ (hD'.limsup_comp_le_limsup (u := F))
  apply le_limsup_of_frequently_le'
  apply Filter.Eventually.frequently
  filter_upwards [hp] with k hk
  have hv := gaussian_affine_volume (a k) (r := Real.sqrt u/Real.sqrt (D k))
    (div_pos (Real.sqrt_pos.mpr hu) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hD0 k))))
    (microstates τ X (R+Real.sqrt u*64) m (D k) ε.val) hk
  have he : F (D k-1) = ((((D k:ℝ)^2)⁻¹:ℝ):EReal)*
    (volume (microstates τ X (R+Real.sqrt u*64) m (D k) ε.val)).log+(((n:ℝ)/2*Real.log (D k):ℝ):EReal) := by
    have hn : D k-1+1=D k := Nat.sub_add_cancel (hD0 k)
    have hc : ((D k-1:ℕ):ℝ)+1=(D k:ℝ) := by exact_mod_cast hn
    simp only [F,hn,hc]
    rw [hn]
  change _ ≤ F (D k-1)
  rw [he]
  apply normalized_log_lower n (D k) (hD0 k) hu
    (ne_of_lt (microstates_volume_lt_top τ X _ (by positivity) _ _ _))
  simpa only [Fintype.card_prod,Fintype.card_fin,mul_assoc] using hv
 end Generic
 namespace Model
 theorem chiCutoff_lower (p : ℕ) [NeZero p] (hp : 2≤p) {h : ℝ} (hh : 0<h) :
    ((((p+1:ℕ):ℝ)/2*Real.log h-Real.log 2:ℝ):EReal) ≤ chiCutoff (τ p) (X p h) (64+Real.sqrt h*64) := by
  obtain ⟨D,A,hD0,hD,hA,hAH,hM⟩ := exists_tensor_matrix_models p hp
  let a := fun k => matrixCoordinatesOfHermitian (A k)
  have ha (k : ℕ) : hermitianMatrix (a k)=A k := funext (hermitianMatrix_coordinatesOfHermitian (A k) (hAH k))
  apply chiCutoff_lower_of_heat_models (τ p) (X p h) hD0 hD a (by norm_num : (0:ℝ)≤64)
    (fun k i => by rw [ha]; exact hA k i) hh
  intro w ε hε
  simp only [ha]
  exact FreeTensor.heatMatrix_probability_tendsto hD0 hD A (by norm_num) hA ∅ (C p)
    (C_mem_background p ∅) (initialIndex p) (initialIndex_injective p) (fun i => Set.notMem_empty _) hM h w hε
 theorem chi_gt_bot_oai (p : ℕ) [NeZero p] (hp : 2≤p) {h : ℝ} (hh : 0<h) :
    (⊥:EReal)<chi (τ p) (X p h) := by
  have hl := chiCutoff_lower p hp hh
  have hu : chiCutoff (τ p) (X p h) (64+Real.sqrt h*64) ≤ chi (τ p) (X p h) :=
    le_iSup_of_le ⟨64+Real.sqrt h*64,by positivity⟩ le_rfl
  exact (EReal.bot_lt_coe _).trans_le (hl.trans hu)
 end Model
end FiniteEntropySeparation

end

end OAI
end

theorem solution : type_of% @OAI.FiniteEntropySeparation.Model.chi_gt_bot_oai := @OAI.FiniteEntropySeparation.Model.chi_gt_bot_oai
