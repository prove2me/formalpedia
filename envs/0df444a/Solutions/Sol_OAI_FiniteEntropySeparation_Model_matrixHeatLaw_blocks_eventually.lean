-- Prove2me | solution 1 for OAI.FiniteEntropySeparation.Model.matrixHeatLaw_blocks_eventually
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:20:15.039987+00:00
-- url     : https://prove2.me/submissions/5d3c2206-f325-4b19-b8b2-4ea3c69c1ebd

import Mathlib
import Definitions.Def_FiniteEntropySeparation
import Definitions.Def_OAIQWFE002
import Theorems.Thm_HighDimProb_RandomProcesses_gaussian_integration_by_parts

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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
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
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

noncomputable section
open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal
namespace FiniteEntropySeparation
 theorem integral_pi_prod {ι : Type u1} [Fintype ι] (f : ι → ℝ → ℝ)
    (s : ι → Set ℝ) (hs : ∀i,MeasurableSet (s i)) :
    ∫ x : ι → ℝ in Set.pi univ s, ∏ i,f i (x i) = ∏ i,∫ x in s i,f i x := by
  classical
  rw [← integral_indicator (MeasurableSet.univ_pi hs)]
  have he : (Set.pi univ s).indicator (fun x : ι → ℝ => ∏ i,f i (x i)) =
      fun x => ∏ i,(s i).indicator (f i) (x i) := by
    funext x
    by_cases h : ∀i,x i ∈ s i
    · simp [Set.indicator_of_mem,Set.mem_pi,h]
    · obtain ⟨i,hi⟩ := not_forall.mp h
      rw [Set.indicator_of_notMem (by simpa only [Set.mem_univ_pi] using not_forall.mpr ⟨i,hi⟩)]
      symm
      exact prod_eq_zero (mem_univ i) (Set.indicator_of_notMem hi _)
  rw [he,integral_fintype_prod_volume_eq_prod]
  simp only [integral_indicator,hs]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal Topology
namespace FiniteEntropySeparation
 variable {ι : Type u1} [Fintype ι]
 theorem normalKernel_pos (s : ℝ) (x : EuclideanSpace ℝ ι) : 0<normalKernel s x := Real.exp_pos _
 theorem normalKernel_formula {s : ℝ} (hs : 0<s) (x : EuclideanSpace ℝ ι) :
    normalKernel s x = (Real.sqrt (2*Real.pi*s))⁻¹^(Fintype.card ι)*Real.exp (-‖x‖^2/(2*s)) := by
  rw [normalKernel,sub_eq_add_neg,Real.exp_add]
  simp only [neg_div]
  congr 1
  have hp : 0<2*Real.pi*s := by positivity
  rw [← Real.exp_log (show 0<(Real.sqrt (2*Real.pi*s))⁻¹^(Fintype.card ι) by positivity),Real.log_pow,Real.log_inv,Real.log_sqrt hp.le]
  congr 1
  ring
 theorem normalKernel_product {s : ℝ} (hs : 0<s) (x : EuclideanSpace ℝ ι) :
    normalKernel s x = ∏ i,gaussianPDFReal 0 ⟨s,hs.le⟩ (x i) := by
  classical
  rw [normalKernel_formula hs]
  simp only [gaussianPDFReal,sub_zero,prod_mul_distrib,prod_const,card_univ,← Real.exp_sum]
  congr 1
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs,sq_abs,← sum_div,sum_neg_distrib]
  rfl
 theorem normalKernel_continuous_space (s : ℝ) : Continuous (normalKernel (ι := ι) s) := by
  unfold normalKernel
  fun_prop
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem normalKernel_le (s : ℝ) (hs : 0<s) (x : EuclideanSpace ℝ ι) :
    normalKernel s x ≤ Real.exp (-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)) := by
  apply Real.exp_le_exp.mpr
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity))
 theorem normalKernel_integrable_finite (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) (x : EuclideanSpace ℝ ι) : Integrable (fun a => normalKernel s (x-a)) μ := by
  apply (integrable_const (Real.exp (-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)))).mono'
    (((normalKernel_continuous_space s).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  exact ae_of_all _ (fun a => by change ‖normalKernel s (x-a)‖≤_; rw [Real.norm_eq_abs,abs_of_pos (normalKernel_pos _ _)]; exact normalKernel_le s hs _)
 theorem smoothedDensity_continuous (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) : Continuous (smoothedDensity μ s) := by
  apply continuous_of_dominated (bound := fun _ => Real.exp (-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)))
  · intro x; exact (normalKernel_integrable_finite μ hs x).aestronglyMeasurable
  · intro x; exact ae_of_all _ (fun a => by change ‖normalKernel s (x-a)‖≤_; rw [Real.norm_eq_abs,abs_of_pos (normalKernel_pos _ _)]; exact normalKernel_le s hs _)
  · exact integrable_const _
  · exact ae_of_all _ (fun a => (normalKernel_continuous_space s).comp (continuous_id.sub continuous_const))
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.NormalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem map_withDensity_of_measurePreserving {α : Type u2} {β : Type u3} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurePreserving f μ ν)
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    (μ.withDensity (g ∘ f)).map f = ν.withDensity g := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hf.measurable]
  change (∫⁻ a,(F ∘ f) a ∂μ.withDensity (g ∘ f)) = _
  rw [lintegral_withDensity_eq_lintegral_mul μ (hg.comp hf.measurable) (hF.comp hf.measurable),lintegral_withDensity_eq_lintegral_mul ν hg hF]
  exact hf.lintegral_comp (hg.mul hF)
 theorem productNormal_withDensity {s : ℝ} (hs : 0<s) :
    Measure.pi (fun _ : ι => gaussianReal 0 (⟨s,hs.le⟩ : ℝ≥0)) =
      volume.withDensity (fun x : ι → ℝ => ENNReal.ofReal (∏i,gaussianPDFReal 0 (⟨s,hs.le⟩ : ℝ≥0) (x i))) := by
  classical
  have hv : (⟨s,hs.le⟩ : ℝ≥0)≠0 := by
    intro h; exact hs.ne' (congrArg (fun x : ℝ≥0 => (x:ℝ)) h)
  have hi : Integrable (fun x : ι → ℝ => ∏i,gaussianPDFReal 0 (⟨s,hs.le⟩ : ℝ≥0) (x i)) :=
    Integrable.fintype_prod (fun _ => integrable_gaussianPDFReal 0 (⟨s,hs.le⟩ : ℝ≥0))
  let v : ℝ≥0 := ⟨s,hs.le⟩
  have : ∀i : ι,SigmaFinite (gaussianReal 0 v) := fun _ => inferInstance
  apply Measure.pi_eq (μ := fun _ : ι => gaussianReal 0 v)
  intro S hS
  rw [withDensity_apply _ (MeasurableSet.univ_pi hS)]
  rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ (fun x => prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)))]
  rw [integral_pi_prod _ S hS,ENNReal.ofReal_prod_of_nonneg]
  · apply prod_congr rfl
    intro i _
    rw [gaussianReal_apply 0 hv]
    exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 (⟨s,hs.le⟩ : ℝ≥0)).integrableOn
      (ae_of_all _ (gaussianPDFReal_nonneg _ _))
  · intro i _
    exact integral_nonneg (gaussianPDFReal_nonneg _ _)
 theorem normalLaw_eq_map {s : ℝ} (hs : 0<s) :
    normalLaw (ι := ι) s = (Measure.pi (fun _ : ι => gaussianReal 0 (⟨s,hs.le⟩ : ℝ≥0))).map (WithLp.toLp 2) := by
  rw [productNormal_withDensity hs]
  have he : (fun x : ι → ℝ => ENNReal.ofReal (∏i,gaussianPDFReal 0 (⟨s,hs.le⟩ : ℝ≥0) (x i))) =
       (fun x => ENNReal.ofReal (normalKernel s x)) ∘ WithLp.toLp 2 := by
    funext x; simp only [Function.comp_apply,normalKernel_product hs]
  rw [he]
  exact (map_withDensity_of_measurePreserving (PiLp.volume_preserving_toLp ι)
    (fun x => ENNReal.ofReal (normalKernel s x))
    (ENNReal.measurable_ofReal.comp (normalKernel_continuous_space s).measurable)).symm
 theorem normalLaw_eq_scaled {s : ℝ} (hs : 0<s) :
    normalLaw (ι := ι) s = (productGaussian ι).map (fun x => Real.sqrt s • WithLp.toLp 2 x) := by
  have hm : (productGaussian ι).map (fun x i => Real.sqrt s*x i) = Measure.pi (fun _ : ι => gaussianReal 0 (⟨s,hs.le⟩ : ℝ≥0)) := by
    change (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x i => Real.sqrt s * id (x i)) = _
    rw [Measure.pi_map_pi (fun _ => (measurable_id.const_mul (Real.sqrt s)).aemeasurable)]
    congr 1
    funext i
    simp only [id_eq]
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp only [mul_one,NNReal.coe_mk,Real.sq_sqrt hs.le]
      rfl
  rw [normalLaw_eq_map hs,← hm]
  rw [Measure.map_map (show Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) from (PiLp.continuous_toLp 2 _).measurable) (by fun_prop)]
  congr 1
 theorem normalLaw_probability {s : ℝ} (hs : 0<s) : IsProbabilityMeasure (normalLaw (ι := ι) s) := by
  rw [normalLaw_eq_scaled hs]
  exact Measure.isProbabilityMeasure_map (by fun_prop)
 theorem smoothedLaw_eq (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) :
    (μ.prod (normalLaw s)).map (fun z => z.1+z.2) =
      volume.withDensity (fun x => ENNReal.ofReal (smoothedDensity μ s x)) := by
  have : IsProbabilityMeasure (normalLaw (ι := ι) s) := normalLaw_probability hs
  have hk := (ENNReal.measurable_ofReal.comp (normalKernel_continuous_space (ι := ι) s).measurable)
  have hden := (ENNReal.measurable_ofReal.comp (smoothedDensity_continuous μ hs).measurable)
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (by fun_prop)]
  rw [lintegral_prod _ (show AEMeasurable (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => F (z.1+z.2)) _ from (hF.comp (by fun_prop)).aemeasurable)]
  have hinner (a : EuclideanSpace ℝ ι) :
      (∫⁻z,F (a+z) ∂normalLaw s) = ∫⁻z,ENNReal.ofReal (normalKernel s z)*F (a+z) := by
    exact lintegral_withDensity_eq_lintegral_mul volume hk (show Measurable (fun z => F (a+z)) from hF.comp (measurable_const.add measurable_id))
  simp_rw [hinner]
  have hshift (a : EuclideanSpace ℝ ι) :
      (∫⁻z,ENNReal.ofReal (normalKernel s z)*F (a+z)) =
      ∫⁻x,ENNReal.ofReal (normalKernel s (x-a))*F x := by
    have he := (measurePreserving_add_left (volume : Measure (EuclideanSpace ℝ ι)) a).lintegral_comp
      (f := fun x => ENNReal.ofReal (normalKernel s (x-a))*F x)
      ((hk.comp (measurable_id.sub measurable_const)).mul hF)
    simpa only [add_sub_cancel_left] using he
  simp_rw [hshift]
  have hmeas : Measurable (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      ENNReal.ofReal (normalKernel s (z.2-z.1))*F z.2) :=
    (hk.comp (measurable_snd.sub measurable_fst)).mul (hF.comp measurable_snd)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  change (∫⁻x,∫⁻a,ENNReal.ofReal (normalKernel s (x-a))*F x ∂μ) = ∫⁻x,F x ∂volume.withDensity (ENNReal.ofReal ∘ smoothedDensity μ s)
  rw [lintegral_withDensity_eq_lintegral_mul volume hden hF]
  apply lintegral_congr
  intro x
  rw [lintegral_mul_const (F x) (show Measurable (fun a => ENNReal.ofReal (normalKernel s (x-a))) from hk.comp (measurable_const.sub measurable_id)),← ofReal_integral_eq_lintegral_ofReal (normalKernel_integrable_finite μ hs x) (ae_of_all _ (fun a => (normalKernel_pos _ _).le))]
  rfl
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianBlockTail
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
variable {ι : Type u1} [Fintype ι]
 theorem normalLaw_rotation (s : ℝ) (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (normalLaw s).map U = normalLaw s := by
  have he : (fun x => ENNReal.ofReal (normalKernel s x)) =
      (fun x => ENNReal.ofReal (normalKernel s x)) ∘ U := by
    funext x
    simp [normalKernel]
  unfold normalLaw
  conv_lhs => rw [he]
  exact map_withDensity_of_measurePreserving U.measurePreserving _
    (ENNReal.measurable_ofReal.comp (normalKernel_continuous_space s).measurable)
 theorem normalLaw_measurePreserving (s : ℝ) (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    MeasurePreserving U (normalLaw s) (normalLaw s) :=
  ⟨U.continuous.measurable,normalLaw_rotation s U⟩
 theorem gaussian_square_integral : (∫x : ℝ,x^2 ∂gaussianReal 0 1)=1 := by
  simpa [pow_two] using gaussian_polynomial_stein (Polynomial.X : Polynomial ℝ)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CoordinateMask
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
 theorem coordinateMask_sq (m : Finset ι) (x : EuclideanSpace ℝ ι) :
    ‖coordinateMask m x‖^2=∑i∈m,x i^2 := by
  classical
  simp [coordinateMask,EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
 theorem coordinateMask_continuous (m : Finset ι) : Continuous (coordinateMask m) :=
  (coordinateMaskLinear m).continuous_of_finiteDimensional
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 theorem hermitianMatrix_continuous {n d : ℕ} (i : Fin n) :
    Continuous (fun a : MatrixCoordinates n d => hermitianMatrix a i) :=
  (continuous_apply i).comp (hermitianChart n d).continuous_of_finiteDimensional
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
 namespace IsRealPolynomial
 theorem coord {ι : Type u1} [Fintype ι] [DecidableEq ι] (i : ι) : IsRealPolynomial (fun x : ι → ℝ => x i) := ⟨MvPolynomial.X i, by simp⟩
 theorem pow {ι : Type u1} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (n : ℕ) : IsRealPolynomial (fun x => f x^n) := by
  obtain ⟨P,rfl⟩ := hf
  exact ⟨P^n,by simp⟩
 theorem integrable {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) : Integrable f (productGaussian ι) := by
  obtain ⟨P,rfl⟩ := hf
  exact gaussian_mvPolynomial_integrable P
 end IsRealPolynomial
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
-- module Solutions.OAIQW_FiniteEntropySeparation.SpectralBlockMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset MeasureTheory ProbabilityTheory
namespace FiniteEntropySeparation
variable {p d : ℕ}
 theorem blockMask_card (f : Fin d → Fin p) :
    (blockMask f).card = p*∑j : Fin d,(univ.filter (fun k => f k=f j)).card := by
  classical
  rw [blockMask,card_filter]
  simp only [Fintype.sum_prod_type]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last,lt_self_iff_false,false_and,ite_false,sum_const_zero,add_zero,
    Fin.val_castSucc,Fin.is_lt,true_and]
  have he : (∑j : Fin d,∑k : Fin d,if f j=f k then 1 else 0)=
      ∑j : Fin d,(univ.filter (fun k => f k=f j)).card := by
    apply sum_congr rfl
    intro j _
    simp only [card_filter,eq_comm]
  simp only [he,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
 theorem blockMask_card_le (f : Fin d → Fin p) (hf : balancedBlocks f) :
    (blockMask f).card≤2*d^2 := by
  rw [blockMask_card,mul_sum]
  calc
    _ ≤ ∑j : Fin d,2*d := sum_le_sum (fun j _ => hf (f j))
    _ = _ := by simp; ring
 theorem blockMask_matrixEnergy (f : Fin d → Fin p) (a : MatrixCoordinates (p+1) d) :
    ‖coordinateMask (blockMask f) a‖^2 =
      ∑i : Fin p,∑j : Fin d,∑k : Fin d,if f j=f k then Complex.normSq (hermitianMatrix a i.castSucc j k) else 0 := by
  classical
  rw [coordinateMask_sq,blockMask,sum_filter]
  simp only [Fintype.sum_prod_type]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last,lt_self_iff_false,false_and,ite_false,sum_const_zero,add_zero,
    Fin.val_castSucc,Fin.is_lt,true_and]
  apply sum_congr rfl
  intro i _
  simp_rw [hermitianMatrix_normSq]
  have he : (∑j : Fin d,∑k : Fin d,if f j=f k then a (i.castSucc,k,j)^2 else 0)=
      ∑j : Fin d,∑k : Fin d,if f j=f k then a (i.castSucc,j,k)^2 else 0 := by
    rw [sum_comm]
    congr 1
    funext k
    apply sum_congr rfl
    intro j _
    simp only [eq_comm]
  have hp (j k : Fin d) : (if f j=f k then (a (i.castSucc,j,k)^2+a (i.castSucc,k,j)^2)/2 else 0) =
      ((if f j=f k then a (i.castSucc,j,k)^2 else 0)+(if f j=f k then a (i.castSucc,k,j)^2 else 0))/2 := by split_ifs <;> ring
  conv_rhs => simp only [hp,← sum_div,sum_add_distrib]
  rw [he]
  ring
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixRotationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Matrix.Norms.L2Operator
open Finset Set
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem unitary_matrix_norm {d : ℕ} (hd : 0<d) (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    matrixOpNorm (U:Matrix (Fin d) (Fin d) ℂ)=1 := by
  have : NeZero d := ⟨by omega⟩
  exact CStarRing.norm_coe_unitary U
 theorem isCompact_unitary_matrix (hd : 0<d) :
    IsCompact (unitary (Matrix (Fin d) (Fin d) ℂ) : Set (Matrix (Fin d) (Fin d) ℂ)) := by
  apply (Metric.isCompact_iff_isClosed_bounded).mpr
  refine ⟨isClosed_unitary,?_⟩
  rw [Metric.isBounded_iff_subset_closedBall (0 : Matrix (Fin d) (Fin d) ℂ)]
  refine ⟨1,fun U hU => ?_⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  change matrixOpNorm U≤1
  exact (unitary_matrix_norm hd ⟨U,hU⟩).le
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.BlockEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Set
open scoped Matrix.Norms.L2Operator ENNReal
namespace FiniteEntropySeparation
variable {p d n : ℕ}
 theorem matrixCoordinatesOfHermitian_continuous :
    Continuous (matrixCoordinatesOfHermitian : (Fin n → Matrix (Fin d) (Fin d) ℂ) → MatrixCoordinates n d) := by
  unfold matrixCoordinatesOfHermitian
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  rintro ⟨i,j,k⟩
  dsimp only
  split_ifs <;> fun_prop
 theorem rotateCoordinates_continuous_joint :
    Continuous (fun z : unitary (Matrix (Fin d) (Fin d) ℂ) × MatrixCoordinates n d => rotateCoordinates z.1 z.2) := by
  unfold rotateCoordinates
  apply matrixCoordinatesOfHermitian_continuous.comp
  apply continuous_pi
  intro i
  exact ((continuous_subtype_val.comp continuous_fst).star.mul ((hermitianMatrix_continuous i).comp continuous_snd)).mul
    (continuous_subtype_val.comp continuous_fst)
 theorem blockEvent_isClosed (hd : 0<d) (r M : ℝ) : IsClosed (blockEvent p d r M) := by
  have : CompactSpace (unitary (Matrix (Fin d) (Fin d) ℂ)) := isCompact_iff_compactSpace.mp (isCompact_unitary_matrix hd)
  have hf (f : Fin d → Fin p) : IsClosed {a : MatrixCoordinates (p+1) d |
      ∃U : unitary (Matrix (Fin d) (Fin d) ℂ),r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖} := by
    have hh : IsClosed {z : unitary (Matrix (Fin d) (Fin d) ℂ) × MatrixCoordinates (p+1) d |
        r≤‖coordinateMask (blockMask f) (rotateCoordinates z.1 z.2)‖} :=
      isClosed_le continuous_const ((coordinateMask_continuous _).comp rotateCoordinates_continuous_joint).norm
    convert isClosedMap_snd_of_compactSpace _ hh using 1
    ext a
    simp only [Set.mem_ofPred_eq,Set.mem_image,Prod.exists]
    constructor
    · rintro ⟨U,hU⟩; exact ⟨U,a,hU,rfl⟩
    · rintro ⟨U,b,hU,rfl⟩; exact ⟨U,hU⟩
  have he : blockEvent p d r M = {a | ‖a‖≤M} ∩
      ⋃ f : Fin d → Fin p, ⋃ (_ : balancedBlocks f),
        {a | ∃U : unitary (Matrix (Fin d) (Fin d) ℂ),r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖} := by
    ext a; simp [blockEvent]
  rw [he]
  exact (isClosed_le continuous_norm continuous_const).inter (isClosed_iUnion_of_finite (fun f => isClosed_iUnion_of_finite (fun _ => hf f)))
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianProjectionMoments
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
 theorem productGaussian_coordinate_second {ι : Type u1} [Fintype ι] [DecidableEq ι] (i : ι) :
    (∫x : ι → ℝ,x i^2 ∂productGaussian ι)=1 := by
  have hm := measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i
  have he := integral_map hm.measurable.aemeasurable
    (show AEStronglyMeasurable (fun x : ℝ => x^2) (Measure.map (Function.eval i) (productGaussian ι)) from (continuous_id.pow 2).aestronglyMeasurable)
  change (∫y : ℝ,y^2 ∂Measure.map (Function.eval i) (Measure.pi (fun _ : ι => gaussianReal 0 1)))=_ at he
  rw [hm.map_eq,gaussian_square_integral] at he
  exact he.symm
 theorem normalLaw_coordinateMask_integrable {s : ℝ} (hs : 0<s) (m : Finset ι) :
    Integrable (fun x => ‖coordinateMask m x‖^2) (normalLaw s) := by
  rw [normalLaw_eq_scaled hs]
  apply (integrable_map_measure (((coordinateMask_continuous m).norm.pow 2).aestronglyMeasurable) (by fun_prop : AEMeasurable (fun x : ι → ℝ => Real.sqrt s • WithLp.toLp 2 x) _)).mpr
  change Integrable (fun x : ι → ℝ => ‖coordinateMask m (Real.sqrt s • WithLp.toLp 2 x)‖^2) (productGaussian ι)
  simp only [coordinateMask_sq,PiLp.smul_apply,smul_eq_mul,mul_pow,Real.sq_sqrt hs.le,← mul_sum]
  exact (integrable_finsetSum _ (fun i _ => ((IsRealPolynomial.coord i).pow 2).integrable)).const_mul s
 theorem normalLaw_coordinateMask_integral {s : ℝ} (hs : 0<s) (m : Finset ι) :
    (∫x,‖coordinateMask m x‖^2 ∂normalLaw s)=s*m.card := by
  rw [normalLaw_eq_scaled hs]
  have hm : AEStronglyMeasurable (fun x : EuclideanSpace ℝ ι => ‖coordinateMask m x‖^2) (Measure.map (fun x : ι → ℝ => Real.sqrt s • WithLp.toLp 2 x) (productGaussian ι)) := ((coordinateMask_continuous m).norm.pow 2).aestronglyMeasurable
  rw [integral_map (by fun_prop) hm]
  simp only [coordinateMask_sq,PiLp.smul_apply,smul_eq_mul,mul_pow,Real.sq_sqrt hs.le,← mul_sum]
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => ((IsRealPolynomial.coord i).pow 2).integrable)]
  simp only [productGaussian_coordinate_second,sum_const,mul_one,nsmul_eq_mul]
 theorem normalLaw_coordinateMask_markov {s r : ℝ} (hs : 0<s) (hr : 0<r) (m : Finset ι) :
    (normalLaw s) {x | r≤‖coordinateMask m x‖} ≤ ENNReal.ofReal (s*m.card/r^2) := by
  have hz : 0<r^2 := sq_pos_of_pos hr
  let F : EuclideanSpace ℝ ι → ℝ := fun x => ‖coordinateMask m x‖^2/r^2
  have hF := (normalLaw_coordinateMask_integrable hs m).div_const (r^2)
  have hh := hF.measure_le_integral (ae_of_all _ (fun x => div_nonneg (sq_nonneg _) hz.le))
    (s := {x | r≤‖coordinateMask m x‖}) (fun x hx => by
      dsimp at hx
      rw [le_div_iff₀ hz,one_mul]
      exact pow_le_pow_left₀ hr.le hx 2)
  simpa only [integral_div,normalLaw_coordinateMask_integral hs m] using hh
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MicrostatesSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology
namespace FiniteEntropySeparation
 theorem exists_strictMono_diagonal (P : ℕ → ℕ → Prop)
    (hP : ∀k L,∃d,L<d ∧ P k d) : ∃D : ℕ → ℕ, StrictMono D ∧ ∀k,P k (D k) := by
  classical
  choose f hf hfP using hP
  let D : ℕ → ℕ := fun k => Nat.rec (f 0 0) (fun k d => f (k+1) d) k
  refine ⟨D,strictMono_nat_of_lt_succ (fun k => hf (k+1) (D k)),?_⟩
  intro k
  cases k with
  | zero => exact hfP 0 0
  | succ k => exact hfP (k+1) (D k)
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

 theorem fockMoments_eq (p : ℕ) : fockMoments p = unit + subst (fockMoments p) quadratic := by
  funext w
  cases w with
  | nil => simp [fockMoments]
  | cons i w =>
    simp only [Pi.add_apply, unit_cons, zero_add, quadratic_subst_derivative]
    exact Fock.semicircular_integration_by_parts i w

end FiniteEntropySeparation.FreeSeries

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

theorem norm_sum_sq_orthogonal {H : Type u1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type u2} [Fintype ι] (x : ι → H)
    (h : ∀ i j, i ≠ j → inner ℂ (x i) (x j) = 0) :
    ‖∑ i, x i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  classical
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), sum_inner]
  have hs (i : ι) : inner ℂ (x i) (∑ j, x j) = inner ℂ (x i) (x i) := by
    rw [inner_sum]
    exact Finset.sum_eq_single i (fun j _ hji => h i j (Ne.symm hji)) (by simp)
  simp_rw [hs]
  simp only [map_sum, ← norm_sq_eq_re_inner (𝕜 := ℂ)]

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

 theorem spectralSignal_selfAdjoint (y : AddChar A ℂ → ℝ) :
    IsSelfAdjoint (spectralSignal (B := B) (N := N) y) := by
  show star _ = _
  simp [spectralSignal,
    star_sum (R := Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A))]

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

 theorem characterProjection_orthogonal (ψ φ : AddChar A ℂ) (h : ψ ≠ φ)
    (v w : Space B N (Multiplicative A)) :
    inner ℂ (characterProjection ψ v) (characterProjection φ w) = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
    star_characterProjection, ← mul_apply_eq_comp, characterProjection_mul, ite_eq_right (Ne.symm h)]
  simp

 theorem spectralSignal_norm_le (y : AddChar A ℂ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hy : ∀ ψ, |y ψ| ≤ R) : ‖spectralSignal (B := B) (N := N) y‖ ≤ R := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  have hx : ∑ ψ : AddChar A ℂ, characterProjection ψ x = x := by
    simpa only [sum_apply, one_apply_eq_self] using
      congrArg (fun T : Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A) => T x)
        (sum_characterProjection (B := B) (N := N) (A := A))
  have hn : ∑ ψ : AddChar A ℂ, ‖characterProjection ψ x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← norm_sum_sq_orthogonal _ (fun ψ φ h => characterProjection_orthogonal ψ φ h x x), hx]
  have hn' : ‖spectralSignal (B := B) (N := N) y x‖ ^ 2 =
      ∑ ψ : AddChar A ℂ, |y ψ| ^ 2 * ‖characterProjection ψ x‖ ^ 2 := by
    simp only [spectralSignal, sum_apply, smul_apply]
    rw [norm_sum_sq_orthogonal _ (by
      intro ψ φ h
      simp [characterProjection_orthogonal ψ φ h x x])]
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hsq : ‖spectralSignal (B := B) (N := N) y x‖ ^ 2 ≤ R ^ 2 * ‖x‖ ^ 2 := by
    rw [hn', ← hn, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ψ _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (abs_nonneg _) (hy ψ) 2
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg x))).mp
  simpa only [mul_pow] using hsq

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
-- module Solutions.OAIQW_FiniteEntropySeparation.NoiseTensor
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
variable {B N G : Type} [Group G]

variable [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem noise_basis_orthonormal : Orthonormal ℂ (fun w : List N =>
    basis (noiseWord (B := B) (G := G) w)) := by
  rw [orthonormal_iff_ite]
  intro v w
  by_cases h : v = w
  · subst w
    simp [basis, ]
  · have h' : noiseWord (B := B) (G := G) v ≠ noiseWord w :=
      fun hh => h (noiseWord_injective hh)
    simp [basis, lp.inner_single_left, lp.single_apply, h, h']

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

 theorem equidiscreteSignal_selfAdjoint : IsSelfAdjoint (equidiscreteSignal (B := B) (N := N) p) :=
  spectralSignal_selfAdjoint _

 theorem equidiscreteSignal_norm_le (hp : 2 ≤ p) :
    ‖equidiscreteSignal (B := B) (N := N) p‖ ≤ 1 :=
  spectralSignal_norm_le _ 1 zero_le_one (fun _character => equidiscreteAtom_abs_le hp _)

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

omit [Group G] in
theorem semicircularB_selfAdjoint [Group G] (b : B) : IsSelfAdjoint (semicircularB (N := N) (G := G) b) :=
  IsSelfAdjoint.add_star_self (creationB (N := N) (G := G) b)
 theorem semicircularN_selfAdjoint (i : N) : IsSelfAdjoint (semicircularN (B := B) (G := G) i) :=
  IsSelfAdjoint.add_star_self (creationN (B := B) (G := G) i)

 theorem semicircularB_mem_background (J : Set N) (b : B) :
    semicircularB (N := N) (G := G) b ∈ backgroundAlgebra J :=
  Algebra.subset_adjoin (Or.inl (Or.inl ⟨b,rfl⟩))

 theorem heatTuple_selfAdjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {n : ℕ} (X S : Fin n → H →L[ℂ] H)
    (hX : ∀ i, IsSelfAdjoint (X i)) (hS : ∀ i, IsSelfAdjoint (S i)) (u : ℝ) (i : Fin n) :
    IsSelfAdjoint (heatTuple X S u i) := by
  change star (X i + (Real.sqrt u : ℂ) • S i) = _
  simp only [star_add, star_smul, Complex.star_def, Complex.conj_ofReal, (hX i).star_eq,
    (hS i).star_eq, heatTuple]

end FreeTensor

namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]

omit [NeZero p] in
theorem initialIndex_injective [NeZero p] : Function.Injective (initialIndex p) := Fin.castAdd_injective (p+1) (p+1)

omit [NeZero p] in
theorem auxiliaryIndex_injective [NeZero p] : Function.Injective (auxiliaryIndex p) := Fin.natAdd_injective (p+1) (p+1)

omit [NeZero p] in
theorem auxiliaryIndex_fresh [NeZero p] (i : Fin (p+1)) : auxiliaryIndex p i ∉ oldNoise p := by
  rintro ⟨j,h⟩
  have hv := congrArg Fin.val h
  simp only [initialIndex, auxiliaryIndex, Fin.val_castAdd, Fin.val_natAdd] at hv
  have hj := j.isLt
  omega

 theorem C_selfAdjoint (i : Fin (p+1)) : IsSelfAdjoint (C p i) := by
  induction i using Fin.lastCases with
  | last => rw [C_last]; exact equidiscreteSignal_selfAdjoint p
  | cast i => rw [C_castSucc]; exact semicircularB_selfAdjoint i

 theorem C_mem_background (J : Set (Fin ((p+1)+(p+1)))) (i : Fin (p+1)) :
    C p i ∈ backgroundAlgebra J := by
  induction i using Fin.lastCases with
  | last => rw [C_last]; exact equidiscreteSignal_mem_background p J
  | cast i => rw [C_castSucc]; exact semicircularB_mem_background J i

 theorem X_selfAdjoint (h : ℝ) (i : Fin (p+1)) : IsSelfAdjoint (X p h i) :=
  heatTuple_selfAdjoint (C p) (initialNoise p) (C_selfAdjoint p)
    (fun _index => semicircularN_selfAdjoint _) h i

end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.BlockEventLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
namespace FiniteEntropySeparation
variable {p d : ℕ}
 theorem normalLaw_rotated_mask_markov {s r : ℝ} (hs : 0<s) (hr : 0<r)
    (f : Fin d → Fin p) (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    (normalLaw s) {a | r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖} ≤
      ENNReal.ofReal (s*(blockMask f).card/r^2) := by
  have hm := normalLaw_measurePreserving s (rotateLinearIsometryEquiv (n := p+1) U)
  have hE : MeasurableSet {a : MatrixCoordinates (p+1) d | r≤‖coordinateMask (blockMask f) a‖} :=
    (isClosed_le continuous_const (coordinateMask_continuous _).norm).measurableSet
  have he := hm.measure_preimage hE.nullMeasurableSet
  change (normalLaw s) {a | r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖} = _ at he
  rw [he]
  exact normalLaw_coordinateMask_markov hs hr _
 theorem coordinateMask_univ {ι : Type u1} [Fintype ι] [DecidableEq ι] (x : EuclideanSpace ℝ ι) :
    coordinateMask univ x=x := by ext i; simp [coordinateMask]
 theorem normalLaw_norm_markov {ι : Type u2} [Fintype ι] [DecidableEq ι] {s r : ℝ} (hs : 0<s) (hr : 0<r) :
    (normalLaw (ι := ι) s) {a | r≤‖a‖} ≤ ENNReal.ofReal (s*Fintype.card ι/r^2) := by
  simpa only [coordinateMask_univ,card_univ] using normalLaw_coordinateMask_markov (ι := ι) hs hr univ
 theorem blockEvent_add_mem {r A B M : ℝ} (hAB : A+B≤M)
    (a g : MatrixCoordinates (p+1) d) (ha : ‖a‖≤A) (hg : ‖g‖≤B)
    (f : Fin d → Fin p) (hf : balancedBlocks f) (U : unitary (Matrix (Fin d) (Fin d) ℂ))
    (ha' : 2*r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖)
    (hg' : ‖coordinateMask (blockMask f) (rotateCoordinates U g)‖≤r) :
    a+g∈blockEvent p d r M := by
  refine ⟨(norm_add_le _ _).trans ((add_le_add ha hg).trans hAB),f,hf,U,?_⟩
  have he : coordinateMask (blockMask f) (rotateCoordinates U (a+g))=
      coordinateMask (blockMask f) (rotateCoordinates U a)+coordinateMask (blockMask f) (rotateCoordinates U g) := by
    have hr := (rotateLinearIsometryEquiv (n := p+1) U).map_add a g
    change rotateCoordinates U (a+g)=rotateCoordinates U a+rotateCoordinates U g at hr
    rw [hr]
    exact (coordinateMaskLinear (blockMask f)).map_add _ _
  have hr := norm_sub_norm_le (coordinateMask (blockMask f) (rotateCoordinates U a))
    (-coordinateMask (blockMask f) (rotateCoordinates U g))
  simp only [norm_neg,sub_neg_eq_add] at hr
  rw [he]
  linarith
 theorem blockEvent_conditional_lower (hp : 2≤p) (hd : 0<d) {t v : ℝ} (ht : 0<t)
    (hv : 1≤v) (htv : t≤v) (hpt : 256*t≤p)
    (a : MatrixCoordinates (p+1) d) (ha : ‖a‖≤2*Real.sqrt ((p:ℝ)*d))
    (hab : ∃f : Fin d → Fin p,balancedBlocks f ∧ ∃U : unitary (Matrix (Fin d) (Fin d) ℂ),
      Real.sqrt ((p:ℝ)*d)/2≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖) :
    ENNReal.ofReal (1/2:ℝ) ≤ (normalLaw (t/d)) {g | a+g∈blockEvent p d (Real.sqrt ((p:ℝ)*d)/4) (4*Real.sqrt (v*p*d))} := by
  classical
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have hpd : 0<(p:ℝ)*d := mul_pos (by linarith) hd'
  have hvpd : 0<v*p*d := by positivity
  have htd : 0<t/(d:ℝ) := div_pos ht hd'
  have : IsProbabilityMeasure (normalLaw (ι := MatrixIndex (p+1) d) (t/d)) := normalLaw_probability htd
  obtain ⟨f,hf,U,hU⟩ := hab
  let E : Set (MatrixCoordinates (p+1) d) := {g | a+g∈blockEvent p d (Real.sqrt ((p:ℝ)*d)/4) (4*Real.sqrt (v*p*d))}
  let N : Set (MatrixCoordinates (p+1) d) := {g | 2*Real.sqrt (v*p*d)≤‖g‖}
  let B : Set (MatrixCoordinates (p+1) d) := {g | Real.sqrt ((p:ℝ)*d)/4≤‖coordinateMask (blockMask f) (rotateCoordinates U g)‖}
  have hN : (normalLaw (t/d)) N≤ENNReal.ofReal (3/8:ℝ) := by
    apply (normalLaw_norm_markov htd (by positivity : 0<2*Real.sqrt (v*p*d))).trans
    apply ENNReal.ofReal_le_ofReal
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_pow,Real.sq_sqrt hvpd.le]
    apply (div_le_iff₀ (by positivity : 0<(2:ℝ)^2*(v*p*d))).mpr
    field_simp
    nlinarith
  have hB : (normalLaw (t/d)) B≤ENNReal.ofReal (1/8:ℝ) := by
    apply (normalLaw_rotated_mask_markov htd (div_pos (Real.sqrt_pos.mpr hpd) (by norm_num)) f U).trans
    apply ENNReal.ofReal_le_ofReal
    have hc : ((blockMask f).card:ℝ)≤2*(d:ℝ)^2 := by exact_mod_cast blockMask_card_le f hf
    rw [div_pow,Real.sq_sqrt hpd.le]
    apply (div_le_iff₀ (by positivity : 0<(p:ℝ)*d/(4:ℝ)^2)).mpr
    have hh := mul_le_mul_of_nonneg_left hc htd.le
    have he : t/(d:ℝ)*(2*d^2)=2*t*d := by field_simp
    rw [he] at hh
    have hpdt := mul_le_mul_of_nonneg_right hpt hd'.le
    nlinarith
  have hsub : Eᶜ⊆N∪B := by
    intro g hg
    by_contra h
    have hn : ‖g‖<2*Real.sqrt (v*p*d) := lt_of_not_ge (fun hh => h (Or.inl hh))
    have hb : ‖coordinateMask (blockMask f) (rotateCoordinates U g)‖<Real.sqrt ((p:ℝ)*d)/4 :=
      lt_of_not_ge (fun hh => h (Or.inr hh))
    apply hg
    apply blockEvent_add_mem (A := 2*Real.sqrt ((p:ℝ)*d)) (B := 2*Real.sqrt (v*p*d)) _ a g ha hn.le f hf U _ hb.le
    · have hh : Real.sqrt ((p:ℝ)*d)≤Real.sqrt (v*p*d) := Real.sqrt_le_sqrt (by nlinarith)
      linarith
    · linarith
  have hEc : (normalLaw (t/d)) Eᶜ≤ENNReal.ofReal (1/2:ℝ) := by
    apply (measure_mono hsub).trans ((measure_union_le _ _).trans _)
    calc
      _ ≤ ENNReal.ofReal (3/8:ℝ)+ENNReal.ofReal (1/8:ℝ) := add_le_add hN hB
      _ = _ := by rw [← ENNReal.ofReal_add (by norm_num : (0:ℝ)≤3/8) (by norm_num : (0:ℝ)≤1/8)]; congr 1; norm_num
  have hm : MeasurableSet E := (blockEvent_isClosed hd _ _).measurableSet.preimage (by fun_prop : Measurable (fun g : MatrixCoordinates (p+1) d => a+g))
  have hh := measure_add_measure_compl hm (μ := normalLaw (t/d))
  rw [measure_univ] at hh
  have hle : (1:ℝ≥0∞)≤(normalLaw (t/d)) E+ENNReal.ofReal (1/2:ℝ) := by rw [← hh]; exact add_le_add (le_refl _) hEc
  have hfE : (normalLaw (t/d)) E≠⊤ := measure_ne_top _ _
  have htoreal := (ENNReal.toReal_le_toReal (by simp) (by finiteness)).mpr hle
  rw [ENNReal.toReal_add hfE (by finiteness)] at htoreal
  change ENNReal.ofReal (1/2:ℝ)≤(normalLaw (t/d)) E
  apply (ENNReal.ofReal_le_iff_le_toReal hfE).mpr
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤1/2)] at htoreal
  linarith
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixSpectralMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
open scoped ComplexConjugate
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem matrixWord_unitary_conjugate (U : unitary (Matrix (Fin d) (Fin d) ℂ))
    (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (w : List (Fin n)) :
    (w.map (fun i => star (U:Matrix (Fin d) (Fin d) ℂ)*A i*(U:Matrix (Fin d) (Fin d) ℂ))).prod =
      star (U:Matrix (Fin d) (Fin d) ℂ)*(w.map A).prod*(U:Matrix (Fin d) (Fin d) ℂ) := by
  induction w with
  | nil => simp []
  | cons i w ih =>
    simp only [List.map_cons,List.prod_cons,ih]
    have hU : (U:Matrix (Fin d) (Fin d) ℂ)*star (U:Matrix (Fin d) (Fin d) ℂ)=1 := by simp
    calc
      _ = star (U:Matrix (Fin d) (Fin d) ℂ)*A i*((U:Matrix (Fin d) (Fin d) ℂ)*star (U:Matrix (Fin d) (Fin d) ℂ))*(w.map A).prod*(U:Matrix (Fin d) (Fin d) ℂ) := by noncomm_ring
      _ = _ := by rw [hU]; noncomm_ring
 theorem trace_unitary_conjugate (U : unitary (Matrix (Fin d) (Fin d) ℂ)) (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (star (U:Matrix (Fin d) (Fin d) ℂ)*A*(U:Matrix (Fin d) (Fin d) ℂ))=Matrix.trace A := by
  rw [Matrix.trace_mul_cycle]
  have hU : (U:Matrix (Fin d) (Fin d) ℂ)*star (U:Matrix (Fin d) (Fin d) ℂ)=1 := by simp
  rw [hU,one_mul]
 theorem matrixMoment_rotate (U : unitary (Matrix (Fin d) (Fin d) ℂ)) (a : MatrixCoordinates n d) (w : List (Fin n)) :
    matrixMoment (rotateCoordinates U a) w=matrixMoment a w := by
  unfold matrixMoment
  have he : hermitianMatrix (rotateCoordinates U a)=fun i => star (U:Matrix (Fin d) (Fin d) ℂ)*hermitianMatrix a i*U := funext (hermitianMatrix_rotate U a)
  rw [he]
  rw [matrixWord_unitary_conjugate,trace_unitary_conjugate]
 theorem matrixMoment_replicate (a : MatrixCoordinates n d) (i : Fin n) (k : ℕ) :
    matrixMoment a (List.replicate k i)=(d:ℂ)⁻¹*Matrix.trace (hermitianMatrix a i^k) := by
  simp [matrixMoment]
 theorem diagonal_eigenvalues (a : MatrixCoordinates n d) (i : Fin n) :
    hermitianMatrix (rotateCoordinates (hermitianMatrix_isHermitian a i).eigenvectorUnitary a) i =
      Matrix.diagonal (fun j => ((hermitianMatrix_isHermitian a i).eigenvalues j:ℂ)) := by
  rw [hermitianMatrix_rotate]
  simpa [Unitary.conjStarAlgAut_apply,Function.comp_def] using (hermitianMatrix_isHermitian a i).conjStarAlgAut_star_eigenvectorUnitary
 theorem matrixMoment_eigenvalues (a : MatrixCoordinates n d) (i : Fin n) (k : ℕ) :
    (matrixMoment a (List.replicate k i)).re=(d:ℝ)⁻¹*∑j,((hermitianMatrix_isHermitian a i).eigenvalues j)^k := by
  rw [← matrixMoment_rotate (hermitianMatrix_isHermitian a i).eigenvectorUnitary a,
    matrixMoment_replicate,diagonal_eigenvalues,Matrix.diagonal_pow,Matrix.trace_diagonal]
  simp only [Pi.pow_apply,← Complex.ofReal_pow,← Complex.ofReal_sum,← Complex.ofReal_natCast,← Complex.ofReal_inv,← Complex.ofReal_mul,Complex.ofReal_re]
 theorem matrixUnivariateMoment_eigenvalues (q : Polynomial ℝ) (a : MatrixCoordinates n d) (i : Fin n) :
    matrixUnivariateMoment q a i=(d:ℝ)⁻¹*∑j,q.eval ((hermitianMatrix_isHermitian a i).eigenvalues j) := by
  unfold matrixUnivariateMoment
  simp_rw [matrixMoment_eigenvalues]
  simp only [mul_left_comm (q.coeff _),← mul_sum]
  congr 1
  simp only [Polynomial.eval_eq_sum,Polynomial.sum]
  rw [sum_comm]
  simp only [mul_sum]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SpectralClustering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
namespace FiniteEntropySeparation
variable {p d : ℕ}
 theorem clusterLabel_close [NeZero p] (y : Fin p → ℝ) (δ : ℝ) (x : Fin d → ℝ) (j : Fin d)
    (hj : j∉badSpectrum y δ x) : |x j-y (clusterLabel y δ x j)|≤δ := by
  have he : ∃l,|x j-y l|≤δ := by simpa [badSpectrum,not_forall,not_lt] using hj
  simp only [clusterLabel,dite_eq_left he]
  exact he.choose_spec
 theorem clusterLabel_separated [NeZero p] (y : Fin p → ℝ) (δ Δ : ℝ) (x : Fin d → ℝ)
    (hy : ∀i j,i≠j → Δ≤|y i-y j|) (hδ : δ≤Δ/4)
    {j k : Fin d} (hj : j∉badSpectrum y δ x) (hk : k∉badSpectrum y δ x)
    (hjk : clusterLabel y δ x j≠clusterLabel y δ x k) : Δ/2≤|x j-x k| := by
  have hj' := clusterLabel_close y δ x j hj
  have hk' := clusterLabel_close y δ x k hk
  have hy' := hy _ _ hjk
  have ht : |y (clusterLabel y δ x j)-y (clusterLabel y δ x k)|≤
      |x j-y (clusterLabel y δ x j)|+|x j-x k|+|x k-y (clusterLabel y δ x k)| := by
    calc
      _ = |-(x j-y (clusterLabel y δ x j))+(x j-x k)+(x k-y (clusterLabel y δ x k))| := by congr 1; ring
      _ ≤ |-(x j-y (clusterLabel y δ x j))|+|x j-x k|+|x k-y (clusterLabel y δ x k)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = _ := by rw [abs_neg]
  linarith
 theorem badSpectrum_product_bound (y : Fin p → ℝ) {δ : ℝ} (hδ : 0≤δ) (x : Fin d → ℝ) :
    ((badSpectrum y δ x).card:ℝ)*δ^(2*p) ≤ ∑j : Fin d,(∏l : Fin p,(x j-y l))^2 := by
  have hb j (hj : j∈badSpectrum y δ x) : δ^(2*p)≤(∏l : Fin p,(x j-y l))^2 := by
    have hh : δ^p≤|∏l : Fin p,(x j-y l)| := by
      rw [abs_prod]
      have hp := prod_le_prod₀ (fun _ (_ : _∈(univ:Finset (Fin p))) => hδ)
        (fun l (_ : l∈(univ:Finset (Fin p))) => ((mem_filter.mp hj).2 l).le)
      simpa using hp
    have := pow_le_pow_left₀ (pow_nonneg hδ p) hh 2
    simpa [← pow_mul,sq_abs,Nat.mul_comm] using this
  calc
    _ = ∑j∈badSpectrum y δ x,δ^(2*p) := by simp
    _ ≤ ∑j∈badSpectrum y δ x,(∏l : Fin p,(x j-y l))^2 := sum_le_sum hb
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
 theorem clusterLabel_rank_bound [NeZero p] (y : Fin p → ℝ) (δ : ℝ) (x : Fin d → ℝ)
    (q : Fin p → ℝ → ℝ)
    (hq : ∀l r,|r-y l|≤δ → (3:ℝ)/4≤q l r^2)
    (hm : ∀l,(∑j : Fin d,q l (x j)^2)≤9*(d:ℝ)/(8*p))
    (hb : ((badSpectrum y δ x).card:ℝ)≤(d:ℝ)/(2*p)) (l : Fin p) :
    (p:ℝ)*((univ.filter (fun j => clusterLabel y δ x j=l)).card:ℝ)≤2*d := by
  classical
  have hp : (0:ℝ)<p := by exact_mod_cast NeZero.pos p
  let S := univ.filter (fun j => clusterLabel y δ x j=l)
  let B := badSpectrum y δ x
  have hgood : ((S\B).card:ℝ)*(3/4:ℝ)≤∑j : Fin d,q l (x j)^2 := by
    calc
      _ = ∑j∈S\B,(3/4:ℝ) := by simp
      _ ≤ ∑j∈S\B,q l (x j)^2 := by
        apply sum_le_sum
        intro j hj
        have he : clusterLabel y δ x j=l := (mem_filter.mp (mem_sdiff.mp hj).1).2
        have hh := clusterLabel_close y δ x j (mem_sdiff.mp hj).2
        rw [he] at hh
        exact hq l (x j) hh
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
  have hcard : (S.card:ℝ)≤((S\B).card:ℝ)+(B.card:ℝ) := by
    exact_mod_cast (card_le_card (show S⊆(S\B)∪B by intro j hj; by_cases h:j∈B <;> simp [hj,h])).trans (card_union_le _ _)
  have hgood' := hgood.trans (hm l)
  have hbad : (p:ℝ)*(B.card:ℝ)≤(d:ℝ)/2 := by
    dsimp [B]
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<2*p)).mp hb
    nlinarith
  have hgood'' : (p:ℝ)*((S\B).card:ℝ)≤3*(d:ℝ)/2 := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<8*p)).mp hgood'
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hcard hp.le
  change (p:ℝ)*(S.card:ℝ)≤2*d
  nlinarith
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixBlockEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
open scoped ComplexConjugate
namespace FiniteEntropySeparation
variable {p d : ℕ}
 theorem small_rows_bound (W : Fin d → Fin d → ℝ) (hW : ∀j k,0≤W j k)
    (B : Finset (Fin d)) (hb : (B.card:ℝ)≤(d:ℝ)/4096)
    (hfour : (∑j : Fin d,(∑k : Fin d,W j k)^2)≤4*d) :
    (∑j∈B,∑k : Fin d,W j k)≤(d:ℝ)/32 := by
  have hrows : ∀ j, 0 ≤ ∑ k : Fin d, W j k := fun j => sum_nonneg (fun k _ => hW j k)
  have hc := sq_sum_le_card_mul_sum_sq (s := B) (f := fun j => ∑k : Fin d,W j k)
  have hh : (∑j∈B,(∑k : Fin d,W j k)^2)≤4*d :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)).trans hfour
  have hm := mul_le_mul hb hh (sum_nonneg (fun j _ => pow_nonneg (hrows j) 2)) (by positivity : (0:ℝ)≤d/4096)
  have hd : (0:ℝ)≤d := by positivity
  nlinarith
 theorem clustered_energy_lower [NeZero p] (y : Fin p → ℝ) (δ Δ : ℝ) (x : Fin d → ℝ)
    (hy : ∀i j,i≠j → Δ≤|y i-y j|) (hδ : δ≤Δ/4) (hΔ : 0<Δ)
    (W : Fin d → Fin d → ℝ) (hW : ∀j k,0≤W j k) (hsymm : ∀j k,W j k=W k j)
    (hsecond : 3*(d:ℝ)/4≤∑j,∑k,W j k)
    (hfour : (∑j : Fin d,(∑k : Fin d,W j k)^2)≤4*d)
    (hcomm : (∑j,∑k,(x j-x k)^2*W j k)≤Δ^2*d/64)
    (hb : ((badSpectrum y δ x).card:ℝ)≤(d:ℝ)/4096) :
    (d:ℝ)/2≤∑j,∑k,if clusterLabel y δ x j=clusterLabel y δ x k then W j k else 0 := by
  classical
  let B := badSpectrum y δ x
  have hrows := small_rows_bound W hW B hb hfour
  have hpoint j k : W j k ≤
      (if clusterLabel y δ x j=clusterLabel y δ x k then W j k else 0)+
      (4/Δ^2)*((x j-x k)^2*W j k)+
      (if j∈B then W j k else 0)+(if k∈B then W j k else 0) := by
    have hn := hW j k
    have hc : 0≤(4/Δ^2)*((x j-x k)^2*W j k) := by positivity
    by_cases he : clusterLabel y δ x j=clusterLabel y δ x k
    · simp only [ite_eq_left he]; split_ifs <;> linarith
    by_cases hj : j∈B
    · simp only [ite_eq_right he,ite_eq_left hj]; split_ifs <;> linarith
    by_cases hk : k∈B
    · simp only [ite_eq_right he,ite_eq_left hk]; split_ifs ; linarith
    simp only [ite_eq_right he,ite_eq_right hj,ite_eq_right hk,zero_add,add_zero]
    have hs := clusterLabel_separated y δ Δ x hy hδ hj hk he
    have hs' : Δ^2/4≤(x j-x k)^2 := by nlinarith [sq_abs (x j-x k)]
    have hf : 1≤(4/Δ^2)*(x j-x k)^2 := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hΔ)).mpr
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hf hn
    nlinarith
  have hh := sum_le_sum (fun j (_ : j∈(univ:Finset (Fin d))) => sum_le_sum (fun k (_ : k∈(univ:Finset (Fin d))) => hpoint j k))
  have he1 : (∑j : Fin d,∑k : Fin d,if j∈B then W j k else 0)=∑j∈B,∑k : Fin d,W j k := by
    calc
      _ = ∑j : Fin d,if j∈B then ∑k : Fin d,W j k else 0 := by
        apply sum_congr rfl
        intro j _
        by_cases hj : j∈B <;> simp [hj]
      _ = _ := by simp
  have he2 : (∑j : Fin d,∑k : Fin d,if k∈B then W j k else 0)=∑j∈B,∑k : Fin d,W j k := by
    rw [sum_comm]
    simpa only [hsymm] using he1
  simp only [sum_add_distrib,← mul_sum,he1,he2] at hh
  have hc := mul_le_mul_of_nonneg_left hcomm (show 0≤4/Δ^2 by positivity)
  have hc' : (4/Δ^2)*(∑j,∑k,(x j-x k)^2*W j k)≤(d:ℝ)/16 := by
    calc
      _ ≤ (4/Δ^2)*(Δ^2*(d:ℝ)/64) := hc
      _ = _ := by field_simp [ne_of_gt hΔ]; ring
  linarith
 theorem hermitian_row_energy (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (j : Fin d) :
    ∑k,Complex.normSq (A j k)=((A^2) j j).re := by
  have he k : star (A j k)=A k j := by simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun hA.eq k) j
  rw [pow_two,Matrix.mul_apply,Complex.re_sum]
  apply sum_congr rfl
  intro k _
  rw [← he k,Complex.star_def,Complex.mul_conj,Complex.ofReal_re]
 theorem hermitian_row_fourth (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    (∑j : Fin d,(∑k : Fin d,Complex.normSq (A j k))^2)≤(Matrix.trace (A^4)).re := by
  have hA2 : (A^2).IsHermitian := hA.pow 2
  have ht : (Matrix.trace (A^4)).re=hsNorm (A^2)^2 := by
    rw [hsNorm_sq,← trace_conjTranspose_mul_re,hA2.eq,← pow_add]
  rw [ht,hsNorm_sq]
  apply sum_le_sum
  intro j _
  rw [hermitian_row_energy A hA]
  apply le_trans _ (Finset.single_le_sum (fun k _ => Complex.normSq_nonneg ((A^2) j k)) (mem_univ j))
  simp only [Complex.normSq_apply]
  nlinarith [sq_nonneg ((A^2) j j).im]
 theorem hermitian_entry_symmetric (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (j k : Fin d) :
    Complex.normSq (A j k)=Complex.normSq (A k j) := by
  have he : star (A j k)=A k j := by simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun hA.eq k) j
  rw [← he,Complex.star_def,Complex.normSq_conj]
 theorem commutator_diagonal_entry (A : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℝ) (j k : Fin d) :
    Complex.normSq ((Matrix.diagonal (fun j => (x j:ℂ))*A-A*Matrix.diagonal (fun j => (x j:ℂ))) j k)=
      (x j-x k)^2*Complex.normSq (A j k) := by
  simp only [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  rw [mul_comm (A j k),← sub_mul,← Complex.ofReal_sub,Complex.normSq_mul,Complex.normSq_ofReal]
  ring
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SpectralTestFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset Filter
open scoped Topology ComplexConjugate
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem univariateMoment_continuous (q : Polynomial ℝ) (i : Fin n) : Continuous (fun m : List (Fin n) → ℂ => univariateMoment m q i) := by
  unfold univariateMoment
  fun_prop
 theorem commutatorMoment_continuous (i j : Fin n) : Continuous (fun m : List (Fin n) → ℂ => commutatorMoment m i j) := by
  unfold commutatorMoment
  fun_prop
 theorem univariateMoment_matrix (q : Polynomial ℝ) (a : MatrixCoordinates n d) (i : Fin n) :
    univariateMoment (matrixMoment a) q i=(d:ℝ)⁻¹*∑j,q.eval ((hermitianMatrix_isHermitian a i).eigenvalues j) :=
  matrixUnivariateMoment_eigenvalues q a i
 theorem commutatorMoment_matrix (a : MatrixCoordinates n d) (i j : Fin n) :
    commutatorMoment (matrixMoment a) i j = (d:ℝ)⁻¹*hsNorm (hermitianMatrix a j*hermitianMatrix a i-hermitianMatrix a i*hermitianMatrix a j)^2 := by
  let A := hermitianMatrix a i
  let B := hermitianMatrix a j
  have hA : A.conjTranspose=A := (hermitianMatrix_isHermitian a i).eq
  have hB : B.conjTranspose=B := (hermitianMatrix_isHermitian a j).eq
  rw [hsNorm_sq,← trace_conjTranspose_mul_re]
  change _ = (d:ℝ)⁻¹*(Matrix.trace ((B*A-A*B).conjTranspose*(B*A-A*B))).re
  simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,hA,hB]
  have he : (A*B-B*A)*(B*A-A*B)=A*B*B*A-A*B*A*B-B*A*B*A+B*A*A*B := by noncomm_ring
  rw [he,Matrix.trace_add,Matrix.trace_sub,Matrix.trace_sub]
  unfold commutatorMoment matrixMoment
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  change ((d:ℂ)⁻¹*Matrix.trace (A*(B*(B*A)))-(d:ℂ)⁻¹*Matrix.trace (A*(B*(A*B)))-
    (d:ℂ)⁻¹*Matrix.trace (B*(A*(B*A)))+(d:ℂ)⁻¹*Matrix.trace (B*(A*(A*B)))).re = _
  simp only [← mul_add,← mul_sub,mul_assoc,← Complex.ofReal_natCast,← Complex.ofReal_inv,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
 theorem matrixMoment_second_hs (a : MatrixCoordinates n d) (i : Fin n) :
    (matrixMoment a [i,i]).re=(d:ℝ)⁻¹*hsNorm (hermitianMatrix a i)^2 := by
  rw [hsNorm_sq,← trace_conjTranspose_mul_re,(hermitianMatrix_isHermitian a i).eq]
  simp [matrixMoment,← Complex.ofReal_natCast,← Complex.ofReal_inv]
 theorem matrixMoment_fourth_trace (a : MatrixCoordinates n d) (i : Fin n) :
    (matrixMoment a [i,i,i,i]).re=(d:ℝ)⁻¹*(Matrix.trace (hermitianMatrix a i^4)).re := by
  have he := matrixMoment_replicate a i 4
  simp only [List.replicate_succ,List.replicate_zero] at he
  rw [he]
  simp [← Complex.ofReal_natCast,← Complex.ofReal_inv]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SpectralParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset Filter Set
open scoped Topology
namespace FiniteEntropySeparation
variable {p : ℕ}
 theorem spectralAnnihilator_eval (r : ℝ) :
    (spectralAnnihilator p).eval r=∏l : Fin p,(r-equidiscreteAtom p l) := by
  rw [spectralAnnihilator, Polynomial.eval_prod]
  simp
 theorem spectralGood_isOpen (p : ℕ) (δ Δ : ℝ) : IsOpen {m | spectralGood p δ Δ m} := by
  unfold spectralGood
  simp only [ofPred_and,ofPred_forall]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    exact (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply _))).inter
      ((isOpen_lt (Complex.continuous_re.comp (continuous_apply _)) continuous_const).inter
      (isOpen_lt (commutatorMoment_continuous _ _) continuous_const))
  · exact (isOpen_iInter_of_finite (fun l => isOpen_lt (univariateMoment_continuous _ _) continuous_const)).inter
      (isOpen_lt (univariateMoment_continuous _ _) continuous_const)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SpectralMatrixProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
open scoped ComplexConjugate
namespace FiniteEntropySeparation
variable {p d : ℕ} [NeZero p]
 theorem spectralGood_blocks (hd : 0<d) {δ Δ : ℝ} (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin p,i≠j → Δ≤|equidiscreteAtom p i-equidiscreteAtom p j|)
    (hq : ∀l : Fin p,∀r : ℝ,|r-equidiscreteAtom p l|≤δ → (3:ℝ)/4≤((spectralBasis p l).eval r)^2)
    (a : MatrixCoordinates (p+1) d) (ha : spectralGood p δ Δ (matrixMoment a)) :
    ∃f : Fin d → Fin p,balancedBlocks f ∧ ∃U : unitary (Matrix (Fin d) (Fin d) ℂ),
      (p:ℝ)*d/2≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖^2 := by
  classical
  let x := (hermitianMatrix_isHermitian a (Fin.last p)).eigenvalues
  let U := (hermitianMatrix_isHermitian a (Fin.last p)).eigenvectorUnitary
  let b := rotateCoordinates U a
  let y := equidiscreteAtom p
  let f := clusterLabel y δ x
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hp' : (0:ℝ)<p := by exact_mod_cast NeZero.pos p
  have hdiag : hermitianMatrix b (Fin.last p)=Matrix.diagonal (fun j => (x j:ℂ)) := diagonal_eigenvalues a _
  have hm (l : Fin p) : (∑j : Fin d,((spectralBasis p l).eval (x j))^2)≤9*(d:ℝ)/(8*p) := by
    have hh := ha.2.1 l
    rw [univariateMoment_matrix] at hh
    simp only [Polynomial.eval_pow] at hh
    have hh' := mul_lt_mul_of_pos_left hh hd'
    rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hd'),one_mul] at hh'
    exact hh'.le.trans_eq (by ring)
  have hb : ((badSpectrum y δ x).card:ℝ)≤badFraction p*d := by
    have hh := ha.2.2
    rw [univariateMoment_matrix] at hh
    simp only [Polynomial.eval_pow,spectralAnnihilator_eval] at hh
    have hh' := mul_lt_mul_of_pos_left hh hd'
    rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hd'),one_mul] at hh'
    have hb' := (badSpectrum_product_bound y hδ.le x).trans hh'.le
    have he : (d:ℝ)*(badFraction p*δ^(2*p))=(badFraction p*d)*δ^(2*p) := by ring
    rw [he] at hb'
    exact (mul_le_mul_iff_left₀ (pow_pos hδ _)).mp hb'
  have hb1 : ((badSpectrum y δ x).card:ℝ)≤(d:ℝ)/(2*p) := by
    apply hb.trans
    have hh := mul_le_mul_of_nonneg_right (min_le_right (1/4096:ℝ) (1/(2*p))) hd'.le
    simpa [badFraction,mul_comm,div_eq_mul_inv] using hh
  have hb2 : ((badSpectrum y δ x).card:ℝ)≤(d:ℝ)/4096 := by
    apply hb.trans
    have hh := mul_le_mul_of_nonneg_right (min_le_left (1/4096:ℝ) (1/(2*p))) hd'.le
    simpa [badFraction,mul_comm,div_eq_mul_inv] using hh
  have hf : balancedBlocks f := by
    intro l
    have hh := clusterLabel_rank_bound y δ x (fun l r => (spectralBasis p l).eval r) hq hm hb1 l
    exact_mod_cast hh
  refine ⟨f,hf,U,?_⟩
  rw [blockMask_matrixEnergy]
  have henergy (i : Fin p) : (d:ℝ)/2≤∑j : Fin d,∑k : Fin d,if f j=f k then Complex.normSq (hermitianMatrix b i.castSucc j k) else 0 := by
    let A := hermitianMatrix b i.castSucc
    have hA : A.IsHermitian := hermitianMatrix_isHermitian b i.castSucc
    have hsecond : 3*(d:ℝ)/4≤hsNorm A^2 := by
      have hh := (ha.1 i).1
      rw [← matrixMoment_rotate U a, matrixMoment_second_hs] at hh
      have hh' := mul_lt_mul_of_pos_left hh hd'
      rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hd'),one_mul] at hh'
      exact le_of_lt (by convert hh' using 1 ; ring)
    have hfour : (Matrix.trace (A^4)).re≤4*(d:ℝ) := by
      have hh := (ha.1 i).2.1
      rw [← matrixMoment_rotate U a,matrixMoment_fourth_trace] at hh
      have hh' := mul_lt_mul_of_pos_left hh hd'
      rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hd'),one_mul] at hh'
      exact hh'.le.trans_eq (by ring)
    have hc : (∑j : Fin d,∑k : Fin d,(x j-x k)^2*Complex.normSq (A j k))≤Δ^2*d/64 := by
      have hh := (ha.1 i).2.2
      have he : commutatorMoment (matrixMoment b) i.castSucc (Fin.last p)=commutatorMoment (matrixMoment a) i.castSucc (Fin.last p) := by
        unfold commutatorMoment
        simp only [b,matrixMoment_rotate]
      rw [← he,commutatorMoment_matrix,hdiag,hsNorm_sq] at hh
      simp only [commutator_diagonal_entry] at hh
      have hh' := mul_lt_mul_of_pos_left hh hd'
      rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hd'),one_mul] at hh'
      exact hh'.le.trans_eq (by ring)
    apply clustered_energy_lower y δ Δ x hsep hδΔ hΔ (fun j k => Complex.normSq (A j k))
      (fun j k => Complex.normSq_nonneg _) (hermitian_entry_symmetric A hA)
    · simpa only [hsNorm_sq] using hsecond
    · exact (hermitian_row_fourth A hA).trans hfour
    · exact hc
    · exact hb2
  have hh := sum_le_sum (fun i (_ : i∈(univ:Finset (Fin p))) => henergy i)
  simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_div_assoc] using hh
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
-- module Solutions.OAIQW_FiniteEntropySeparation.WickTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem inner_commutatorKernel {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (i : Fin n) (w : List (Fin n)) (v : H) :
    inner ℂ v (commutatorKernel (vacuumRankOne τ) X i w τ.vacuum) =
      ∑ r : Fin w.length, if w[r.val] = i then
        inner ℂ v (wordEval X (w.take r.val) τ.vacuum) *
          wordMoment τ X (w.drop (r.val + 1)) else 0 := by
  rw [commutatorKernel, sum_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · simp only [vacuumRankOne, mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
      map_smul, inner_smul_right, wordMoment, trace]
    exact mul_comm _ _
  · simp

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem rightAnnihilationN_heat {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (i j : Fin n) :
    star (rightCreationN (σ i)) * heatTuple X (fun k => semicircularN (σ k)) u j =
      heatTuple X (fun k => semicircularN (σ k)) u j * star (rightCreationN (σ i)) +
        if j = i then (Real.sqrt u : ℂ) • vacuumRankOne (tracialVector B N G) else 0 := by
  change _ * (X j + (Real.sqrt u : ℂ) • semicircularN (σ j)) = _
  rw [mul_add, mul_smul_comm, (rightAnnihilationN_background (hs i) (hX j)).eq,
    rightAnnihilationN_semicircularN]
  dsimp [heatTuple]
  by_cases hij : j = i
  · subst j
    simp only [ite_true, add_mul, smul_mul_assoc, add_assoc]
    congr 1
    exact smul_add _ _ _
  · have hneq : σ i ≠ σ j := fun h => hij (hσ h).symm
    simp only [ite_eq_right hij, ite_eq_right hneq, add_zero, add_mul, smul_mul_assoc]

theorem wick_testing {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (js w : List (Fin n)) :
    inner ℂ (basis (noiseWord ((js.map σ).reverse)))
      (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w
        (tracialVector B N G).vacuum) =
      (Real.sqrt u : ℂ) ^ js.length *
        reverseDerivativeMoment (tracialVector B N G)
          (heatTuple X (fun k => semicircularN (σ k)) u) js w := by
  let Z := heatTuple X (fun k => semicircularN (σ k)) u
  change inner ℂ _ (wordEval Z w _) = _ * reverseDerivativeMoment _ Z js w
  induction js generalizing w with
  | nil => simp [reverseDerivativeMoment, wordMoment, trace, tracialVector]
  | cons i js ih =>
    have hvec : basis (noiseWord (((i :: js).map σ).reverse)) =
        rightCreationN (σ i) (basis (noiseWord ((js.map σ).reverse)) : Space B N G) := by
      simp only [List.map_cons, List.reverse_cons, basis, rightCreationN_single, rightN_noiseWord]
    rw [hvec, ← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint]
    have hc := commutator_word (vacuumRankOne (tracialVector B N G))
      (star (rightCreationN (σ i))) Z i (Real.sqrt u : ℂ)
      (rightAnnihilationN_heat J X hX σ hσ hs u i) w
    have hc' := congrArg (fun T : Space B N G →L[ℂ] Space B N G =>
      T (tracialVector B N G).vacuum) hc
    have hz : star (rightCreationN (σ i)) (tracialVector B N G).vacuum = 0 := by
      simp [tracialVector, basis, empty]
    simp only [mul_apply_eq_comp, hz, map_zero, add_apply, zero_add, smul_apply] at hc'
    rw [hc', inner_smul_right, inner_commutatorKernel]
    simp_rw [ih]
    rw [reverseDerivativeMoment, List.length_cons, pow_succ, Finset.mul_sum,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> ring

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CumulantResidual
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
 theorem inner_selfAdjoint_word {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (hX : ∀ i, IsSelfAdjoint (X i)) (i : Fin n) (w : List (Fin n)) :
    inner ℂ (X i τ.vacuum) (wordEval X w τ.vacuum) = wordMoment τ X (i::w) := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    (hX i).star_eq]
  rfl
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TwoNoiseFisher
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
section General
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_sq_sqrt_pair [CompleteSpace H] {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℂ x y = 0) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖(Real.sqrt a : ℂ) • x + (Real.sqrt b : ℂ) • y‖ ^ 2 = a + b := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_left, inner_smul_right, hxy]
  simp [norm_smul, hx, hy,
    Real.norm_eq_abs, Real.sq_sqrt ha, Real.sq_sqrt hb,
    abs_of_nonneg (Real.sqrt_nonneg a), abs_of_nonneg (Real.sqrt_nonneg b)]

end General

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
 theorem noise_basis_test {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (i : Fin n) (w : List (Fin n)) :
    inner ℂ (basis (noiseWord [σ i]))
      (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w
        (tracialVector B N G).vacuum) =
      (Real.sqrt u : ℂ) * derivativeMoment (tracialVector B N G)
        (heatTuple X (fun k => semicircularN (σ k)) u) i w := by
  simpa only [List.map_cons, List.map_nil, List.reverse_singleton, List.length_singleton, pow_one,
    reverseDerivativeMoment, derivativeMoment] using wick_testing J X hX σ hσ hs u [i] w

 theorem semicircularN_vacuum (i : N) :
    semicircularN i (tracialVector B N G).vacuum = basis (noiseWord [i]) := by
  simp [semicircularN, tracialVector, basis, creationN_single, annihilationN_single,
    removeN, empty, noiseWord_cons, noiseWord_nil]
end FreeTensor
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]

omit [NeZero p] in
theorem noiseVector₀_norm [NeZero p] (i : Fin (p+1)) : ‖noiseVector₀ p i‖ = 1 := by
  simp [noiseVector₀, basis, lp.norm_single (E := fun _ => ℂ) (p := 2)]

omit [NeZero p] in
theorem noiseVector₁_norm [NeZero p] (i : Fin (p+1)) : ‖noiseVector₁ p i‖ = 1 := by
  simp [noiseVector₁, basis, lp.norm_single (E := fun _ => ℂ) (p := 2)]
 theorem noiseVector_orthogonal (i j : Fin (p+1)) : inner ℂ (noiseVector₀ p i) (noiseVector₁ p j) = 0 := by
  have hneq : [initialIndex p i] ≠ [auxiliaryIndex p j] := by
    intro he
    have he' : initialIndex p i = auxiliaryIndex p j := List.cons.inj he |>.1
    exact auxiliaryIndex_fresh p j ⟨i,he'⟩
  exact noise_basis_orthonormal.inner_eq_zero hneq

 theorem noiseVector₀_C (i j : Fin (p+1)) : inner ℂ (noiseVector₀ p i) (C p j (τ p).vacuum) = 0 := by
  have ht := noise_basis_test ∅ (C p) (C_mem_background p ∅) (initialIndex p)
    (initialIndex_injective p) (by simp) 0 i [j]
  simpa [heatTuple, wordEval, noiseVector₀] using ht
 theorem noiseVector₁_C (i j : Fin (p+1)) : inner ℂ (noiseVector₁ p i) (C p j (τ p).vacuum) = 0 := by
  have ht := noise_basis_test ∅ (C p) (C_mem_background p ∅) (auxiliaryIndex p)
    (auxiliaryIndex_injective p) (by simp) 0 i [j]
  simpa [heatTuple, wordEval, noiseVector₁] using ht

 theorem doublyNoised_vacuum (h s : ℝ) (i : Fin (p+1)) :
    doublyNoised p h s i (τ p).vacuum = C p i (τ p).vacuum +
      ((Real.sqrt h : ℂ) • noiseVector₀ p i + (Real.sqrt s : ℂ) • noiseVector₁ p i) := by
  change (C p i (τ p).vacuum + (Real.sqrt h : ℂ) •
    semicircularN (initialIndex p i) (τ p).vacuum) +
    (Real.sqrt s : ℂ) • semicircularN (auxiliaryIndex p i) (τ p).vacuum = _
  rw [semicircularN_vacuum, semicircularN_vacuum]
  simp only [noiseVector₀, noiseVector₁, add_assoc]

 theorem doublyNoised_variance (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) (i : Fin (p+1)) :
    ‖doublyNoised p h s i (τ p).vacuum‖ ^ 2 = ‖C p i (τ p).vacuum‖ ^ 2 + h+s := by
  have hc : inner ℂ (C p i (τ p).vacuum)
      ((Real.sqrt h : ℂ) • noiseVector₀ p i + (Real.sqrt s : ℂ) • noiseVector₁ p i) = 0 := by
    rw [← inner_conj_symm, inner_add_left, inner_smul_left, inner_smul_left,
      noiseVector₀_C, noiseVector₁_C]
    simp
  rw [doublyNoised_vacuum, norm_add_sq (𝕜 := ℂ), hc,
    norm_sq_sqrt_pair (noiseVector₀_norm p i) (noiseVector₁_norm p i)
      (noiseVector_orthogonal p i i) h s hh hs]
  simp
  ring

end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SignalCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]

omit [NeZero p] in
theorem fockMoments_one [NeZero p] (i : Fin p) : fockMoments p [i] = 0 := by
  have he := congrFun (fockMoments_eq p) [i]
  simpa [subst_cons, conv_nil, quadratic] using he

omit [NeZero p] in
theorem fockMoments_two [NeZero p] (i j : Fin p) : fockMoments p [i,j] = if j=i then 1 else 0 := by
  have he := congrFun (fockMoments_eq p) [i,j]
  simp only [Pi.add_apply, unit_cons, zero_add, subst_cons, conv_cons, subst_nil, conv_nil,
    FreeSeries.deriv_apply, quadratic] at he
  simpa [fockMoments] using he
 theorem C_offDiagonal (i j : Fin (p+1)) (hij : j ≠ i) : signalMoments p [i,j] = 0 := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact (hij rfl).elim
    | cast j =>
      have he := signal_option_moments p [none, some j]
      simpa [fockMoments_one] using he
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      have he := signal_option_moments p [some i, none]
      simpa [fockMoments_one] using he
    | cast j =>
      have hj : j ≠ i := fun h => hij (congrArg Fin.castSucc h)
      have he := signal_option_moments p [some i, some j]
      simpa [fockMoments_two, hj] using he
 theorem C_covariance (i j : Fin (p+1)) :
    signalMoments p [i,j] = if j=i then (variance p i : ℂ) else 0 := by
  by_cases hj : j=i
  · subst j
    rw [ite_eq_left rfl]
    have he := inner_selfAdjoint_word (τ p) (C p) (C_selfAdjoint p) i [i]
    simpa [signalMoments, wordEval, variance, inner_self_eq_norm_sq_to_K] using he.symm
  · rw [ite_eq_right hj]; exact C_offDiagonal p i j hj
 theorem variance_last_le_one (hp : 2 ≤ p) : variance p (Fin.last p) ≤ 1 := by
  have he := (C p (Fin.last p)).le_opNorm (τ p).vacuum
  rw [(τ p).norm_vacuum, mul_one, C_last] at he
  have hn := equidiscreteSignal_norm_le (B := Fin p) (N := Fin ((p+1)+(p+1))) p hp
  unfold variance
  rw [C_last]
  nlinarith [norm_nonneg (equidiscreteSignal p (τ p).vacuum)]
 theorem variance_castSucc (i : Fin p) : variance p i.castSucc = 1 := by
  have he := C_covariance p i.castSucc i.castSucc
  have ht := signal_option_moments p [some i,some i]
  simp only [List.map_cons, List.map_nil, optionFin_some, List.filterMap_cons, List.filterMap_nil,
    id_eq, fockMoments_two, ite_true] at ht
  simp at ht
  rw [ite_eq_left rfl, ht] at he
  exact_mod_cast he.symm
 theorem variance_le_one (hp : 2 ≤ p) (i : Fin (p+1)) : variance p i ≤ 1 := by
  induction i using Fin.lastCases with
  | last => exact variance_last_le_one p hp
  | cast i => rw [variance_castSucc]
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FisherDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem X_variance (u : ℝ) (hu : 0 ≤ u) (i : Fin (p+1)) :
    ‖X p u i (τ p).vacuum‖^2 = variance p i + u := by
  simpa [doublyNoised, heatTuple, variance] using doublyNoised_variance p u 0 hu (le_refl 0) i
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.UniformMicrostateTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace FiniteEntropySeparation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
 theorem diagonalMicrostates_uniform_open (R : ℝ) (O : Set (List (Fin n) → ℂ)) (hO : IsOpen O)
    (hX : wordMoment τ X ∈ O) :
    ∀ᶠk : ℕ in atTop,∀d : ℕ,∀a : MatrixCoordinates n d,a∈diagonalMicrostates τ X R k d → matrixMoment a∈O := by
  classical
  by_contra h
  have hb : ∀N : ℕ,∃k,N≤k ∧ ∃d : ℕ,∃a : MatrixCoordinates n d,
      a∈diagonalMicrostates τ X R k d ∧ matrixMoment a∉O := by
    simpa only [eventually_atTop,not_exists,not_forall,Classical.not_imp,exists_prop] using h
  obtain ⟨I,hI,hi⟩ := exists_strictMono_diagonal (fun _ k => ∃d : ℕ,∃a : MatrixCoordinates n d,
    a∈diagonalMicrostates τ X R k d ∧ matrixMoment a∉O) (by
      intro k L
      obtain ⟨j,hj,hh⟩ := hb (L+1)
      exact ⟨j,by omega,hh⟩)
  choose D a ha hbad using hi
  have hlim : Tendsto (fun k => matrixMoment (a k)) atTop (𝓝 (wordMoment τ X)) := by
    apply tendsto_pi_nhds.mpr
    intro w
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _))
    · filter_upwards [hI.tendsto_atTop.eventually (eventually_ge_atTop w.length)] with k hk
      exact ((ha k).2 w hk).le
    · exact (show Tendsto (fun k : ℕ => (k+1:ℝ)⁻¹) atTop (𝓝 0) by
        simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hI.tendsto_atTop
  have hev := hlim.eventually (hO.mem_nhds hX)
  obtain ⟨k,hk⟩ := hev.exists
  exact hbad k hk
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TotalSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset Filter Set
open scoped Topology
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem totalSecond_continuous : Continuous (totalSecond (n := n)) := by
  unfold totalSecond
  fun_prop
 theorem totalSecond_matrix (a : MatrixCoordinates n d) : totalSecond (matrixMoment a)=(d:ℝ)⁻¹*‖a‖^2 := by
  simp only [totalSecond,matrixMoment_second_hs,hsNorm_sq,← mul_sum,hermitianChart_normSq]
 theorem totalSecond_norm_bound (hd : 0<d) {p : ℕ} (a : MatrixCoordinates (p+1) d)
    (ha : totalSecond (matrixMoment a)<4*p) : ‖a‖≤2*Real.sqrt ((p:ℝ)*d) := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  rw [totalSecond_matrix] at ha
  have hh := mul_lt_mul_of_pos_left ha hd'
  rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hd'),one_mul] at hh
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : 0≤(p:ℝ)*d)]
  nlinarith
 section Operators
 variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M)
 theorem wordMoment_second (X : Fin n → H →L[ℂ] H) (hX : ∀i,IsSelfAdjoint (X i)) (i : Fin n) :
    (wordMoment τ X [i,i]).re=‖X i τ.vacuum‖^2 := by
  have he := inner_selfAdjoint_word τ X hX i [i]
  simpa [wordEval,inner_self_eq_norm_sq_to_K,← Complex.ofReal_pow] using (congrArg Complex.re he).symm
 end Operators
namespace Model
variable (p : ℕ) [NeZero p]
 theorem totalSecond_X (h : ℝ) (hh : 0≤h) :
    totalSecond (wordMoment (τ p) (X p h))=∑i : Fin (p+1),(variance p i+h) := by
  simp only [totalSecond,wordMoment_second (τ p) (X p h) (X_selfAdjoint p h),X_variance p h hh]
 theorem totalSecond_X_lt (hp : 2≤p) {h : ℝ} (hh : 0≤h) (hh1 : h<1) :
    totalSecond (wordMoment (τ p) (X p h))<4*p := by
  rw [totalSecond_X p h hh]
  have hb : (∑i : Fin (p+1),(variance p i+h))≤(p+1:ℝ)*(1+h) := by
    calc
      _ ≤ ∑i : Fin (p+1),(1+h) := sum_le_sum (fun i _ => add_le_add (variance_le_one p hp i) (le_refl h))
      _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  nlinarith
 theorem diagonalMicrostates_norm_eventually (hp : 2≤p) {h : ℝ} (hh : 0≤h) (hh1 : h<1) (R : ℝ) :
    ∀ᶠk : ℕ in atTop,∀d : ℕ,0<d → ∀a : MatrixCoordinates (p+1) d,
      a∈diagonalMicrostates (τ p) (X p h) R k d → ‖a‖≤2*Real.sqrt ((p:ℝ)*d) := by
  have he := diagonalMicrostates_uniform_open (τ p) (X p h) R {m | totalSecond m<4*p}
    (isOpen_lt totalSecond_continuous continuous_const) (totalSecond_X_lt p hp hh hh1)
  filter_upwards [he] with k hk d hd a ha
  exact totalSecond_norm_bound hd a (hk d a ha)
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.BlockEnsembleLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
namespace FiniteEntropySeparation
variable {p d : ℕ}
 theorem matrixHeatLaw_block_lower (hp : 2≤p) (hd : 0<d) {t v : ℝ} (ht : 0<t)
    (hv : 1≤v) (htv : t≤v) (hpt : 256*t≤p)
    (μ : Measure (MatrixCoordinates (p+1) d)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐa ∂μ,‖a‖≤2*Real.sqrt ((p:ℝ)*d) ∧
      ∃f : Fin d → Fin p,balancedBlocks f ∧ ∃U : unitary (Matrix (Fin d) (Fin d) ℂ),
      Real.sqrt ((p:ℝ)*d)/2≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖) :
    ENNReal.ofReal (1/2:ℝ)≤ matrixHeatLaw μ t
      (blockEvent p d (Real.sqrt ((p:ℝ)*d)/4) (4*Real.sqrt (v*p*d))) := by
  have htd : 0<t/(d:ℝ) := div_pos ht (by exact_mod_cast hd)
  let E := blockEvent p d (Real.sqrt ((p:ℝ)*d)/4) (4*Real.sqrt (v*p*d))
  have hE : MeasurableSet E := (blockEvent_isClosed hd _ _).measurableSet
  change _≤(volume.withDensity (fun x => ENNReal.ofReal (smoothedDensity μ (t/d) x))) E
  rw [← smoothedLaw_eq μ htd,Measure.map_apply (by fun_prop) hE]
  have : IsProbabilityMeasure (normalLaw (ι := MatrixIndex (p+1) d) (t/d)) := normalLaw_probability htd
  rw [Measure.prod_apply (hE.preimage (show Measurable (fun z : MatrixCoordinates (p+1) d × MatrixCoordinates (p+1) d => z.1+z.2) from by fun_prop))]
  calc
    _ = ∫⁻a : MatrixCoordinates (p+1) d,ENNReal.ofReal (1/2:ℝ) ∂μ := by simp
    _ ≤ _ := lintegral_mono_ae (hμ.mono (fun a ha => blockEvent_conditional_lower hp hd ht hv htv hpt a ha.1 ha.2))
namespace Model
variable (p : ℕ) [NeZero p]
 theorem diagonalMicrostates_blocks_eventually {δ Δ : ℝ} (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin p,i≠j → Δ≤|equidiscreteAtom p i-equidiscreteAtom p j|)
    (hq : ∀l : Fin p,∀r : ℝ,|r-equidiscreteAtom p l|≤δ → (3:ℝ)/4≤((spectralBasis p l).eval r)^2)
    {h : ℝ} (hh : spectralGood p δ Δ (wordMoment (τ p) (X p h))) (R : ℝ) :
    ∀ᶠk : ℕ in atTop,∀d : ℕ,0<d → ∀a : MatrixCoordinates (p+1) d,
      a∈diagonalMicrostates (τ p) (X p h) R k d →
      ∃f : Fin d → Fin p,balancedBlocks f ∧ ∃U : unitary (Matrix (Fin d) (Fin d) ℂ),
      Real.sqrt ((p:ℝ)*d)/2≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖ := by
  have he := diagonalMicrostates_uniform_open (τ p) (X p h) R {m | spectralGood p δ Δ m}
    (spectralGood_isOpen p δ Δ) hh
  filter_upwards [he] with k hk d hd a ha
  obtain ⟨f,hf,U,hU⟩ := spectralGood_blocks hd hδ hΔ hδΔ hsep hq a (hk d a ha)
  refine ⟨f,hf,U,?_⟩
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  rw [div_pow,Real.sq_sqrt (by positivity : 0≤(p:ℝ)*d)]
  nlinarith
 theorem matrixHeatLaw_blocks_eventually_oai (hp : 2≤p) {δ Δ : ℝ} (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin p,i≠j → Δ≤|equidiscreteAtom p i-equidiscreteAtom p j|)
    (hq : ∀l : Fin p,∀r : ℝ,|r-equidiscreteAtom p l|≤δ → (3:ℝ)/4≤((spectralBasis p l).eval r)^2)
    {h t : ℝ} (hh0 : 0<h) (hh1 : h<1) (hh : spectralGood p δ Δ (wordMoment (τ p) (X p h)))
    (ht : 0<t) (hpt : 256*t≤p) (R : ℝ)
    (D : ℕ → ℕ) (hD : ∀k,0<D k)
    (μ : (k:ℕ) → Measure (MatrixCoordinates (p+1) (D k))) [∀k,IsProbabilityMeasure (μ k)]
    (hμ : ∀k,∀ᵐa ∂μ k,a∈diagonalMicrostates (τ p) (X p h) R k (D k)) :
    ∀ᶠk in atTop,ENNReal.ofReal (1/2:ℝ)≤ matrixHeatLaw (μ k) t
      (blockEvent p (D k) (Real.sqrt ((p:ℝ)*D k)/4) (4*Real.sqrt ((1+h+t)*p*D k))) := by
  filter_upwards [diagonalMicrostates_norm_eventually p hp hh0.le hh1 R,
    diagonalMicrostates_blocks_eventually p hδ hΔ hδΔ hsep hq hh R] with k hk hb
  apply matrixHeatLaw_block_lower hp (hD k) ht (by linarith) (by linarith) hpt (μ k)
  filter_upwards [hμ k] with a ha
  exact ⟨hk (D k) (hD k) a ha,hb (D k) (hD k) a ha⟩
end Model
end FiniteEntropySeparation

end

end OAI
end

theorem solution : type_of% @OAI.FiniteEntropySeparation.Model.matrixHeatLaw_blocks_eventually_oai := @OAI.FiniteEntropySeparation.Model.matrixHeatLaw_blocks_eventually_oai
