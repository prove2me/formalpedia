-- Prove2me | solution 1 for OAI.FiniteEntropySeparation.FreeTensor.freeFisher_le_liminf_matrixFisher
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:19:31.491189+00:00
-- url     : https://prove2.me/submissions/2c4ef6f6-d34d-464d-896a-947da376ef38

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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
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

theorem ConjugateSystem.unique {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ η : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (hη : ConjugateSystem τ X η) : ξ = η := by
  funext i
  have hmem : ξ i - η i ∈ polynomialL2 τ X :=
    (polynomialL2 τ X).sub_mem (hξ i).1 (hη i).1
  have hker : polynomialL2 τ X ≤ (innerSL ℂ (ξ i - η i)).ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      change inner ℂ (ξ i - η i) (wordEval X w τ.vacuum) = 0
      rw [inner_sub_left, (hξ i).2 w, (hη i).2 w, sub_self]
    · exact (innerSL ℂ (ξ i - η i)).isClosed_ker
  have hd : inner ℂ (ξ i - η i) (ξ i - η i) = 0 := hker hmem
  exact sub_eq_zero.mp ((inner_self_eq_zero).mp hd)

theorem freeFisher_eq_of_conjugate {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) :
    freeFisher τ X = ENNReal.ofReal (∑ i, ‖ξ i‖ ^ 2) := by
  apply le_antisymm
  · exact iInf_le_of_le ξ (iInf_le_of_le hξ le_rfl)
  · refine le_iInf fun η => le_iInf fun hη => ?_
    rw [hξ.unique τ hη]

 theorem wordVector_mem_polynomialL2 {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (w : List (Fin n)) :
    wordEval X w τ.vacuum ∈ polynomialL2 τ X :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, rfl⟩)

 theorem projectedConjugate_system {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (η : Fin n → H)
    (hη : ∀ i w, inner ℂ (η i) (wordEval X w τ.vacuum) = derivativeMoment τ X i w) :
    ConjugateSystem τ X (projectedConjugate τ X η) := by
  intro i
  refine ⟨(polynomialL2 τ X).starProjection_apply_mem _, fun w => ?_⟩
  have h := (polynomialL2 τ X).starProjection_inner_eq_zero (η i)
    (wordEval X w τ.vacuum) (wordVector_mem_polynomialL2 τ X w)
  rw [inner_sub_left, hη i w] at h
  exact (sub_eq_zero.mp h).symm

theorem freeFisher_le_testVectors {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (η : Fin n → H)
    (hη : ∀ i w, inner ℂ (η i) (wordEval X w τ.vacuum) = derivativeMoment τ X i w) :
    freeFisher τ X ≤ ENNReal.ofReal (∑ i, ‖η i‖ ^ 2) := by
  rw [freeFisher_eq_of_conjugate τ (projectedConjugate_system τ X η hη)]
  apply ENNReal.ofReal_le_ofReal
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) ((polynomialL2 τ X).norm_starProjection_apply_le _) _

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
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped Topology
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 theorem normalKernel_hasDeriv_coordinate_at (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) (r : ℝ) :
    HasDerivAt (fun t : ℝ => normalKernel s (x+t • EuclideanSpace.single i 1))
      (normalGradient s (x+r • EuclideanSpace.single i 1) i) r := by
  have hd : HasDerivAt (fun t : ℝ => ‖x+t • EuclideanSpace.single i 1‖^2) (2*(x i+r)) r := by
    have h := ((hasDerivAt_const r x).add ((hasDerivAt_id r).smul_const (EuclideanSpace.single i 1))).norm_sq
    simpa [real_inner_comm,PiLp.inner_apply,EuclideanSpace.single] using h
  have h := ((hasDerivAt_const r (-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s))).sub (hd.div_const (2*s))).exp
  convert h using 1
  · rfl
  · dsimp only [Pi.sub_apply,normalGradient]
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,EuclideanSpace.single,PiLp.single_apply,ite_true,mul_one,normalKernel]
    ring
 omit [DecidableEq ι] in
 theorem normalGradient_continuous (s : ℝ) (i : ι) : Continuous (fun x : EuclideanSpace ℝ ι => normalGradient s x i) := by
  unfold normalGradient
  exact (((PiLp.continuous_apply 2 _ i).neg).div_const s).mul (normalKernel_continuous_space s)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CompactIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace FiniteEntropySeparation
variable {E : Type u1} {F : Type u2} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
 omit [NormedSpace ℝ E] [BorelSpace E] [NormedSpace ℝ F] in
 theorem integrable_of_compact_ae (μ : Measure E) [IsFiniteMeasure μ] {K : Set E} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) {f : E → F} (hm : AEStronglyMeasurable f μ) (hf : ContinuousOn f K) : Integrable f μ := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hf
  apply (integrable_const C).mono' hm
  filter_upwards [hμ] with x hx
  exact hC x hx
 theorem hasDerivAt_integral_compact {E : Type u1} {F : Type u2}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [SecondCountableTopology E] (μ : Measure E) [IsFiniteMeasure μ] {K : Set E} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) (f f' : ℝ → E → F) {a b t : ℝ} (ha : a<t) (hb : t<b)
    (hf : ∀s∈Icc a b,Continuous (f s)) (hf' : ∀s∈Icc a b,Continuous (f' s))
    (hc : ContinuousOn (fun z : ℝ × E => f' z.1 z.2) (Icc a b ×ˢ K))
    (hd : ∀s∈Icc a b,∀x∈K,HasDerivAt (fun u => f u x) (f' s x) s) :
    Integrable (f' t) μ ∧ HasDerivAt (fun u => ∫ x,f u x ∂μ) (∫ x,f' t x ∂μ) t := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hc
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Icc a b) (bound := fun _ => C) (Icc_mem_nhds ha hb)
  · filter_upwards [Icc_mem_nhds ha hb] with s hs
    exact (hf s hs).aestronglyMeasurable
  · exact integrable_of_compact_ae μ hK hμ (hf t ⟨ha.le,hb.le⟩).aestronglyMeasurable (hf t ⟨ha.le,hb.le⟩).continuousOn
  · exact (hf' t ⟨ha.le,hb.le⟩).aestronglyMeasurable
  · filter_upwards [hμ] with x hx s hs
    exact hC (s,x) ⟨hs,hx⟩
  · exact integrable_const _
  · filter_upwards [hμ] with x hx s hs
    exact hd s hs x hx
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
 theorem smoothedDensity_pos (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0<s) (x : EuclideanSpace ℝ ι) : 0<smoothedDensity μ s x := by
  rw [smoothedDensity,integral_pos_iff_support_of_nonneg (fun a => (normalKernel_pos _ _).le) (normalKernel_integrable_finite μ hs x)]
  have h : Function.support (fun a => normalKernel s (x-a))=univ := by
    ext a; simp [Function.mem_support,(normalKernel_pos s (x-a)).ne']
  simp [h]
 theorem smoothedDensity_continuous (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) : Continuous (smoothedDensity μ s) := by
  apply continuous_of_dominated (bound := fun _ => Real.exp (-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)))
  · intro x; exact (normalKernel_integrable_finite μ hs x).aestronglyMeasurable
  · intro x; exact ae_of_all _ (fun a => by change ‖normalKernel s (x-a)‖≤_; rw [Real.norm_eq_abs,abs_of_pos (normalKernel_pos _ _)]; exact normalKernel_le s hs _)
  · exact integrable_const _
  · exact ae_of_all _ (fun a => (normalKernel_continuous_space s).comp (continuous_id.sub continuous_const))
 theorem smoothedDensity_hasDeriv_coordinate [DecidableEq ι] (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hμ : ∀ᵐ a ∂μ,a∈K)
    (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) (r : ℝ) :
    HasDerivAt (fun t => smoothedDensity μ s (x+t • EuclideanSpace.single i 1))
      (smoothedGradient μ s (x+r • EuclideanSpace.single i 1) i) r := by
  apply (hasDerivAt_integral_compact μ hK hμ (fun t a => normalKernel s (x+t • EuclideanSpace.single i 1-a))
    (fun t a => normalGradient s (x+t • EuclideanSpace.single i 1-a) i) (a := r-1) (b := r+1) (by linarith) (by linarith) ?_ ?_ ?_ ?_).2
  · intro t ht; exact (normalKernel_continuous_space s).comp (continuous_const.sub continuous_id)
  · intro t ht; exact (normalGradient_continuous s i).comp (continuous_const.sub continuous_id)
  · exact ((normalGradient_continuous s i).comp ((continuous_const.add (continuous_fst.smul continuous_const)).sub continuous_snd)).continuousOn
  · intro t ht a ha
    simpa only [add_sub_right_comm] using normalKernel_hasDeriv_coordinate_at s (x-a) i t
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
 theorem matrixMoment_continuous {n d : ℕ} (w : List (Fin n)) :
    Continuous (fun a : MatrixCoordinates n d => matrixMoment a w) := by
  have hp : Continuous (fun a : MatrixCoordinates n d => (w.map (hermitianMatrix a)).prod) := by
    induction w with
    | nil => simpa using (continuous_const : Continuous (fun _ : MatrixCoordinates n d => (1 : Matrix (Fin d) (Fin d) ℂ)))
    | cons i w ih => simpa using (hermitianMatrix_continuous i).matrix_mul ih
  unfold matrixMoment Matrix.trace
  exact continuous_const.mul (continuous_finsetSum _ (fun i _ => hp.matrix_elem i i))
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
 theorem const_mul {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (r : ℝ) :
    IsRealPolynomial (fun x => r*f x) := (const r).mul hf
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
 theorem hasDerivAt {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (i : ι) (x : ι → ℝ) :
    HasDerivAt (fun t => f (Function.update x i t)) (complexCoordinateDerivative f i x) (x i) := by
  rw [hf.coordinateDerivative_eq]
  exact hf.hasCoordinateDeriv i x
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
 theorem matrix_entry_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (j k : Fin d) :
    ‖A j k‖ ≤ matrixOpNorm A := by
  have h := matrix_column_bound A k
  have hs := single_le_sum (fun i (_ : i ∈ (univ : Finset (Fin d))) => Complex.normSq_nonneg (A i k)) (mem_univ j)
  rw [Complex.normSq_eq_norm_sq] at hs
  have hn := (norm_nonneg (A j k))
  have hN := matrixOpNorm_nonneg A
  nlinarith
 theorem matrix_trace_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖Matrix.trace A‖ ≤ (d:ℝ)*matrixOpNorm A := by
  calc
    _ ≤ ∑ j, ‖A j j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, matrixOpNorm A := sum_le_sum (fun j _ => matrix_entry_bound A j j)
    _ = _ := by simp
 theorem matrix_normalized_trace_bound {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖(d:ℂ)⁻¹*Matrix.trace A‖ ≤ matrixOpNorm A := by
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h := matrix_trace_bound A
  calc
    (d:ℝ)⁻¹*‖Matrix.trace A‖ ≤ (d:ℝ)⁻¹*((d:ℝ)*matrixOpNorm A) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hd.ne'), one_mul]
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
-- module Solutions.OAIQW_FiniteEntropySeparation.FisherVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter
namespace FiniteEntropySeparation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem conjugate_polynomial_pairing {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (i : Fin n) (p : WordPolynomial n) :
    inner ℂ (ξ i) (polynomialVector τ X p) = polynomialDerivative τ X i p := by
  simp only [polynomialVector, polynomialDerivative, Finsupp.linearCombination_apply,
    Finsupp.sum, inner_sum, inner_smul_right, (hξ i).2, smul_eq_mul]

theorem norm_sq_eq_iSup_dense {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type} (v : ι → H) (ξ : H)
    (hξ : ξ ∈ (Submodule.span ℂ (Set.range v)).topologicalClosure) :
    ENNReal.ofReal (‖ξ‖ ^ 2) =
      ⨆ p : ι →₀ ℂ, ENNReal.ofReal
        (2 * (inner ℂ ξ (Finsupp.linearCombination ℂ v p)).re -
          ‖Finsupp.linearCombination ℂ v p‖ ^ 2) := by
  let Q : H → ℝ := fun z => 2 * (inner ℂ ξ z).re - ‖z‖ ^ 2
  have hQ : Continuous Q := by fun_prop
  let b := ⨆ p : ι →₀ ℂ, ENNReal.ofReal (Q (Finsupp.linearCombination ℂ v p))
  change ENNReal.ofReal (‖ξ‖ ^ 2) = b
  apply le_antisymm
  · have hc : IsClosed {z : H | ENNReal.ofReal (Q z) ≤ b} :=
      isClosed_le (ENNReal.continuous_ofReal.comp hQ) continuous_const
    have hs : (Submodule.span ℂ (Set.range v) : Set H) ⊆ {z | ENNReal.ofReal (Q z) ≤ b} := by
      intro z hz
      rw [← Finsupp.range_linearCombination] at hz
      obtain ⟨p,rfl⟩ := hz
      exact le_iSup (fun p : ι →₀ ℂ => ENNReal.ofReal (Q (Finsupp.linearCombination ℂ v p))) p
    have hh := hc.closure_subset_iff.mpr hs hξ
    have he : Q ξ = ‖ξ‖ ^ 2 := by
      have hself : (inner ℂ ξ ξ).re = ‖ξ‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) ξ).symm
      dsimp [Q]
      rw [hself]
      ring
    change ENNReal.ofReal (Q ξ) ≤ b at hh
    rwa [he] at hh
  · refine iSup_le fun p => ENNReal.ofReal_le_ofReal ?_
    have h := norm_sub_sq (𝕜 := ℂ) ξ (Finsupp.linearCombination ℂ v p)
    change ‖ξ - Finsupp.linearCombination ℂ v p‖ ^ 2 =
      ‖ξ‖ ^ 2 - 2 * (inner ℂ ξ (Finsupp.linearCombination ℂ v p)).re +
        ‖Finsupp.linearCombination ℂ v p‖ ^ 2 at h
    dsimp [Q]
    nlinarith [sq_nonneg ‖ξ - Finsupp.linearCombination ℂ v p‖]

 theorem freeFisher_variational {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) :
    freeFisher τ X = ∑ i, ⨆ p : WordPolynomial n, ENNReal.ofReal (fisherTest τ X i p) := by
  rw [freeFisher_eq_of_conjugate τ hξ, ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
  apply Finset.sum_congr rfl
  intro i _
  have h := norm_sq_eq_iSup_dense (fun w => wordEval X w τ.vacuum) (ξ i) (hξ i).1
  change ENNReal.ofReal (‖ξ i‖ ^ 2) =
    ⨆ p : WordPolynomial n, ENNReal.ofReal
      (2 * (inner ℂ (ξ i) (polynomialVector τ X p)).re - ‖polynomialVector τ X p‖ ^ 2) at h
  simpa only [conjugate_polynomial_pairing τ hξ, fisherTest] using h

 theorem freeFisher_lt_top_iff {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) :
    freeFisher τ X < ⊤ ↔ ∃ ξ, ConjugateSystem τ X ξ := by
  constructor
  · intro h
    by_contra! hn
    have he : freeFisher τ X = ⊤ := by simp [freeFisher, hn]
    rw [he] at h
    exact lt_irrefl _ h
  · rintro ⟨ξ,hξ⟩
    rw [freeFisher_eq_of_conjugate τ hξ]
    exact ENNReal.ofReal_lt_top

 theorem exists_conjugate_of_fisher_le {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (c : ℝ)
    (h : freeFisher τ X ≤ ENNReal.ofReal c) : ∃ ξ, ConjugateSystem τ X ξ :=
  (freeFisher_lt_top_iff τ X).mp (h.trans_lt ENNReal.ofReal_lt_top)

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixScoreWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem matrixScoreWord_polynomial (w : List (Fin n)) (j k : Fin d) :
    IsComplexPolynomial (matrixScoreWord w j k) :=
  ((IsMatrixPolynomial.const (hermitianBasis j k)).mul
    (IsMatrixPolynomial.word (fun i a b => coordinateMatrix_polynomial i a b) w)).trace
 theorem matrixScoreWord_derivative (w : List (Fin n)) (i : Fin n) (j k : Fin d) (x : MatrixIndex n d → ℝ) :
    complexCoordinateDerivative (matrixScoreWord w j k) (i,j,k) x =
      ∑r : Fin w.length, if w[r.val]=i then
        Matrix.trace (hermitianBasis j k*matrixWord (coordinateMatrix x) (w.take r.val)*hermitianBasis j k*
          matrixWord (coordinateMatrix x) (w.drop (r.val+1))) else 0 := by
  have hd := hasDerivAt_matrix_mul
    (A := fun _ : ℝ => hermitianBasis j k) (A' := 0)
    (fun a b => hasDerivAt_const (x (i,j,k)) (hermitianBasis j k a b))
    (hasDerivAt_matrixWord (coordinateMatrix_hasDeriv x (i,j,k)) w)
  have ht := HasDerivAt.sum (u := univ) (fun a _ => hd a a)
  have he := ht.deriv
  simp only [Finset.sum_fn] at he
  change complexCoordinateDerivative (matrixScoreWord w j k) (i,j,k) x = _ at he
  rw [he]
  simp only [Function.update_eq_self,zero_mul,zero_add,Matrix.mul_apply,Matrix.add_apply,
    Matrix.zero_apply,zero_mul,zero_add]
  change Matrix.trace (hermitianBasis j k*matrixWordVariation (coordinateMatrix x)
    (fun a => if i=a then hermitianBasis j k else 0) w) = _
  rw [matrixWordVariation,mul_sum,Matrix.trace_sum]
  apply sum_congr rfl
  intro r _
  by_cases h : w[r.val]=i
  · simp [h,mul_assoc]
  · simp [h,Ne.symm h]
 theorem hermitianBasis_contract_trace (U V : Matrix (Fin d) (Fin d) ℂ) :
    (∑j,∑k,Matrix.trace (hermitianBasis j k*U*hermitianBasis j k*V)) = Matrix.trace U*Matrix.trace V := by
  calc
    _ = Matrix.trace ((∑j,∑k,hermitianBasis j k*U*hermitianBasis j k)*V) := by
      simp only [sum_mul,Matrix.trace_sum]
    _ = _ := by rw [hermitianBasis_contract,smul_mul_assoc,one_mul,Matrix.trace_smul,smul_eq_mul]
 theorem matrixScoreWord_divergence (w : List (Fin n)) (i : Fin n) (x : MatrixIndex n d → ℝ) :
    (∑j,∑k,complexCoordinateDerivative (matrixScoreWord w j k) (i,j,k) x) =
      ∑r : Fin w.length, if w[r.val]=i then
        Matrix.trace (matrixWord (coordinateMatrix x) (w.take r.val))*
          Matrix.trace (matrixWord (coordinateMatrix x) (w.drop (r.val+1))) else 0 := by
  simp_rw [matrixScoreWord_derivative]
  have hreorder (f : Fin d → Fin d → Fin w.length → ℂ) :
      (∑j,∑k,∑r,f j k r) = ∑r,∑j,∑k,f j k r := by
    calc
      _ = ∑j,∑r,∑k,f j k r := sum_congr rfl (fun j _ => sum_comm)
      _ = _ := sum_comm
  rw [hreorder]
  apply sum_congr rfl
  intro r _
  by_cases h : w[r.val]=i
  · simp only [h,ite_true]
    exact hermitianBasis_contract_trace _ _
  · simp [h]
 theorem matrixScorePolynomial_sum (p : WordPolynomial n) (j k : Fin d) (x : MatrixIndex n d → ℝ) :
    matrixScorePolynomial p j k x = ∑w∈p.support,p w*matrixScoreWord w j k x := by
  simp only [matrixScorePolynomial,matrixPolynomial,Finsupp.sum,mul_sum,mul_smul_comm,
    Matrix.trace_sum,Matrix.trace_smul,smul_eq_mul,matrixScoreWord]
 theorem matrixScorePolynomial_polynomial (p : WordPolynomial n) (j k : Fin d) :
    IsComplexPolynomial (matrixScorePolynomial p j k) := by
  have he : matrixScorePolynomial p j k = fun x => ∑w∈p.support,p w*matrixScoreWord w j k x := funext (matrixScorePolynomial_sum p j k)
  rw [he]
  exact IsComplexPolynomial.finset_sum p.support (fun w _ => (matrixScoreWord_polynomial w j k).const_mul (p w))
 theorem matrixScorePolynomial_divergence (p : WordPolynomial n) (i : Fin n) (x : MatrixIndex n d → ℝ) :
    (∑j,∑k,complexCoordinateDerivative (matrixScorePolynomial p j k) (i,j,k) x) =
      ∑w∈p.support,p w*∑r : Fin w.length, if w[r.val]=i then
        Matrix.trace (matrixWord (coordinateMatrix x) (w.take r.val))*
          Matrix.trace (matrixWord (coordinateMatrix x) (w.drop (r.val+1))) else 0 := by
  have he j k : complexCoordinateDerivative (matrixScorePolynomial p j k) (i,j,k) x =
      ∑w∈p.support,p w*complexCoordinateDerivative (matrixScoreWord w j k) (i,j,k) x := by
    have hd := HasDerivAt.sum (u := p.support) (fun w _ => ((matrixScoreWord_polynomial w j k).hasDerivAt (i,j,k) x).const_mul (p w))
    simpa only [complexCoordinateDerivative,matrixScorePolynomial_sum,Finset.sum_fn] using hd.deriv
  simp_rw [he]
  calc
    _ = ∑w∈p.support,p w*(∑j,∑k,complexCoordinateDerivative (matrixScoreWord w j k) (i,j,k) x) := by
      simp_rw [mul_sum]
      calc
        _ = ∑j,∑w∈p.support,∑k,p w*complexCoordinateDerivative (matrixScoreWord w j k) (i,j,k) x :=
          sum_congr rfl (fun j _ => sum_comm)
        _ = _ := sum_comm
    _ = _ := by simp_rw [matrixScoreWord_divergence]
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

theorem heat_freeFisher_le {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 < u) :
    freeFisher (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) ≤
      ENNReal.ofReal ((n : ℝ) / u) := by
  let Z := heatTuple X (fun i => semicircularN (σ i)) u
  let η : Fin n → Space B N G := fun i =>
    ((Real.sqrt u)⁻¹ : ℂ) • basis (leftN (σ i) empty)
  have hc (i j : Fin n) : star (rightCreationN (σ i)) * Z j =
      Z j * star (rightCreationN (σ i)) +
        if j = i then (Real.sqrt u : ℂ) • vacuumRankOne (tracialVector B N G) else 0 := by
    change _ * (X j + (Real.sqrt u : ℂ) • semicircularN (σ j)) = _
    rw [mul_add, mul_smul_comm, (rightAnnihilationN_background (hs i) (hX j)).eq,
      rightAnnihilationN_semicircularN]
    change _ = (X j + (Real.sqrt u : ℂ) • semicircularN (σ j)) *
      star (rightCreationN (σ i)) +
      if j = i then (Real.sqrt u : ℂ) • vacuumRankOne (tracialVector B N G) else 0
    by_cases hij : j = i
    · subst j
      simp only [ite_true, add_mul, smul_mul_assoc, add_assoc]
      congr 1
      exact smul_add _ _ _
    · have hneq : σ i ≠ σ j := fun h => hij (hσ h).symm
      simp only [hij, hneq, ↓reduceIte, add_zero, add_mul, smul_mul_assoc]
  have hu' : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu)
  have hη (i : Fin n) (w : List (Fin n)) :
      inner ℂ (η i) (wordEval Z w (tracialVector B N G).vacuum) =
        derivativeMoment (tracialVector B N G) Z i w := by
    have h := commutator_integration_by_parts (tracialVector B N G) Z
      (star (rightCreationN (σ i))) i (Real.sqrt u) (hc i)
      (by simp [tracialVector, basis, empty]) w
    simp only [star_star, tracialVector, basis, rightCreationN_single] at h
    have he : rightN (σ i) (empty : Word B N G) = leftN (σ i) empty := by
      simp [rightN_eq_append, empty, leftN, push, append]
    rw [he] at h
    change inner ℂ (((Real.sqrt u : ℂ)⁻¹) • lp.single 2 (leftN (σ i) empty) 1)
      (wordEval Z w (lp.single 2 empty 1)) = _
    rw [inner_smul_left, h]
    simp [hu', tracialVector, basis]
  refine (freeFisher_le_testVectors (tracialVector B N G) Z η hη).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hnorm (i : Fin n) : ‖η i‖ ^ 2 = u⁻¹ := by
    simp [η, norm_smul, basis, norm_inv,
      lp.norm_single (E := fun _ : Word B N G => ℂ) (p := 2),
      abs_of_nonneg (Real.sqrt_nonneg u), inv_pow, Real.sq_sqrt (le_of_lt hu)]
  simp [hnorm, div_eq_mul_inv]

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FisherLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter
namespace FiniteEntropySeparation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem wordEval_append {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ} (X : Fin n → H →L[ℂ] H) (u v : List (Fin n)) :
    wordEval X (u ++ v) = wordEval X u * wordEval X v := by
  simp [wordEval]

 theorem star_wordEval {n : ℕ} (X : Fin n → H →L[ℂ] H)
    (hX : ∀ i, IsSelfAdjoint (X i)) (w : List (Fin n)) :
    star (wordEval X w) = wordEval X w.reverse := by
  induction w with
  | nil => simp [wordEval]
  | cons i w ih =>
    simp only [wordEval, List.map_cons, List.prod_cons, star_mul, (hX i).star_eq,
      List.reverse_cons, List.map_append, List.prod_append, ] at *
    rw [ih]
    simp

 theorem inner_wordVector {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (hX : ∀ i, IsSelfAdjoint (X i)) (u v : List (Fin n)) :
    inner ℂ (wordEval X u τ.vacuum) (wordEval X v τ.vacuum) =
      wordMoment τ X (u.reverse ++ v) := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    star_wordEval X hX u]
  simp only [wordMoment, trace, wordEval_append, mul_apply_eq_comp]

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
 theorem heat_conjugates_exist {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 < u) :
    ∃ ξ, ConjugateSystem (tracialVector B N G)
      (heatTuple X (fun i => semicircularN (σ i)) u) ξ :=
  exists_conjugate_of_fisher_le _ _ (n/u) (heat_freeFisher_le J X hX σ hσ hs u hu)

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixPolynomialNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem matrixWord_conjTranspose (A : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (w : List (Fin n)) :
    (matrixWord A w).conjTranspose = matrixWord A w.reverse := by
  induction w with
  | nil => simp [matrixWord]
  | cons i w ih =>
    simp only [matrixWord_cons,Matrix.conjTranspose_mul,ih,(hA i).eq,List.reverse_cons,
      matrixWord_append,matrixWord_cons,matrixWord_nil,mul_one]
 theorem matrixScorePolynomial_norm_lower (p : WordPolynomial n) (x : MatrixIndex n d → ℝ) :
    (∑j,∑k,(matrixScorePolynomial p j k x).re^2) ≤
      (Matrix.trace ((matrixPolynomial p (coordinateMatrix x)).conjTranspose*matrixPolynomial p (coordinateMatrix x))).re := by
  rw [trace_conjTranspose_mul_re,← hermitianBasis_parseval]
  apply sum_le_sum
  intro j _
  apply sum_le_sum
  intro k _
  change (matrixScorePolynomial p j k x).re^2 ≤ Complex.normSq (matrixScorePolynomial p j k x)
  simp only [Complex.normSq_apply]
  nlinarith [sq_nonneg (matrixScorePolynomial p j k x).im]
 theorem matrixPolynomialNorm_trace (p : WordPolynomial n) (a : MatrixCoordinates n d) :
    matrixPolynomialNorm p a = (d:ℝ)⁻¹*(Matrix.trace
      ((matrixPolynomial p (hermitianMatrix a)).conjTranspose*matrixPolynomial p (hermitianMatrix a))).re := by
  have he : Matrix.trace ((matrixPolynomial p (hermitianMatrix a)).conjTranspose*matrixPolynomial p (hermitianMatrix a)) =
      ∑u∈p.support,∑v∈p.support,star (p u)*p v*Matrix.trace (matrixWord (hermitianMatrix a) (u.reverse++v)) := by
    simp only [matrixPolynomial,Finsupp.sum,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,
      matrixWord_conjTranspose _ (hermitianMatrix_isHermitian a),sum_mul,mul_sum,
      smul_mul_assoc,mul_smul_comm,Matrix.trace_sum,Matrix.trace_smul,
      smul_eq_mul,matrixWord_append]
    rw [sum_comm]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    ring
  rw [he]
  unfold matrixPolynomialNorm matrixMoment
  have he' : (∑u∈p.support,∑v∈p.support,star (p u)*p v*((d:ℂ)⁻¹*Matrix.trace ((u.reverse++v).map (hermitianMatrix a)).prod)) =
      (d:ℂ)⁻¹*(∑u∈p.support,∑v∈p.support,star (p u)*p v*Matrix.trace (matrixWord (hermitianMatrix a) (u.reverse++v))) := by
    simp only [mul_sum,matrixWord]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    ring
  rw [he']
  simp only [← Complex.ofReal_natCast,← Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
 theorem polynomialVector_norm_formula {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) (X : Fin n → H →L[ℂ] H)
    (hX : ∀i,IsSelfAdjoint (X i)) (p : WordPolynomial n) :
    ‖polynomialVector τ X p‖^2 =
      (∑u∈p.support,∑v∈p.support,star (p u)*p v*wordMoment τ X (u.reverse++v)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [polynomialVector,Finsupp.linearCombination_apply,Finsupp.sum,sum_inner,inner_sum,
    inner_smul_left,inner_smul_right,inner_wordVector τ X hX,mul_assoc,mul_sum]
  change (∑u∈p.support,∑v∈p.support,p u*(star (p v)*wordMoment τ X (v.reverse++u))).re = _
  rw [sum_comm]
  congr 1
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  ring
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
 variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
 theorem diagonalMicrostates_moments {D : ℕ → ℕ} {R : ℝ}
    (a : (k:ℕ) → MatrixCoordinates n (D k))
    (ha : ∀k,a k ∈ diagonalMicrostates τ X R k (D k)) (w : List (Fin n)) :
    Tendsto (fun k => matrixMoment (a k) w) atTop (𝓝 (wordMoment τ X w)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _))
  · filter_upwards [eventually_ge_atTop w.length] with k hk
    exact ((ha k).2 w hk).le
  · simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
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

 theorem heatTuple_selfAdjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {n : ℕ} (X S : Fin n → H →L[ℂ] H)
    (hX : ∀ i, IsSelfAdjoint (X i)) (hS : ∀ i, IsSelfAdjoint (S i)) (u : ℝ) (i : Fin n) :
    IsSelfAdjoint (heatTuple X S u i) := by
  change star (X i + (Real.sqrt u : ℂ) • S i) = _
  simp only [star_add, star_smul, Complex.star_def, Complex.conj_ofReal, (hX i).star_eq,
    (hS i).star_eq, heatTuple]

end FreeTensor

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
end FreeTensor
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
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.UniformConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace FiniteEntropySeparation
 theorem uniform_of_all_selections {α : ℕ → Type u1} (S : (k:ℕ) → Set (α k)) (hS : ∀k,(S k).Nonempty)
    (F : (k:ℕ) → α k → ℝ) (hF : ∀a:(k:ℕ) → α k,(∀k,a k ∈ S k) → Tendsto (fun k => F k (a k)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0<ε) : ∀ᶠ k in atTop,∀a ∈ S k,|F k a|<ε := by
  classical
  choose a ha using hS
  let b (k : ℕ) : α k := if h : ∃x ∈ S k,ε≤|F k x| then h.choose else a k
  have hb (k : ℕ) : b k ∈ S k := by
    dsimp only [b]
    split_ifs with h
    · exact h.choose_spec.1
    · exact ha k
  have ht := (hF b hb).abs.eventually (gt_mem_nhds (by simpa using hε))
  filter_upwards [ht] with k hk x hx
  by_contra he
  have h : ∃x ∈ S k,ε≤|F k x| := ⟨x,hx,le_of_not_gt he⟩
  have hh : ε≤|F k (b k)| := by simpa only [b,dite_eq_left h] using h.choose_spec.2
  exact (not_lt_of_ge hh) hk
 theorem integral_tendsto_zero_of_uniform {α : ℕ → Type u2} [∀k,MeasurableSpace (α k)]
    (μ : (k:ℕ) → Measure (α k)) [∀k,IsProbabilityMeasure (μ k)]
    (S : (k:ℕ) → Set (α k)) (hS : ∀k,∀ᵐ a ∂μ k,a ∈ S k)
    (F : (k:ℕ) → α k → ℝ) (hm : ∀k,AEStronglyMeasurable (F k) (μ k))
    (hu : ∀ε:ℝ,0<ε → ∀ᶠ k in atTop,∀a ∈ S k,|F k a|<ε) :
    Tendsto (fun k => ∫ a,F k a ∂μ k) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hu (ε/2) (by positivity)] with k hk
  have hb : ∀ᵐ a ∂μ k,‖F k a‖≤ε/2 := by
    filter_upwards [hS k] with a ha
    exact (hk a ha).le
  have hi : Integrable (F k) (μ k) := (integrable_const (ε/2)).mono' (hm k) hb
  have hn : ‖∫ a,F k a ∂μ k‖≤ε/2 := by
    apply (norm_integral_le_integral_norm _).trans
    exact (integral_mono_ae hi.norm (integrable_const _) hb).trans_eq (by simp)
  simpa only [dist_zero_right] using hn.trans_lt (by linarith : ε/2<ε)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.RandomMatrixConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace FiniteEntropySeparation
 theorem heatCoordinates_continuous {n d : ℕ} (u : ℝ) :
    Continuous (fun z : MatrixCoordinates n d × (MatrixIndex n d → ℝ) => heatCoordinates z.1 u z.2) := by
  exact continuous_fst.add ((PiLp.continuous_toLp 2 (fun _ : MatrixIndex n d => ℝ)).comp continuous_snd |>.const_smul (Real.sqrt u/Real.sqrt d))
 theorem conditionalHeatError_measurable {n d : ℕ} (u : ℝ) (w : List (Fin n)) (z : ℂ) :
    Measurable (fun a : MatrixCoordinates n d => ∫ x,‖matrixMoment (heatCoordinates a u x) w-z‖^2 ∂productGaussian (MatrixIndex n d)) := by
  have h : Continuous (fun z' : MatrixCoordinates n d × (MatrixIndex n d → ℝ) => ‖matrixMoment (heatCoordinates z'.1 u z'.2) w-z‖^2) :=
    (((matrixMoment_continuous w).comp (heatCoordinates_continuous u)).sub continuous_const).norm.pow 2
  exact h.stronglyMeasurable.integral_prod_right'.measurable
 namespace FreeTensor
 variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G] {n : ℕ}
 theorem heatError_uniform {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
    (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀i,X i ∈ backgroundAlgebra J)
    {R : ℝ} (hR : 0≤R) (hn : ∀k,(diagonalMicrostates (tracialVector B N G) X R k (D k)).Nonempty)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀i,σ i ∉ J)
    (u : ℝ) (w : List (Fin n)) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k in atTop,∀a ∈ diagonalMicrostates (tracialVector B N G) X R k (D k),
      |∫ x,‖matrixMoment (heatCoordinates a u x) w-
        wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) w‖^2 ∂productGaussian (MatrixIndex n (D k))|<ε := by
  apply uniform_of_all_selections _ hn _ _ hε
  intro a ha
  simp only [matrixMoment_heatCoordinates]
  apply heatMatrix_meanSquare_tendsto hD0 hD (fun k => hermitianMatrix (a k)) hR (fun k i => (ha k).1 i) J X hX σ hσ hs
  intro v
  exact diagonalMicrostates_moments (tracialVector B N G) X a ha v
 theorem heatError_integral_tendsto {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
    (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀i,X i ∈ backgroundAlgebra J)
    {R : ℝ} (hR : 0≤R) (hn : ∀k,(diagonalMicrostates (tracialVector B N G) X R k (D k)).Nonempty)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀i,σ i ∉ J)
    (μ : (k:ℕ) → Measure (MatrixCoordinates n (D k))) [∀k,IsProbabilityMeasure (μ k)]
    (hμ : ∀k,∀ᵐ a ∂μ k,a ∈ diagonalMicrostates (tracialVector B N G) X R k (D k))
    (u : ℝ) (w : List (Fin n)) :
    Tendsto (fun k => ∫ a,∫ x,‖matrixMoment (heatCoordinates a u x) w-
      wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) w‖^2 ∂productGaussian (MatrixIndex n (D k)) ∂μ k) atTop (𝓝 0) := by
  apply integral_tendsto_zero_of_uniform μ _ hμ _ (fun k => (conditionalHeatError_measurable u w _).aestronglyMeasurable)
  intro ε hε
  exact heatError_uniform hD0 hD J X hX hR hn σ hσ hs u w hε
 end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.RandomHeatMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Topology ENNReal
namespace FiniteEntropySeparation
 theorem heatMatrix_noiseBound {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) {R : ℝ}
    (hR : 0≤R) (hA : ∀i,matrixOpNorm (A i)≤R) (u : ℝ) (x : MatrixIndex n d → ℝ) (i : Fin n) :
    matrixOpNorm (heatMatrix A u x i) ≤ (1+Real.sqrt u)*jointNoiseBound R x := by
  have h1 := jointMatrix_norm_bound A hR hA x (Sum.inl i)
  have h2 := jointMatrix_norm_bound A hR hA x (Sum.inr i)
  have h := matrixOpNorm_add (A i) ((Real.sqrt u:ℂ) • gueMatrix x i)
  rw [matrixOpNorm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at h
  change matrixOpNorm (heatMatrix A u x i) ≤ _ at h
  calc
    _ ≤ matrixOpNorm (A i)+Real.sqrt u*matrixOpNorm (gueMatrix x i) := h
    _ ≤ jointNoiseBound R x+Real.sqrt u*jointNoiseBound R x := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
    _ = _ := by ring
 theorem heatMoment_bound {n d : ℕ} (hd : 0<d) (a : MatrixCoordinates n d) {R : ℝ}
    (hR : 0≤R) (ha : ∀i,matrixOpNorm (hermitianMatrix a i)≤R) (u : ℝ) (x : MatrixIndex n d → ℝ) (w : List (Fin n)) :
    ‖matrixMoment (heatCoordinates a u x) w‖ ≤ (1+Real.sqrt u)^w.length*jointNoiseBound R x^w.length := by
  rw [matrixMoment_heatCoordinates]
  apply (matrix_normalized_trace_bound hd _).trans
  rw [← mul_pow]
  exact matrixOpNorm_word _ _ (mul_nonneg (by positivity) (jointNoiseBound_nonneg hR x)) (fun i _ => heatMatrix_noiseBound _ hR ha u x i)
 theorem heatMoment_power_integrable {n d : ℕ} (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {R : ℝ} (hR : 0≤R) (hμ : ∀ᵐ a ∂μ,∀i,matrixOpNorm (hermitianMatrix a i)≤R)
    (u : ℝ) (w : List (Fin n)) (m : ℕ) :
    Integrable (fun z : MatrixCoordinates n d × (MatrixIndex n d → ℝ) => ‖matrixMoment (heatCoordinates z.1 u z.2) w‖^m)
      (μ.prod (productGaussian (MatrixIndex n d))) := by
  have hb := ((jointNoiseBound_moment (n := n) hd hR (w.length*m)).1.const_mul ((1+Real.sqrt u)^(w.length*m))).comp_snd μ
  apply hb.mono'
  · exact (((matrixMoment_continuous w).comp (heatCoordinates_continuous u)).norm.pow m).aestronglyMeasurable
  have hm : ∀ᵐ z ∂μ.prod (productGaussian (MatrixIndex n d)),∀i,matrixOpNorm (hermitianMatrix z.1 i)≤R := by
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr
    · filter_upwards [hμ] with a ha
      exact ae_of_all _ (fun _ => ha)
    · simpa only [Set.ofPred_forall,Function.comp_apply] using MeasurableSet.iInter (fun i : Fin n => measurableSet_le ((matrixOpNorm_continuous.comp (hermitianMatrix_continuous (n := n) (d := d) i)).comp (continuous_fst : Continuous (Prod.fst : MatrixCoordinates n d × (MatrixIndex n d → ℝ) → MatrixCoordinates n d))).measurable (measurable_const (a := R)))
  filter_upwards [hm] with z hz
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  simpa only [mul_pow,← pow_mul] using pow_le_pow_left₀ (norm_nonneg _) (heatMoment_bound hd z.1 hR hz u z.2 w) m
 theorem heatMoment_integrable {n d : ℕ} (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {R : ℝ} (hR : 0≤R) (hμ : ∀ᵐ a ∂μ,∀i,matrixOpNorm (hermitianMatrix a i)≤R)
    (u : ℝ) (w : List (Fin n)) :
    Integrable (fun z : MatrixCoordinates n d × (MatrixIndex n d → ℝ) => matrixMoment (heatCoordinates z.1 u z.2) w)
      (μ.prod (productGaussian (MatrixIndex n d))) := by
  apply integrable_norm_iff (((matrixMoment_continuous w).comp (heatCoordinates_continuous u)).aestronglyMeasurable) |>.mp
  simpa using heatMoment_power_integrable hd μ hR hμ u w 1
 theorem heatMoment_error_integrable {n d : ℕ} (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {R : ℝ} (hR : 0≤R) (hμ : ∀ᵐ a ∂μ,∀i,matrixOpNorm (hermitianMatrix a i)≤R)
    (u : ℝ) (w : List (Fin n)) (c : ℂ) :
    Integrable (fun z : MatrixCoordinates n d × (MatrixIndex n d → ℝ) => ‖matrixMoment (heatCoordinates z.1 u z.2) w-c‖^2)
      (μ.prod (productGaussian (MatrixIndex n d))) := by
  have hi := ((heatMoment_power_integrable hd μ hR hμ u w 2).add (integrable_const (‖c‖^2))).const_mul 2
  apply hi.mono' (((((matrixMoment_continuous w).comp (heatCoordinates_continuous u)).sub continuous_const).norm.pow 2).aestronglyMeasurable)
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    dsimp only [Pi.add_apply,Pi.pow_apply,Pi.sub_apply,Function.comp_apply]
    have h := norm_sub_le (matrixMoment (heatCoordinates z.1 u z.2) w) c
    have hn := norm_nonneg (matrixMoment (heatCoordinates z.1 u z.2) w-c)
    nlinarith [sq_nonneg (‖matrixMoment (heatCoordinates z.1 u z.2) w‖-‖c‖)])
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.L2Convergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace FiniteEntropySeparation
 theorem integral_sq_le_integral_square {Ω : Type u1} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun x => (f x)^2) μ) :
    (∫ x,f x ∂μ)^2 ≤ ∫x,(f x)^2 ∂μ := by
  let m := ∫x,f x ∂μ
  have h : 0≤∫x,(f x-m)^2 ∂μ := integral_nonneg (fun x => sq_nonneg (f x-m))
  have he : (fun x => (f x-m)^2) = fun x => (f x)^2-2*m*f x+m^2 := by funext x; ring
  rw [he] at h
  have ha := integral_add (hf2.sub (hf.const_mul (2*m))) (integrable_const (m^2))
  simp only [Pi.sub_apply] at ha
  rw [ha,integral_sub hf2 (hf.const_mul (2*m)),integral_const_mul] at h
  simp only [integral_const,probReal_univ,one_smul] at h
  dsimp only [m] at h
  nlinarith
 theorem complex_integral_error_sq_le {Ω : Type u2} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℂ} (c : ℂ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => ‖f x-c‖^2) μ) :
    ‖(∫x,f x ∂μ)-c‖^2 ≤ ∫x,‖f x-c‖^2 ∂μ := by
  have hi := hf.sub (integrable_const c)
  have h : ‖(∫x,f x ∂μ)-c‖ ≤ ∫x,‖f x-c‖ ∂μ := by
    have hh := norm_integral_le_integral_norm (fun x => f x-c) (μ := μ)
    simpa only [integral_sub hf (integrable_const c),integral_const,probReal_univ,one_smul] using hh
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans (integral_sq_le_integral_square μ hi.norm hf2)
 theorem complex_integral_error_le {Ω : Type u3} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℂ} (c : ℂ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => ‖f x-c‖^2) μ) :
    ‖(∫x,f x ∂μ)-c‖ ≤ Real.sqrt (∫x,‖f x-c‖^2 ∂μ) := by
  exact (Real.le_sqrt (norm_nonneg _) (integral_nonneg (fun x => sq_nonneg _))).mpr
    (complex_integral_error_sq_le μ c hf hf2)
 theorem complex_integral_tendsto_of_L2 {Ω : ℕ → Type u4} [∀k,MeasurableSpace (Ω k)]
    (μ : (k:ℕ) → Measure (Ω k)) [∀k,IsProbabilityMeasure (μ k)] (f : (k:ℕ) → Ω k → ℂ) (c : ℂ)
    (hi : ∀k,Integrable (f k) (μ k)) (hi2 : ∀k,Integrable (fun x => ‖f k x-c‖^2) (μ k))
    (ht : Tendsto (fun k => ∫x,‖f k x-c‖^2 ∂μ k) atTop (𝓝 0)) :
    Tendsto (fun k => ∫x,f k x ∂μ k) atTop (𝓝 c) := by
  rw [← tendsto_sub_nhds_zero_iff]
  exact squeeze_zero_norm (fun k => complex_integral_error_le (μ k) c (hi k) (hi2 k)) (by simpa only [Function.comp_def,Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp ht)
 theorem complex_mul_integrable_of_squares {Ω : Type u5} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℂ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => ‖f x‖^2) μ) (hg2 : Integrable (fun x => ‖g x‖^2) μ) :
    Integrable (fun x => f x*g x) μ := by
  apply ((hf2.add hg2).div_const 2).mono' (hf.mul hg)
  exact ae_of_all _ (fun x => by dsimp; rw [norm_mul]; nlinarith [sq_nonneg (‖f x‖-‖g x‖)])
 theorem complex_integral_mul_centered_bound {Ω : Type u6} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℂ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => ‖f x‖^2) μ) (hg2 : Integrable (fun x => ‖g x‖^2) μ) :
    ‖∫x,f x*g x ∂μ‖ ≤ ((∫x,‖f x‖^2 ∂μ)+(∫x,‖g x‖^2 ∂μ))/2 := by
  calc
    _ ≤ ∫x,‖f x*g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫x,(‖f x‖^2+‖g x‖^2)/2 ∂μ := by
      apply integral_mono (complex_mul_integrable_of_squares μ hf hg hf2 hg2).norm ((hf2.add hg2).div_const 2)
      intro x; dsimp; rw [norm_mul]; nlinarith [sq_nonneg (‖f x‖-‖g x‖)]
    _ = _ := by rw [integral_div,integral_add hf2 hg2]
 theorem complex_integral_mul_tendsto_of_L2 {Ω : ℕ → Type u7} [∀k,MeasurableSpace (Ω k)]
    (μ : (k:ℕ) → Measure (Ω k)) [∀k,IsProbabilityMeasure (μ k)]
    (f g : (k:ℕ) → Ω k → ℂ) (c d : ℂ)
    (hif : ∀k,Integrable (f k) (μ k)) (hig : ∀k,Integrable (g k) (μ k))
    (hif2 : ∀k,Integrable (fun x => ‖f k x-c‖^2) (μ k))
    (hig2 : ∀k,Integrable (fun x => ‖g k x-d‖^2) (μ k))
    (htf : Tendsto (fun k => ∫x,‖f k x-c‖^2 ∂μ k) atTop (𝓝 0))
    (htg : Tendsto (fun k => ∫x,‖g k x-d‖^2 ∂μ k) atTop (𝓝 0)) :
    Tendsto (fun k => ∫x,f k x*g k x ∂μ k) atTop (𝓝 (c*d)) := by
  have hcf (k : ℕ) : Integrable (fun x => f k x-c) (μ k) := (hif k).sub (integrable_const c)
  have hcg (k : ℕ) : Integrable (fun x => g k x-d) (μ k) := (hig k).sub (integrable_const d)
  have hr : Tendsto (fun k => ∫x,(f k x-c)*(g k x-d) ∂μ k) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => complex_integral_mul_centered_bound (μ k) (hcf k).aestronglyMeasurable (hcg k).aestronglyMeasurable (hif2 k) (hig2 k))
    simpa using (htf.add htg).div_const 2
  have hf := complex_integral_tendsto_of_L2 μ f c hif hif2 htf
  have hg := complex_integral_tendsto_of_L2 μ g d hig hig2 htg
  have he k : (∫x,f k x*g k x ∂μ k) = (∫x,(f k x-c)*(g k x-d) ∂μ k)+
      ((∫x,f k x ∂μ k)-c)*d+c*((∫x,g k x ∂μ k)-d)+c*d := by
    have hmul := complex_mul_integrable_of_squares (μ k) (hcf k).aestronglyMeasurable (hcg k).aestronglyMeasurable (hif2 k) (hig2 k)
    have hpoint : (fun x => f k x*g k x) = fun x => (f k x-c)*(g k x-d)+(f k x-c)*d+c*(g k x-d)+c*d := by funext x; ring
    have ha := integral_add ((hmul.add ((hcf k).mul_const d)).add ((hcg k).const_mul c)) (integrable_const (c*d))
    have hb := integral_add (hmul.add ((hcf k).mul_const d)) ((hcg k).const_mul c)
    simp only [Pi.add_apply] at ha hb
    rw [hpoint,ha,hb,
      integral_add hmul ((hcf k).mul_const d),integral_mul_const,integral_const_mul,
      integral_sub (hif k) (integrable_const c),integral_sub (hig k) (integrable_const d)]
    simp only [integral_const,probReal_univ,one_smul]
  simp_rw [he]
  convert ((hr.add ((hf.sub_const c).mul_const d)).add ((hg.sub_const d).const_mul c)).add_const (c*d) using 1 ; simp
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.RandomHeatConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace FiniteEntropySeparation.FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G] {n : ℕ}
variable {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
  (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀i,X i ∈ backgroundAlgebra J)
  {R : ℝ} (hR : 0≤R) (hn : ∀k,(diagonalMicrostates (tracialVector B N G) X R k (D k)).Nonempty)
  (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀i,σ i ∉ J)
  (μ : (k:ℕ) → Measure (MatrixCoordinates n (D k))) [∀k,IsProbabilityMeasure (μ k)]
  (hμ : ∀k,∀ᵐ a ∂μ k,a ∈ diagonalMicrostates (tracialVector B N G) X R k (D k))
include hD0 hD hX hR hn hσ hs hμ
 theorem heatError_product_tendsto (u : ℝ) (w : List (Fin n)) :
    Tendsto (fun k => ∫z : MatrixCoordinates n (D k) × (MatrixIndex n (D k) → ℝ),
      ‖matrixMoment (heatCoordinates z.1 u z.2) w-wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) w‖^2
      ∂(μ k).prod (productGaussian (MatrixIndex n (D k)))) atTop (𝓝 0) := by
  have he k := heatMoment_error_integrable (hD0 k) (μ k) hR ((hμ k).mono (fun a ha => ha.1)) u w
    (wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) w)
  have heq (k : ℕ) := integral_prod _ (he k)
  simp_rw [heq]
  exact heatError_integral_tendsto hD0 hD J X hX hR hn σ hσ hs μ hμ u w
 theorem heatMoment_product_tendsto (u : ℝ) (w : List (Fin n)) :
    Tendsto (fun k => ∫z : MatrixCoordinates n (D k) × (MatrixIndex n (D k) → ℝ),
      matrixMoment (heatCoordinates z.1 u z.2) w
      ∂(μ k).prod (productGaussian (MatrixIndex n (D k)))) atTop
      (𝓝 (wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) w)) := by
  exact complex_integral_tendsto_of_L2 _ _ _
    (fun k => heatMoment_integrable (hD0 k) (μ k) hR ((hμ k).mono (fun a ha => ha.1)) u w)
    (fun k => heatMoment_error_integrable (hD0 k) (μ k) hR ((hμ k).mono (fun a ha => ha.1)) u w _)
    (heatError_product_tendsto hD0 hD J X hX hR hn σ hσ hs μ hμ u w)
 theorem heatMoment_products_tendsto (u : ℝ) (v w : List (Fin n)) :
    Tendsto (fun k => ∫z : MatrixCoordinates n (D k) × (MatrixIndex n (D k) → ℝ),
      matrixMoment (heatCoordinates z.1 u z.2) v*matrixMoment (heatCoordinates z.1 u z.2) w
      ∂(μ k).prod (productGaussian (MatrixIndex n (D k)))) atTop
      (𝓝 (wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) v*
        wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) w)) := by
  exact complex_integral_mul_tendsto_of_L2 _ _ _ _ _
    (fun k => heatMoment_integrable (hD0 k) (μ k) hR ((hμ k).mono (fun a ha => ha.1)) u v)
    (fun k => heatMoment_integrable (hD0 k) (μ k) hR ((hμ k).mono (fun a ha => ha.1)) u w)
    (fun k => heatMoment_error_integrable (hD0 k) (μ k) hR ((hμ k).mono (fun a ha => ha.1)) u v _)
    (fun k => heatMoment_error_integrable (hD0 k) (μ k) hR ((hμ k).mono (fun a ha => ha.1)) u w _)
    (heatError_product_tendsto hD0 hD J X hX hR hn σ hσ hs μ hμ u v)
    (heatError_product_tendsto hD0 hD J X hX hR hn σ hσ hs μ hμ u w)
end FiniteEntropySeparation.FreeTensor

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixHeatLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem matrixHeatLaw_eq (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) :
    matrixHeatLaw μ s = (μ.prod (productGaussian (MatrixIndex n d))).map (fun z => heatCoordinates z.1 s z.2) := by
  have hsd : 0<s/(d:ℝ) := div_pos hs (by exact_mod_cast hd)
  rw [matrixHeatLaw,← smoothedLaw_eq μ hsd,normalLaw_eq_scaled hsd]
  have he : μ.prod ((productGaussian (MatrixIndex n d)).map (fun x => Real.sqrt (s/d) • WithLp.toLp 2 x)) =
      (μ.prod (productGaussian (MatrixIndex n d))).map (Prod.map id (fun x => Real.sqrt (s/d) • WithLp.toLp 2 x)) := by
    convert Measure.map_prod_map μ (productGaussian (MatrixIndex n d)) measurable_id
      (show Measurable (fun x : MatrixIndex n d → ℝ => Real.sqrt (s/d) • WithLp.toLp 2 x) from
        (show Continuous (WithLp.toLp 2 : (MatrixIndex n d → ℝ) → MatrixCoordinates n d) from PiLp.continuous_toLp 2 _).measurable.const_smul (Real.sqrt (s/d))) using 1
    rw [Measure.map_id]
  rw [he,Measure.map_map (show Measurable (fun z : MatrixCoordinates n d × MatrixCoordinates n d => z.1+z.2) from by fun_prop)
    (show Measurable (Prod.map id (fun x : MatrixIndex n d → ℝ => Real.sqrt (s/d) • WithLp.toLp 2 x)) from
      measurable_id.prodMap ((show Continuous (WithLp.toLp 2 : (MatrixIndex n d → ℝ) → MatrixCoordinates n d) from PiLp.continuous_toLp 2 _).measurable.const_smul (Real.sqrt (s/d))))]
  congr 1
  funext z
  simp only [Function.comp_apply,Prod.map_fst,Prod.map_snd,id_eq,heatCoordinates,Real.sqrt_div hs.le]
 theorem integral_matrixHeatLaw (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) (hd : 0<d) (f : MatrixCoordinates n d → ℝ) :
    (∫x,f x ∂matrixHeatLaw μ s) = ∫x,smoothedDensity μ (s/d) x*f x := by
  have hp : ∀x,0 ≤ smoothedDensity μ (s/d) x := fun x => integral_nonneg (fun y => (normalKernel_pos _ _).le)
  rw [matrixHeatLaw,integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (hp _),smul_eq_mul]
  · exact ENNReal.measurable_ofReal.comp (smoothedDensity_continuous μ (div_pos hs (by exact_mod_cast hd))).measurable
  · exact ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory
namespace FiniteEntropySeparation
variable {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
 theorem gaussianDecay_integrable {c : ℝ} (hc : 0<c) : Integrable (fun x : E => Real.exp (-c*‖x‖^2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b := (c:ℂ)) (by simpa using hc) 0 (0:E)).re
  convert h using 1
  funext x
  simp only [zero_mul,add_zero]
  change Real.exp (-c*‖x‖^2) = (Complex.exp (-(c:ℂ)*(‖x‖:ℂ)^2)).re
  rw [← Complex.ofReal_pow,← Complex.ofReal_neg,← Complex.ofReal_mul,← Complex.ofReal_exp]
  rfl
 theorem polynomial_gaussian_bound {c : ℝ} (hc : 0<c) (m : ℕ) (r : ℝ) (hr : 0≤r) :
    (1+r)^m*Real.exp (-c*r) ≤
      ((m.factorial:ℝ)*(2/c)^m*Real.exp (c/2))*Real.exp (-(c/2)*r) := by
  have hy : 0≤(c/2)*(1+r) := by positivity
  have he := Real.pow_div_factorial_le_exp _ hy m
  have hf : 0<(m.factorial:ℝ) := by positivity
  have hh : (1+r)^m ≤ (m.factorial:ℝ)*(2/c)^m*Real.exp ((c/2)*(1+r)) := by
    have hpow : 0<(c/2)^m := by positivity
    have he' : (c/2)^m*(1+r)^m ≤ Real.exp ((c/2)*(1+r))*(m.factorial:ℝ) := by
      simpa only [mul_pow] using (div_le_iff₀ hf).mp he
    calc
      _ ≤ Real.exp ((c/2)*(1+r))*(m.factorial:ℝ)/(c/2)^m := (le_div_iff₀ hpow).mpr (by simpa [mul_comm] using he')
      _ = _ := by rw [div_eq_mul_inv,← inv_pow,inv_div]; ring
  apply (mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le).trans_eq
  calc
    _ = ((m.factorial:ℝ)*(2/c)^m)*(Real.exp ((c/2)*(1+r))*Real.exp (-c*r)) := by ring
    _ = ((m.factorial:ℝ)*(2/c)^m)*Real.exp (c/2 + -(c/2)*r) := by rw [← Real.exp_add]; congr 2; ring
    _ = _ := by rw [Real.exp_add]; ring
 theorem polynomial_gaussian_integrable {c : ℝ} (hc : 0<c) (m : ℕ) :
    Integrable (fun x : E => (1+‖x‖^2)^m*Real.exp (-c*‖x‖^2)) := by
  apply ((gaussianDecay_integrable (E := E) (show 0<c/2 by positivity)).const_mul
    ((m.factorial:ℝ)*(2/c)^m*Real.exp (c/2))).mono'
  · exact (by fun_prop : Continuous (fun x : E => (1+‖x‖^2)^m*Real.exp (-c*‖x‖^2))).aestronglyMeasurable
  · exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact polynomial_gaussian_bound hc m (‖x‖^2) (sq_nonneg _))
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianConvolutionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem normalKernel_shift_bounds {a b s D K : ℝ} (ha : 0<a) (hs : s∈Icc a b)
    (hD : |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D) (_hK : 0 ≤ K)
    (x y : EuclideanSpace ℝ ι) (hy : ‖y‖ ≤ K) :
    Real.exp (-D-(‖x‖^2+K^2)/a)  ≤  normalKernel s (x-y) ∧
    normalKernel s (x-y)  ≤  Real.exp (D+K^2/(2*b))*Real.exp (-‖x‖^2/(4*b)) := by
  have hs0 : 0<s := ha.trans_le hs.1
  have hb : 0<b := hs0.trans_le hs.2
  have hnorm : ‖x-y‖ ≤ ‖x‖+K := (norm_sub_le x y).trans (add_le_add le_rfl hy)
  have hnorm' : ‖x‖ ≤ ‖x-y‖+K := by
    calc _ = ‖(x-y)+y‖ := by rw [sub_add_cancel]
         _  ≤  ‖x-y‖+‖y‖ := norm_add_le _ _
         _  ≤  _ := add_le_add_right hy _
  have hu : ‖x-y‖^2 ≤ 2*(‖x‖^2+K^2) := by
    nlinarith [sq_nonneg (‖x‖-K),pow_le_pow_left₀ (norm_nonneg _) hnorm 2]
  have hl : ‖x‖^2 ≤ 2*(‖x-y‖^2+K^2) := by
    nlinarith [sq_nonneg (‖x-y‖-K),pow_le_pow_left₀ (norm_nonneg _) hnorm' 2]
  have hdivu : ‖x-y‖^2/(2*s) ≤ (‖x‖^2+K^2)/a := by
    calc _  ≤  ‖x-y‖^2/(2*a) := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith [hs.1])
         _  ≤  _ := by apply (div_le_iff₀ (show 0<2*a by positivity)).mpr; field_simp; nlinarith
  have hdivl : ‖x‖^2/(4*b)-K^2/(2*b) ≤ ‖x-y‖^2/(2*s) := by
    calc _  ≤  ‖x-y‖^2/(2*b) := by apply (le_div_iff₀ (show 0<2*b by positivity)).mpr; field_simp; nlinarith
         _  ≤  _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith [hs.2])
  constructor
  · apply Real.exp_le_exp.mpr
    have := (abs_le.mp hD).1
    linarith
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp hD).2
    simp only [neg_div] at *
    linarith
 theorem smoothedDensity_bounds (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {a b s D K : ℝ} (ha : 0<a) (hs : s∈Icc a b)
    (hD : |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D) (hK : 0 ≤ K)
    (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (x : EuclideanSpace ℝ ι) :
    Real.exp (-D-(‖x‖^2+K^2)/a)  ≤  smoothedDensity μ s x ∧
    smoothedDensity μ s x  ≤  Real.exp (D+K^2/(2*b))*Real.exp (-‖x‖^2/(4*b)) := by
  have hi := normalKernel_integrable_finite μ (ha.trans_le hs.1) x
  constructor
  · have h := integral_mono_ae (integrable_const (Real.exp (-D-(‖x‖^2+K^2)/a))) hi
      (hμ.mono (fun y hy => (normalKernel_shift_bounds ha hs hD hK x y hy).1))
    simpa only [smoothedDensity,integral_const,probReal_univ,one_smul] using h
  · have h := integral_mono_ae hi (integrable_const (Real.exp (D+K^2/(2*b))*Real.exp (-‖x‖^2/(4*b))))
      (hμ.mono (fun y hy => (normalKernel_shift_bounds ha hs hD hK x y hy).2))
    simpa only [smoothedDensity,integral_const,probReal_univ,one_smul] using h
 theorem integrable_of_normBound (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {K : ℝ} (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) {f : EuclideanSpace ℝ ι → ℝ} (hf : Continuous f) : Integrable f μ := by
  apply integrable_of_compact_ae μ (isCompact_closedBall (0 : EuclideanSpace ℝ ι) K) _ hf.aestronglyMeasurable hf.continuousOn
  simpa only [Metric.mem_closedBall,dist_zero_right] using hμ
 theorem smoothedGradient_bound (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {a s K : ℝ} (ha : 0<a) (hs : a ≤ s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    |smoothedGradient μ s x i| ≤ ((‖x‖+K)/a)*smoothedDensity μ s x := by
  have hs0 := ha.trans_le hs
  have hi : Integrable (fun y => normalGradient s (x-y) i) μ := integrable_of_normBound μ hμ ((normalGradient_continuous s i).comp (continuous_const.sub continuous_id))
  calc
    _  ≤  ∫y,|normalGradient s (x-y) i| ∂μ := by simpa only [smoothedGradient,Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => normalGradient s (x-y) i)
    _  ≤  ∫y,((‖x‖+K)/a)*normalKernel s (x-y) ∂μ := by
      apply integral_mono_ae hi.norm ((normalKernel_integrable_finite μ hs0 x).const_mul _)
      filter_upwards [hμ] with y hy
      unfold normalGradient
      rw [Real.norm_eq_abs,abs_mul,abs_div,abs_neg,abs_of_pos hs0,abs_of_pos (normalKernel_pos _ _)]
      apply mul_le_mul_of_nonneg_right _ (normalKernel_pos _ _).le
      have hn0 : |(x-y) i| ≤ ‖x-y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) i
      have hn : |(x-y) i| ≤ ‖x‖+K := hn0.trans ((norm_sub_le x y).trans (add_le_add le_rfl hy))
      exact (div_le_div_of_nonneg_right hn hs0.le).trans (div_le_div_of_nonneg_left (by positivity) ha hs)
    _ = _ := integral_const_mul _ _
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory Set
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem smoothedGradient_measurable (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    (s : ℝ) (i : ι) : StronglyMeasurable (fun x => smoothedGradient μ s x i) := by
  exact (((normalGradient_continuous s i).comp (continuous_fst.sub continuous_snd)).stronglyMeasurable).integral_prod_right'
 theorem smoothedGradient_polynomial_bound (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {a s K : ℝ} (ha : 0<a) (hs : a ≤ s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    |smoothedGradient μ s x i| ≤ ((1+K)/a)*(1+‖x‖^2)*smoothedDensity μ s x := by
  apply (smoothedGradient_bound μ ha hs hK hμ x i).trans
  apply mul_le_mul_of_nonneg_right _ (smoothedDensity_pos μ (ha.trans_le hs) x).le
  have h : ‖x‖+K ≤ (1+K)*(1+‖x‖^2) := by nlinarith [sq_nonneg (‖x‖-1/2),mul_nonneg hK (sq_nonneg ‖x‖)]
  convert div_le_div_of_nonneg_right h ha.le using 1 ; ring
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianEntropyIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory Set
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem smoothedPolynomial_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (m : ℕ) :
    Integrable (fun x => (1+‖x‖^2)^m*smoothedDensity μ s x) := by
  let D := |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)|
  let A := Real.exp (D+K^2/(2*s))
  have hi := (polynomial_gaussian_integrable (E := EuclideanSpace ℝ ι) (c := 1/(4*s)) (by positivity) m).const_mul A
  apply hi.mono' (((continuous_const.add (continuous_norm.pow 2)).pow m).mul (smoothedDensity_continuous μ hs)).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    simp only [Pi.mul_apply,Pi.add_apply,Pi.pow_apply]
    have hp := smoothedDensity_pos μ hs x
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (1+‖x‖^2)^m*smoothedDensity μ s x)]
    have h := (smoothedDensity_bounds μ hs (show s∈Icc s s from ⟨le_rfl,le_rfl⟩) (show |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D from le_rfl) hK hμ x).2
    have he : -‖x‖^2/(4*s)=-(1/(4*s))*‖x‖^2 := by ring
    rw [he] at h
    simpa only [A,mul_assoc,mul_left_comm] using mul_le_mul_of_nonneg_left h (show 0 ≤ (1+‖x‖^2)^m by positivity))
 theorem smoothedIntegrable_of_bound {F : Type u2} [NormedAddCommGroup F]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    {f : EuclideanSpace ℝ ι → F} (hf : AEStronglyMeasurable f) (C : ℝ) (m : ℕ)
    (hb : ∀x,‖f x‖ ≤ C*(1+‖x‖^2)^m*smoothedDensity μ s x) : Integrable f := by
  apply ((smoothedPolynomial_integrable μ hs hK hμ m).const_mul C).mono' hf
  exact ae_of_all _ (fun x => by simpa only [mul_assoc] using hb x)
 theorem smoothedScore_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (i : ι) :
    Integrable (fun x => (smoothedGradient μ s x i)^2/smoothedDensity μ s x) := by
  let C := (1+K)/s
  apply smoothedIntegrable_of_bound μ hs hK hμ
    (((smoothedGradient_measurable μ s i).pow 2).div (smoothedDensity_continuous μ hs).stronglyMeasurable).aestronglyMeasurable (C^2) 2
  intro x
  simp only [Pi.pow_apply,Pi.div_apply]
  have hp := smoothedDensity_pos μ hs x
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hp).mpr
  have hb := smoothedGradient_polynomial_bound μ hs le_rfl hK hμ x i
  have hh := pow_le_pow_left₀ (abs_nonneg _) hb 2
  simp only [sq_abs] at hh
  dsimp only [C]
  nlinarith
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CoordinateIBP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 theorem integral_coordinate_ibp (i : ι) (f f' g g' : EuclideanSpace ℝ ι → ℝ)
    (hf : ∀x r,HasDerivAt (fun t : ℝ => f (x+t • EuclideanSpace.single i 1)) (f' (x+r • EuclideanSpace.single i 1)) r)
    (hg : ∀x r,HasDerivAt (fun t : ℝ => g (x+t • EuclideanSpace.single i 1)) (g' (x+r • EuclideanSpace.single i 1)) r)
    (hfg' : Integrable (fun x => f x*g' x)) (hf'g : Integrable (fun x => f' x*g x))
    (hfg : Integrable (fun x => f x*g x)) :
    (∫x,f x*g' x) = -(∫x,f' x*g x) := by
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ) hf'g hfg' hfg
  · intro x hx
    simpa only [HasLineDerivAt,zero_smul,add_zero] using hf x 0
  · intro x hx
    simpa only [HasLineDerivAt,zero_smul,add_zero] using hg x 0
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.PolynomialGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem mvPolynomial_norm_bound [DecidableEq ι] (P : MvPolynomial ι ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∃ m : ℕ,∀x : EuclideanSpace ℝ ι,
      |MvPolynomial.eval (WithLp.ofLp x) P| ≤ C*(1+‖x‖^2)^m := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨|c|,abs_nonneg _,0,by intro x; simp⟩
  | add P Q hP hQ =>
    obtain ⟨C,hC,m,hP⟩ := hP
    obtain ⟨D,hD,k,hQ⟩ := hQ
    refine ⟨C+D,add_nonneg hC hD,max m k,?_⟩
    intro x
    have hbase : 1≤1+‖x‖^2 := by nlinarith [sq_nonneg ‖x‖]
    calc
      _ ≤ |MvPolynomial.eval (WithLp.ofLp x) P|+|MvPolynomial.eval (WithLp.ofLp x) Q| := by simpa only [map_add] using abs_add_le (MvPolynomial.eval (WithLp.ofLp x) P) (MvPolynomial.eval (WithLp.ofLp x) Q)
      _ ≤ C*(1+‖x‖^2)^m+D*(1+‖x‖^2)^k := add_le_add (hP x) (hQ x)
      _ ≤ C*(1+‖x‖^2)^(max m k)+D*(1+‖x‖^2)^(max m k) := add_le_add
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (le_max_left m k)) hC)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (le_max_right m k)) hD)
      _ = _ := by ring
  | mul_X P i hP =>
    obtain ⟨C,hC,m,hP⟩ := hP
    refine ⟨C,hC,m+1,?_⟩
    intro x
    have hn : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
    have hn' : |x i| ≤ 1+‖x‖^2 := by nlinarith [sq_nonneg (‖x‖-1/2)]
    calc
      _ = |MvPolynomial.eval (WithLp.ofLp x) P| * |x i| := by simp only [map_mul,MvPolynomial.eval_X,abs_mul]
      _ ≤ (C*(1+‖x‖^2)^m)*(1+‖x‖^2) := mul_le_mul (hP x) hn' (abs_nonneg _) (by positivity)
      _ = _ := by rw [pow_succ]; ring
 namespace IsRealPolynomial
 theorem norm_bound {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) :
    ∃ C : ℝ,0 ≤ C ∧ ∃ m : ℕ,∀x : EuclideanSpace ℝ ι,|f (WithLp.ofLp x)| ≤ C*(1+‖x‖^2)^m := by
  obtain ⟨P,rfl⟩ := hf
  exact mvPolynomial_norm_bound P
 theorem smoothed_integrable {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] {s K : ℝ}
    (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) :
    Integrable (fun x => f (WithLp.ofLp x)*smoothedDensity μ s x) := by
  obtain ⟨C,hC,m,hb⟩ := hf.norm_bound
  apply smoothedIntegrable_of_bound μ hs hK hμ
    (((hf.continuous.comp (PiLp.continuous_ofLp 2 _)).mul (smoothedDensity_continuous μ hs)).aestronglyMeasurable) C m
  intro x
  change ‖f (WithLp.ofLp x)*smoothedDensity μ s x‖≤_
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (smoothedDensity_pos μ hs x)]
  exact mul_le_mul_of_nonneg_right (hb x) (smoothedDensity_pos μ hs x).le
 theorem smoothedGradient_integrable {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] {s K : ℝ}
    (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (i : ι) :
    Integrable (fun x => f (WithLp.ofLp x)*smoothedGradient μ s x i) := by
  obtain ⟨C,hC,m,hb⟩ := hf.norm_bound
  apply smoothedIntegrable_of_bound μ hs hK hμ
    ((((hf.continuous.comp (PiLp.continuous_ofLp 2 _)).stronglyMeasurable).mul (smoothedGradient_measurable μ s i)).aestronglyMeasurable) (C*((1+K)/s)) (m+1)
  intro x
  change ‖f (WithLp.ofLp x)*smoothedGradient μ s x i‖≤_
  rw [Real.norm_eq_abs,abs_mul]
  calc
    _ ≤ (C*(1+‖x‖^2)^m)*(((1+K)/s)*(1+‖x‖^2)*smoothedDensity μ s x) :=
      mul_le_mul (hb x) (smoothedGradient_polynomial_bound μ hs le_rfl hK hμ x i) (abs_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ]; ring
 theorem hasDerivAt_line {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f)
    (x : EuclideanSpace ℝ ι) (i : ι) (r : ℝ) :
    HasDerivAt (fun t : ℝ => f (WithLp.ofLp (x+t • EuclideanSpace.single i 1)))
      (coordinateDerivative f i (WithLp.ofLp (x+r • EuclideanSpace.single i 1))) r := by
  let y := x+r • EuclideanSpace.single i 1
  have hy : (WithLp.ofLp y) i = x i+r := by simp [y]
  have hd0 := hf.hasDerivAt i (WithLp.ofLp y)
  rw [hy] at hd0
  have hd := hd0.comp r ((hasDerivAt_id r).const_add (x i))
  convert hd using 1 <;> try rfl
  · funext t
    congr 1
    ext j
    by_cases h : j=i
    · subst j; simp
    · simp [y,h,EuclideanSpace.single]
  · simp [y]
 end IsRealPolynomial
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 theorem smoothed_polynomial_ibp (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (hs : 0<s)
    {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (i : ι) :
    (∫x,f (WithLp.ofLp x)*smoothedGradient μ s x i) =
      -(∫x,coordinateDerivative f i (WithLp.ofLp x)*smoothedDensity μ s x) := by
  have hm : ∀ᵐy ∂μ,y∈Metric.closedBall 0 K := by simpa only [Metric.mem_closedBall,dist_zero_right] using hμ
  exact integral_coordinate_ibp i (fun x => f (WithLp.ofLp x))
    (fun x => coordinateDerivative f i (WithLp.ofLp x))
    (smoothedDensity μ s) (fun x => smoothedGradient μ s x i)
    (fun x r => hf.hasDerivAt_line x i r)
    (fun x r => smoothedDensity_hasDeriv_coordinate μ (isCompact_closedBall _ _) hm s x i r)
    (hf.smoothedGradient_integrable μ hs hK hμ i)
    ((hf.derivative i).smoothed_integrable μ hs hK hμ)
    (hf.smoothed_integrable μ hs hK hμ)
 theorem smoothed_score_lower (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (hs : 0<s)
    {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (i : ι) :
    (∫x,(2*coordinateDerivative f i (WithLp.ofLp x)-f (WithLp.ofLp x)^2)*smoothedDensity μ s x) ≤
      ∫x,(smoothedGradient μ s x i)^2/smoothedDensity μ s x := by
  have hd := (hf.derivative i).smoothed_integrable μ hs hK hμ
  have hsq := (hf.pow 2).smoothed_integrable μ hs hK hμ
  have hg := hf.smoothedGradient_integrable μ hs hK hμ i
  have hi := smoothedScore_integrable μ hs hK hμ i
  have hle : 0 ≤ ∫x,(smoothedGradient μ s x i)^2/smoothedDensity μ s x +
      2*(f (WithLp.ofLp x)*smoothedGradient μ s x i)+f (WithLp.ofLp x)^2*smoothedDensity μ s x := by
    apply integral_nonneg
    intro x
    have hp := smoothedDensity_pos μ hs x
    have hsq' := sq_nonneg (smoothedGradient μ s x i+f (WithLp.ofLp x)*smoothedDensity μ s x)
    have he : (smoothedGradient μ s x i)^2/smoothedDensity μ s x + 2*(f (WithLp.ofLp x)*smoothedGradient μ s x i)+f (WithLp.ofLp x)^2*smoothedDensity μ s x =
        (smoothedGradient μ s x i+f (WithLp.ofLp x)*smoothedDensity μ s x)^2/smoothedDensity μ s x := by field_simp; ring
    change 0 ≤ (smoothedGradient μ s x i)^2/smoothedDensity μ s x + 2*(f (WithLp.ofLp x)*smoothedGradient μ s x i)+f (WithLp.ofLp x)^2*smoothedDensity μ s x
    rw [he]
    exact div_nonneg hsq' hp.le
  have hsum := integral_add (hi.add (hg.const_mul 2)) hsq
  have hsum' := integral_add hi (hg.const_mul 2)
  simp only [Pi.add_apply] at hsum hsum'
  rw [hsum,hsum',integral_const_mul,smoothed_polynomial_ibp μ hK hμ hs hf i] at hle
  have he : (fun x => (2*coordinateDerivative f i (WithLp.ofLp x)-f (WithLp.ofLp x)^2)*smoothedDensity μ s x) =
      fun x => 2*(coordinateDerivative f i (WithLp.ofLp x)*smoothedDensity μ s x)-f (WithLp.ofLp x)^2*smoothedDensity μ s x := by
    funext x; ring
  rw [he,integral_sub (hd.const_mul 2) hsq,integral_const_mul]
  linarith
 theorem classicalFisher_polynomial_lower (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (hs : 0<s)
    (f : ι → (ι → ℝ) → ℝ) (hf : ∀i,IsRealPolynomial (f i)) :
    (∑i,∫x,(2*coordinateDerivative (f i) i (WithLp.ofLp x)-(f i (WithLp.ofLp x))^2)*smoothedDensity μ s x) ≤
      classicalFisher μ s :=
  sum_le_sum (fun i _ => smoothed_score_lower μ hK hμ hs (hf i) i)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixFisherTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset MeasureTheory
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem matrixRealScore_polynomial (p : WordPolynomial n) (j k : Fin d) :
    IsRealPolynomial (matrixRealScore p j k) := (matrixScorePolynomial_polynomial p j k).1.const_mul d
 theorem matrixRealScore_derivative (p : WordPolynomial n) (i : Fin n) (j k : Fin d) (x : MatrixIndex n d → ℝ) :
    coordinateDerivative (matrixRealScore p j k) (i,j,k) x =
      (d:ℝ)*(complexCoordinateDerivative (matrixScorePolynomial p j k) (i,j,k) x).re := by
  have hp := (matrixScorePolynomial_polynomial p j k)
  rw [hp.coordinateDerivative_eq]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero]
  exact ((hp.1.hasDerivAt (i,j,k) x).const_mul (d:ℝ)).deriv
 theorem matrixRealScore_divergence (hd : 0<d) (p : WordPolynomial n) (i : Fin n) (x : MatrixIndex n d → ℝ) :
    (∑j,∑k,coordinateDerivative (matrixRealScore p j k) (i,j,k) x) =
      (d:ℝ)^3*(matrixPolynomialDerivative p i (WithLp.toLp 2 x)).re := by
  simp_rw [matrixRealScore_derivative]
  simp_rw [← mul_sum]
  simp_rw [← Complex.re_sum]
  rw [matrixScorePolynomial_divergence]
  have hdC : (d:ℂ)≠0 := by exact_mod_cast hd.ne'
  have he : (∑w∈p.support,p w*∑r : Fin w.length,if w[r.val]=i then
        Matrix.trace (matrixWord (coordinateMatrix x) (w.take r.val))*Matrix.trace (matrixWord (coordinateMatrix x) (w.drop (r.val+1))) else 0) =
      (d:ℂ)^2*matrixPolynomialDerivative p i (WithLp.toLp 2 x) := by
    unfold matrixPolynomialDerivative matrixMoment
    simp only [mul_sum]
    apply sum_congr rfl
    intro w _
    apply sum_congr rfl
    intro r _
    split_ifs
    · dsimp [coordinateMatrix,matrixWord]
      field_simp
      ; ring_nf ; rfl
    · ring
  rw [he]
  simp only [← Complex.ofReal_natCast,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring
 theorem matrixFisherTest_pointwise (hd : 0<d) (p : WordPolynomial n) (i : Fin n) (a : MatrixCoordinates n d) :
    (d:ℝ)^3*matrixFisherTest p i a ≤
      ∑j,∑k,(2*coordinateDerivative (matrixRealScore p j k) (i,j,k) (WithLp.ofLp a)-matrixRealScore p j k (WithLp.ofLp a)^2) := by
  have hdiv := matrixRealScore_divergence hd p i (WithLp.ofLp a)
  have hn := matrixScorePolynomial_norm_lower p (WithLp.ofLp a)
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hn' : (∑j,∑k,matrixRealScore p j k (WithLp.ofLp a)^2) ≤ (d:ℝ)^3*matrixPolynomialNorm p a := by
    simp only [matrixRealScore,mul_pow,← mul_sum]
    rw [matrixPolynomialNorm_trace]
    have he : (d:ℝ)^3*((d:ℝ)⁻¹*(Matrix.trace ((matrixPolynomial p (hermitianMatrix a)).conjTranspose*matrixPolynomial p (hermitianMatrix a))).re) =
      (d:ℝ)^2*(Matrix.trace ((matrixPolynomial p (coordinateMatrix (WithLp.ofLp a))).conjTranspose*matrixPolynomial p (coordinateMatrix (WithLp.ofLp a)))).re := by
      change (d:ℝ)^3*((d:ℝ)⁻¹*(Matrix.trace ((matrixPolynomial p (hermitianMatrix a)).conjTranspose*matrixPolynomial p (hermitianMatrix a))).re)= (d:ℝ)^2*(Matrix.trace ((matrixPolynomial p (hermitianMatrix a)).conjTranspose*matrixPolynomial p (hermitianMatrix a))).re
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hn (sq_nonneg _)
  simp only [sum_sub_distrib,← mul_sum] at *
  rw [hdiv]
  dsimp [matrixFisherTest]
  nlinarith
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixTestPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Finset
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem matrixMoment_polynomial (w : List (Fin n)) :
    IsComplexPolynomial (fun x : MatrixIndex n d → ℝ => matrixMoment (WithLp.toLp 2 x) w) :=
  ((IsMatrixPolynomial.word (fun i a b => coordinateMatrix_polynomial i a b) w).trace).const_mul ((d:ℂ)⁻¹)
 theorem matrixPolynomialDerivative_polynomial (p : WordPolynomial n) (i : Fin n) :
    IsComplexPolynomial (fun x : MatrixIndex n d → ℝ => matrixPolynomialDerivative p i (WithLp.toLp 2 x)) := by
  apply IsComplexPolynomial.finset_sum p.support
  intro w _
  apply IsComplexPolynomial.const_mul
  apply IsComplexPolynomial.finset_sum univ
  intro r _
  by_cases h : w[r.val]=i
  · simp only [h,ite_true]
    exact (matrixMoment_polynomial _).mul (matrixMoment_polynomial _)
  · simp only [h,ite_false]
    exact IsComplexPolynomial.const 0
 theorem matrixPolynomialNorm_polynomial (p : WordPolynomial n) :
    IsRealPolynomial (fun x : MatrixIndex n d → ℝ => matrixPolynomialNorm p (WithLp.toLp 2 x)) :=
  (IsComplexPolynomial.finset_sum p.support (fun u _ => IsComplexPolynomial.finset_sum p.support
    (fun v _ => (matrixMoment_polynomial (u.reverse++v)).const_mul (star (p u)*p v)))).1
 theorem matrixFisherTest_polynomial (p : WordPolynomial n) (i : Fin n) :
    IsRealPolynomial (fun x : MatrixIndex n d → ℝ => matrixFisherTest p i (WithLp.toLp 2 x)) :=
  ((matrixPolynomialDerivative_polynomial p i).1.const_mul 2).sub (matrixPolynomialNorm_polynomial p)
 theorem matrix_classicalFisher_lower (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0 ≤ K) (hμ : ∀ᵐy ∂μ,‖y‖ ≤ K) (hs : 0<s)
    (p : Fin n → WordPolynomial n) :
    (d:ℝ)^3*(∑i,∫a,matrixFisherTest (p i) i a*smoothedDensity μ s a) ≤ classicalFisher μ s := by
  let f : MatrixIndex n d → (MatrixIndex n d → ℝ) → ℝ := fun q => matrixRealScore (p q.1) q.2.1 q.2.2
  have hf q : IsRealPolynomial (f q) := matrixRealScore_polynomial _ _ _
  have hc := classicalFisher_polynomial_lower μ hK hμ hs f hf
  have hi i : Integrable (fun a => matrixFisherTest (p i) i a*smoothedDensity μ s a) :=
    (matrixFisherTest_polynomial (p i) i).smoothed_integrable μ hs hK hμ
  have hj q : Integrable (fun a => (2*coordinateDerivative (f q) q (WithLp.ofLp a)-(f q (WithLp.ofLp a))^2)*smoothedDensity μ s a) :=
    (((hf q).derivative q).const_mul 2 |>.sub ((hf q).pow 2)).smoothed_integrable μ hs hK hμ
  apply le_trans _ hc
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  rw [← integral_const_mul]
  simp_rw [← integral_finsetSum _ (fun k _ => hj (i,_,k))]
  rw [← integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hj (i,j,k)))]
  apply integral_mono ((hi i).const_mul _) (integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hj (i,j,k))))
  intro a
  have hp := mul_le_mul_of_nonneg_right (matrixFisherTest_pointwise hd (p i) i a) (smoothedDensity_pos μ hs a).le
  simpa only [sum_mul,mul_assoc] using hp
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixHeatLawMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem integral_heatLaw_eq {E : Type u1} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ] {s : ℝ} (hs : 0<s)
    (f : MatrixCoordinates n d → E) (hf : Continuous f) :
    (∫a,f a ∂matrixHeatLaw μ s) = ∫z,f (heatCoordinates z.1 s z.2) ∂μ.prod (productGaussian (MatrixIndex n d)) := by
  rw [matrixHeatLaw_eq hd μ hs]
  exact integral_map (heatCoordinates_continuous s).measurable.aemeasurable hf.aestronglyMeasurable
 theorem integrable_heatLaw_iff {E : Type u2} [NormedAddCommGroup E]
    (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ] {s : ℝ} (hs : 0<s)
    (f : MatrixCoordinates n d → E) (hf : Continuous f) :
    Integrable f (matrixHeatLaw μ s) ↔ Integrable (fun z => f (heatCoordinates z.1 s z.2)) (μ.prod (productGaussian (MatrixIndex n d))) := by
  rw [matrixHeatLaw_eq hd μ hs]
  exact integrable_map_measure hf.aestronglyMeasurable (heatCoordinates_continuous s).measurable.aemeasurable
 theorem matrixHeatLaw_moment_integrable (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {R s : ℝ} (hR : 0 ≤ R) (hμ : ∀ᵐa ∂μ,∀i,matrixOpNorm (hermitianMatrix a i) ≤ R) (hs : 0<s) (w : List (Fin n)) :
    Integrable (fun a => matrixMoment a w) (matrixHeatLaw μ s) :=
  (integrable_heatLaw_iff hd μ hs _ (matrixMoment_continuous w)).mpr (heatMoment_integrable hd μ hR hμ s w)
 theorem matrixHeatLaw_product_integrable (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {R s : ℝ} (hR : 0 ≤ R) (hμ : ∀ᵐa ∂μ,∀i,matrixOpNorm (hermitianMatrix a i) ≤ R) (hs : 0<s) (v w : List (Fin n)) :
    Integrable (fun a => matrixMoment a v*matrixMoment a w) (matrixHeatLaw μ s) := by
  apply (integrable_heatLaw_iff hd μ hs _ ((matrixMoment_continuous v).mul (matrixMoment_continuous w))).mpr
  exact complex_mul_integrable_of_squares _
    (((matrixMoment_continuous v).comp (heatCoordinates_continuous s)).aestronglyMeasurable)
    (((matrixMoment_continuous w).comp (heatCoordinates_continuous s)).aestronglyMeasurable)
    (heatMoment_power_integrable hd μ hR hμ s v 2) (heatMoment_power_integrable hd μ hR hμ s w 2)
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
  (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀i,X i ∈ backgroundAlgebra J)
  {R : ℝ} (hR : 0 ≤ R) (hn : ∀k,(diagonalMicrostates (tracialVector B N G) X R k (D k)).Nonempty)
  (σ : Fin n → N) (hσ : Function.Injective σ) (hsigma : ∀i,σ i ∉ J)
  (μ : (k:ℕ) → Measure (MatrixCoordinates n (D k))) [∀k,IsProbabilityMeasure (μ k)]
  (hμ : ∀k,∀ᵐ a ∂μ k,a ∈ diagonalMicrostates (tracialVector B N G) X R k (D k))
include hD0 hD hX hR hn hσ hsigma hμ
 theorem matrixHeatLaw_moment_tendsto {s : ℝ} (hs : 0<s) (w : List (Fin n)) :
    Tendsto (fun k => ∫a,matrixMoment a w ∂matrixHeatLaw (μ k) s) atTop
      (𝓝 (wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) s) w)) := by
  simp_rw [integral_heatLaw_eq (hD0 _) _ hs _ (matrixMoment_continuous w)]
  exact heatMoment_product_tendsto hD0 hD J X hX hR hn σ hσ hsigma μ hμ s w
 theorem matrixHeatLaw_product_tendsto {s : ℝ} (hs : 0<s) (v w : List (Fin n)) :
    Tendsto (fun k => ∫a,matrixMoment a v*matrixMoment a w ∂matrixHeatLaw (μ k) s) atTop
      (𝓝 (wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) s) v*
        wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) s) w)) := by
  have he (k : ℕ) := integral_heatLaw_eq (hD0 k) (μ k) hs (fun a => matrixMoment a v*matrixMoment a w) ((matrixMoment_continuous v).mul (matrixMoment_continuous w))
  simp_rw [he]
  exact heatMoment_products_tendsto hD0 hD J X hX hR hn σ hσ hsigma μ hμ s v w
end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FisherTestLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory Finset Filter
open scoped Topology
namespace FiniteEntropySeparation
 theorem complex_integrable_re {Ω : Type u1} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℂ}
    (hf : Integrable f μ) : Integrable (fun x => (f x).re) μ := hf.re
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H) (hX : ∀i,IsSelfAdjoint (X i))
variable {D : ℕ → ℕ} (ν : (k:ℕ) → Measure (MatrixCoordinates n (D k)))
  (hi : ∀k w,Integrable (fun a => matrixMoment a w) (ν k))
  (hip : ∀k v w,Integrable (fun a => matrixMoment a v*matrixMoment a w) (ν k))
  (ht : ∀w,Tendsto (fun k => ∫a,matrixMoment a w ∂ν k) atTop (𝓝 (wordMoment τ X w)))
  (htp : ∀v w,Tendsto (fun k => ∫a,matrixMoment a v*matrixMoment a w ∂ν k) atTop (𝓝 (wordMoment τ X v*wordMoment τ X w)))
 include hi in
 theorem matrixPolynomialNorm_integrable (k : ℕ) (p : WordPolynomial n) :
    Integrable (matrixPolynomialNorm p) (ν k) :=
  (integrable_finsetSum p.support (fun u _ => integrable_finsetSum p.support (fun v _ => (hi k (u.reverse++v)).const_mul (star (p u)*p v)))).re
 include hip in
 theorem matrixPolynomialDerivative_integrable (k : ℕ) (p : WordPolynomial n) (i : Fin n) :
    Integrable (matrixPolynomialDerivative p i) (ν k) := by
  apply integrable_finsetSum p.support
  intro w _
  apply Integrable.const_mul
  apply integrable_finsetSum univ
  intro r _
  by_cases h : w[r.val]=i
  · simpa only [h,ite_true] using hip k (w.take r.val) (w.drop (r.val+1))
  · simp only [h,ite_false]
    exact integrable_zero _ _ _
 include hi ht hX in
 theorem matrixPolynomialNorm_integral_tendsto (p : WordPolynomial n) :
    Tendsto (fun k => ∫a,matrixPolynomialNorm p a ∂ν k) atTop (𝓝 (‖polynomialVector τ X p‖^2)) := by
  have he k : (∫a,matrixPolynomialNorm p a ∂ν k) =
      (∑u∈p.support,∑v∈p.support,star (p u)*p v*(∫a,matrixMoment a (u.reverse++v) ∂ν k)).re := by
    simp only [matrixPolynomialNorm]
    rw [← complex_integral_re (integrable_finsetSum _ (fun u _ => integrable_finsetSum _ (fun v _ => (hi k _).const_mul _)))]
    rw [integral_finsetSum _ (fun u _ => integrable_finsetSum _ (fun v _ => (hi k _).const_mul _))]
    simp_rw [integral_finsetSum _ (fun v _ => (hi k _).const_mul _),integral_const_mul]
  simp_rw [he]
  rw [polynomialVector_norm_formula τ X hX]
  exact Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_finsetSum p.support (fun u _ => tendsto_finsetSum p.support (fun v _ => (ht _).const_mul _)))
 include hip htp in
 theorem matrixPolynomialDerivative_integral_tendsto (p : WordPolynomial n) (i : Fin n) :
    Tendsto (fun k => ∫a,matrixPolynomialDerivative p i a ∂ν k) atTop (𝓝 (polynomialDerivative τ X i p)) := by
  have hir (k : ℕ) (w : List (Fin n)) (r : Fin w.length) : Integrable (fun a : MatrixCoordinates n (D k) => if w[r.val]=i then matrixMoment a (w.take r.val)*matrixMoment a (w.drop (r.val+1)) else 0) (ν k) := by
    by_cases h : w[r.val]=i
    · simpa only [h,ite_true] using hip k (w.take r.val) (w.drop (r.val+1))
    · simp only [h,ite_false]; exact integrable_zero _ _ _
  have he k : (∫a,matrixPolynomialDerivative p i a ∂ν k) =
      ∑w∈p.support,p w*∑r : Fin w.length,if w[r.val]=i then (∫a,matrixMoment a (w.take r.val)*matrixMoment a (w.drop (r.val+1)) ∂ν k) else 0 := by
    simp only [matrixPolynomialDerivative]
    rw [integral_finsetSum _ (fun w _ => (integrable_finsetSum _ (fun r _ => hir k w r)).const_mul _)]
    apply sum_congr rfl
    intro w _
    rw [integral_const_mul,integral_finsetSum _ (fun r _ => hir k w r)]
    congr 1
    apply sum_congr rfl
    intro r _
    split_ifs <;> simp
  simp_rw [he]
  simp only [polynomialDerivative,Finsupp.linearCombination_apply,Finsupp.sum,smul_eq_mul,derivativeMoment]
  apply tendsto_finsetSum p.support
  intro w _
  apply Tendsto.const_mul
  apply tendsto_finsetSum univ
  intro r _
  split_ifs
  · exact htp _ _
  · exact tendsto_const_nhds
 include hi hip ht htp hX in
 theorem matrixFisherTest_integral_tendsto (p : WordPolynomial n) (i : Fin n) :
    Tendsto (fun k => ∫a,matrixFisherTest p i a ∂ν k) atTop (𝓝 (fisherTest τ X i p)) := by
  have he k : (∫a,matrixFisherTest p i a ∂ν k) =
      2*(∫a,matrixPolynomialDerivative p i a ∂ν k).re-∫a,matrixPolynomialNorm p a ∂ν k := by
    simp only [matrixFisherTest]
    rw [integral_sub ((complex_integrable_re (matrixPolynomialDerivative_integrable ν hip k p i)).const_mul 2) (matrixPolynomialNorm_integrable ν hi k p),integral_const_mul,← complex_integral_re (matrixPolynomialDerivative_integrable ν hip k p i)]
  simp_rw [he]
  exact ((Complex.continuous_re.continuousAt.tendsto.comp (matrixPolynomialDerivative_integral_tendsto τ X ν hip htp p i)).const_mul 2).sub
    (matrixPolynomialNorm_integral_tendsto τ X hX ν hi ht p)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FisherLiminf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open Finset Filter
open scoped Topology ENNReal
namespace FiniteEntropySeparation
 theorem ennreal_sum_iSup_tuple {P : Type u1} [Nonempty P] (n : ℕ) (f : Fin n → P → ℝ≥0∞) :
    (∑i,⨆p,f i p) = ⨆p : Fin n → P,∑i,f i (p i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ,ih (fun i => f i.succ),ENNReal.iSup_add]
    simp_rw [ENNReal.add_iSup]
    apply le_antisymm
    · apply iSup_le
      intro a
      apply iSup_le
      intro p
      exact le_iSup_of_le (Fin.cons a p) (by simp [Fin.sum_univ_succ])
    · apply iSup_le
      intro p
      exact le_iSup_of_le (p 0) (le_iSup_of_le (fun i => p i.succ) (by simp [Fin.sum_univ_succ]))
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
 theorem fisherTest_zero (i : Fin n) : fisherTest τ X i 0 = 0 := by simp [fisherTest]
 theorem freeFisher_le_liminf_tests {ξ : Fin n → H} (hξ : ConjugateSystem τ X ξ)
    (t : ℕ → Fin n → WordPolynomial n → ℝ) (I : ℕ → ℝ)
    (ht : ∀i p,Tendsto (fun k => t k i p) atTop (𝓝 (fisherTest τ X i p)))
    (hI : ∀k (p : Fin n → WordPolynomial n),∑i,t k i (p i) ≤ I k) :
    freeFisher τ X ≤ liminf (fun k => ENNReal.ofReal (I k)) atTop := by
  rw [freeFisher_variational τ X hξ,ennreal_sum_iSup_tuple]
  apply iSup_le
  intro p
  let q : Fin n → WordPolynomial n := fun i => if 0 ≤ fisherTest τ X i (p i) then p i else 0
  have hq i : 0 ≤ fisherTest τ X i (q i) := by
    dsimp [q]
    split_ifs with h
    · exact h
    · rw [fisherTest_zero]
  have he i : ENNReal.ofReal (fisherTest τ X i (p i)) = ENNReal.ofReal (fisherTest τ X i (q i)) := by
    dsimp [q]
    split_ifs with h
    · rfl
    · rw [fisherTest_zero,ENNReal.ofReal_zero,ENNReal.ofReal_eq_zero]
      exact le_of_not_ge h
  simp_rw [he]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hq i)]
  have ht' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_finsetSum univ (fun i _ => ht i (q i)))
  rw [← ht'.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall (fun k => ENNReal.ofReal_le_ofReal (hI k q)))
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixFisherLiminf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Finset
open scoped Topology
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem matrixHeatLaw_fisher_lower (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (hs : 0<s) (p : Fin n → WordPolynomial n) :
    (∑i,∫a,matrixFisherTest (p i) i a ∂matrixHeatLaw μ s) ≤ normalizedMatrixFisher μ s := by
  rw [normalizedMatrixFisher,le_div_iff₀ (by positivity : (0:ℝ)<(d:ℝ)^3)]
  simp_rw [integral_matrixHeatLaw μ hs hd,mul_comm (smoothedDensity μ (s/d) _) _]
  simpa only [mul_comm] using matrix_classicalFisher_lower hd μ hK hμ (div_pos hs (by exact_mod_cast hd)) p
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
  (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀i,X i ∈ backgroundAlgebra J)
  (hself : ∀i,IsSelfAdjoint (X i))
  {R : ℝ} (hR : 0≤R) (hn : ∀k,(diagonalMicrostates (tracialVector B N G) X R k (D k)).Nonempty)
  (σ : Fin n → N) (hσ : Function.Injective σ) (hsigma : ∀i,σ i ∉ J)
  (μ : (k:ℕ) → Measure (MatrixCoordinates n (D k))) [∀k,IsProbabilityMeasure (μ k)]
  (hμ : ∀k,∀ᵐa ∂μ k,a ∈ diagonalMicrostates (tracialVector B N G) X R k (D k))
include hR hμ in

omit [∀ (k : ℕ), IsProbabilityMeasure (μ k)] in
theorem diagonalMicrostates_norm_ae [∀ (k : ℕ), IsProbabilityMeasure (μ k)] (k : ℕ) :
    ∀ᵐa ∂μ k,‖a‖≤Real.sqrt ((n:ℝ)*D k)*R := by
  filter_upwards [hμ k] with a ha
  have hb := microstates_subset_closedBall (tracialVector B N G) X R hR k (D k) ((k+1:ℝ)⁻¹) ha
  simpa only [Metric.mem_closedBall,dist_zero_right] using hb
include hD0 hD hX hself hR hn hσ hsigma hμ in
 theorem matrixHeatLaw_fisherTest_tendsto {s : ℝ} (hs : 0<s) (i : Fin n) (p : WordPolynomial n) :
    Tendsto (fun k => ∫a,matrixFisherTest p i a ∂matrixHeatLaw (μ k) s) atTop
      (𝓝 (fisherTest (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) s) i p)) := by
  have hb k : ∀ᵐa ∂μ k,∀i,matrixOpNorm (hermitianMatrix a i) ≤ R := (hμ k).mono (fun _ ha => ha.1)
  exact matrixFisherTest_integral_tendsto
    (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) s)
    (heatTuple_selfAdjoint X (fun i => semicircularN (σ i)) hself (fun i => semicircularN_selfAdjoint (B := B) (G := G) (σ i)) s)
    (fun k => matrixHeatLaw (μ k) s)
    (fun k w => matrixHeatLaw_moment_integrable (hD0 k) (μ k) hR (hb k) hs w)
    (fun k v w => matrixHeatLaw_product_integrable (hD0 k) (μ k) hR (hb k) hs v w)
    (matrixHeatLaw_moment_tendsto hD0 hD J X hX hR hn σ hσ hsigma μ hμ hs)
    (matrixHeatLaw_product_tendsto hD0 hD J X hX hR hn σ hσ hsigma μ hμ hs) p i
include hD0 hD hX hself hR hn hσ hsigma hμ in
 theorem freeFisher_le_liminf_matrixFisher_oai {s : ℝ} (hs : 0<s) :
    freeFisher (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) s) ≤
      liminf (fun k => ENNReal.ofReal (normalizedMatrixFisher (μ k) s)) atTop := by
  obtain ⟨ξ,hξ⟩ := heat_conjugates_exist J X hX σ hσ hsigma s hs
  apply freeFisher_le_liminf_tests _ _ hξ (fun k i p => ∫a,matrixFisherTest p i a ∂matrixHeatLaw (μ k) s)
  · exact matrixHeatLaw_fisherTest_tendsto hD0 hD J X hX hself hR hn σ hσ hsigma μ hμ hs
  · intro k p
    exact matrixHeatLaw_fisher_lower (hD0 k) (μ k) (show 0≤Real.sqrt ((n:ℝ)*D k)*R by positivity)
      (diagonalMicrostates_norm_ae X hR μ hμ k) hs p
end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

theorem solution : type_of% @OAI.FiniteEntropySeparation.FreeTensor.freeFisher_le_liminf_matrixFisher_oai := @OAI.FiniteEntropySeparation.FreeTensor.freeFisher_le_liminf_matrixFisher_oai
