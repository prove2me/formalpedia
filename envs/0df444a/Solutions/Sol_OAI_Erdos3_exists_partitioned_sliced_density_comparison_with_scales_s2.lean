-- Prove2me | solution 1 for OAI.Erdos3.exists_partitioned_sliced_density_comparison_with_scales_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:12:47.72217+00:00
-- url     : https://prove2.me/submissions/0af58362-55c8-482e-8f92-25d0c00ac471

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B112
import Definitions.Def_OAIE3v2B113
import Definitions.Def_OAIE3v2B162
import Theorems.Thm_OAI_Erdos3_exists_uniform_joint_affine_polynomial_source_with_scales_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothedImageTest
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem mappedTest_integrable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → X) (hU : Measurable U)
    (φ : X → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    Integrable (fun a => φ (U a)) μ :=
  (integrable_const (1 : ℝ)).mono' (hφ.comp hU).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun a => hbound (U a)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem tensorCutoffWeight_tsupport {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, TopologicalSpace (E i)]
    (w : ∀ i, E i → ℝ) :
    tsupport (tensorCutoffWeight w) ⊆ {x | ∀ i, x i ∈ tsupport (w i)} := by
  have hc : IsClosed {x : ∀ i, E i | ∀ i, x i ∈ tsupport (w i)} := by
    have he : {x : ∀ i, E i | ∀ i, x i ∈ tsupport (w i)} =
        ⋂ i, (fun x : ∀ i, E i => x i) ⁻¹' tsupport (w i) := by ext; simp
    rw [he]
    exact isClosed_iInter (fun i => (isClosed_tsupport _).preimage (continuous_apply i))
  apply closure_minimal _ hc
  intro x hx i
  apply subset_closure
  change w i (x i) ≠ 0
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

theorem tensorCutoffWeight_compact {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, TopologicalSpace (E i)]
    (w : ∀ i, E i → ℝ) (hw : ∀ i, HasCompactSupport (w i)) :
    HasCompactSupport (tensorCutoffWeight w) :=
  (isCompact_pi_infinite hw).of_isClosed_subset (isClosed_tsupport _)
    (tensorCutoffWeight_tsupport w)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem smoothProductProfile_contDiff (I : Type*) [Fintype I] :
    ContDiff ℝ ∞ (smoothProductProfile I) := by
  rw [smoothProductProfile_eq_cutoff]
  exact contDiff_coordinateBoxCutoff _ smoothProbabilityProfile_contDiff 1

theorem smoothProductProfile_compact (I : Type*) [Fintype I] :
    HasCompactSupport (smoothProductProfile I) := by
  rw [smoothProductProfile_eq_cutoff]
  exact hasCompactSupport_coordinateBoxCutoff _ smoothProbabilityProfile_zero zero_lt_one

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_const {α R : Type*} [DecidableEq α] [CommRing R]
    (c : R) (s : Finset α) : booleanCoefficient (fun _ => c) s = if s = ∅ then c else 0 := by
  have h1 := booleanCoefficient_monomial (R := R) ∅ s
  simp only [Finset.empty_subset, ite_true] at h1
  have hc := booleanCoefficient_const_mul s c (fun _ => (1 : R))
  simpa only [mul_one, h1, mul_ite, mul_zero] using hc

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem polynomialMonomial_eval {K I : Type*}
    (a : K → MvPolynomial I ℝ) (m : K →₀ ℕ) (x : I → ℝ) :
    MvPolynomial.eval x (polynomialMonomial a m) =
      ∏ k ∈ m.support, MvPolynomial.eval x (a k) ^ m k := by
  simp only [polynomialMonomial, map_prod, map_pow]

theorem polynomialMonomial_mass_le {K I : Type*}
    (a : K → MvPolynomial I ℝ) (m : K →₀ ℕ) {M : ℝ}
    (ha : ∀ k ∈ m.support, realPolynomialMass (a k) ≤ M) :
    realPolynomialMass (polynomialMonomial a m) ≤ M ^ (m.sum fun _ n => n) := by
  classical
  apply (realPolynomialMass_prod_le _ _).trans
  calc
    _ ≤ ∏ k ∈ m.support, M ^ m k := by
      apply Finset.prod_le_prod (fun _ _ => realPolynomialMass_nonneg _)
      intro k hk
      exact (realPolynomialMass_pow_le _ _).trans
        (pow_le_pow_left₀ (realPolynomialMass_nonneg _) (ha k hk) _)
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum]; rfl

theorem polynomialMonomial_totalDegree_le {K I : Type*}
    (a : K → MvPolynomial I ℝ) (m : K →₀ ℕ) {e : ℕ}
    (ha : ∀ k ∈ m.support, (a k).totalDegree ≤ e) :
    (polynomialMonomial a m).totalDegree ≤ (m.sum fun _ n => n) * e := by
  classical
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ k ∈ m.support, m k * e := Finset.sum_le_sum (fun k hk =>
      (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (ha k hk)))
    _ = _ := by rw [← Finset.sum_mul]; rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDerivativeBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanAffinePolynomial_eval {B F α : Type*} [Fintype α] [DecidableEq α]
    (a : BlockParameter B F α → ℝ) (b : B) (v : F) (t : Finset α) :
    MvPolynomial.eval a (booleanAffinePolynomial b v t) =
      ∑ r : Option α, (booleanFeature r t : ℝ) * a (b, v, r) := by
  simp only [booleanAffinePolynomial, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F α O : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

omit [DecidableEq B] [DecidableEq F] in
theorem booleanSamplerMap_formula (c : B → ℝ) (sets : O → Finset α)
    (a : BlockParameter B F α → ℝ) (o : O) :
    booleanSamplerMap c sets a o = booleanCoefficient
      (fun t => ∑ b : B, c b * ∏ k : F, ∑ r : Option α, (booleanFeature r t : ℝ) * a (b, k, r)) (sets o) := by
  simp only [booleanSamplerMap, booleanSamplerPolynomial, booleanCoefficient_map, map_sum,
    map_mul, MvPolynomial.eval_C, booleanBlockPolynomial, map_prod, booleanAffinePolynomial_eval]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanFeature_abs_le_one {α : Type*} [DecidableEq α]
    (r : Option α) (t : Finset α) : |(booleanFeature r t : ℝ)| ≤ 1 := by
  cases r with
  | none => norm_num [booleanFeature]
  | some a => simp only [booleanFeature]; split_ifs <;> norm_num

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BooleanPolynomialBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_mass_le {I α : Type*} [DecidableEq α]
    (p : Finset α → MvPolynomial I ℝ) (s : Finset α) {M : ℝ}
    (hp : ∀ t ∈ s.powerset, realPolynomialMass (p t) ≤ M) :
    realPolynomialMass (booleanCoefficient p s) ≤ (2 : ℝ) ^ s.card * M := by
  classical
  unfold booleanCoefficient
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _t ∈ s.powerset, M := by
      apply Finset.sum_le_sum
      intro t ht
      have he : (-1 : MvPolynomial I ℝ) ^ (s \ t).card =
          MvPolynomial.C ((-1 : ℝ) ^ (s \ t).card) := by simp
      rw [he]
      exact (realPolynomialMass_C_mul_le _ _).trans (by simpa using hp t ht)
    _ = _ := by simp

theorem booleanCoefficient_totalDegree_le {I α : Type*} [DecidableEq α]
    (p : Finset α → MvPolynomial I ℝ) (s : Finset α) {d : ℕ}
    (hp : ∀ t ∈ s.powerset, (p t).totalDegree ≤ d) :
    (booleanCoefficient p s).totalDegree ≤ d := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro t ht
  have he : (-1 : MvPolynomial I ℝ) ^ (s \ t).card =
      MvPolynomial.C ((-1 : ℝ) ^ (s \ t).card) := by simp
  rw [he]
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa only [MvPolynomial.totalDegree_C, zero_add] using hp t ht)

theorem booleanAffinePolynomial_mass_le {B F α : Type*} [Fintype α] [DecidableEq α]
    (b : B) (v : F) (t : Finset α) :
    realPolynomialMass (booleanAffinePolynomial b v t) ≤ (Fintype.card α : ℝ) + 1 := by
  classical
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _r : Option α, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r _
      exact (realPolynomialMass_C_mul_le _ _).trans (by
        simpa only [realPolynomialMass_X, mul_one] using booleanFeature_abs_le_one r t)
    _ = _ := by simp

theorem booleanAffinePolynomial_totalDegree_le {B F α : Type*} [Fintype α] [DecidableEq α]
    (b : B) (v : F) (t : Finset α) : (booleanAffinePolynomial b v t).totalDegree ≤ 1 := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro r _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

theorem booleanBlockPolynomial_mass_le {B F α : Type*} [Fintype F] [Fintype α] [DecidableEq α]
    (b : B) (t : Finset α) :
    realPolynomialMass (booleanBlockPolynomial (F := F) b t) ≤
      ((Fintype.card α : ℝ) + 1) ^ Fintype.card F := by
  classical
  apply (realPolynomialMass_prod_le _ _).trans
  calc
    _ ≤ ∏ _v : F, ((Fintype.card α : ℝ) + 1) :=
      Finset.prod_le_prod (fun _ _ => realPolynomialMass_nonneg _)
        (fun v _ => booleanAffinePolynomial_mass_le b v t)
    _ = _ := by simp

theorem booleanBlockPolynomial_totalDegree_le {B F α : Type*} [Fintype F] [Fintype α] [DecidableEq α]
    (b : B) (t : Finset α) : (booleanBlockPolynomial (F := F) b t).totalDegree ≤ Fintype.card F := by
  classical
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _v : F, 1 := Finset.sum_le_sum (fun v _ => booleanAffinePolynomial_totalDegree_le b v t)
    _ = _ := by simp

theorem booleanSamplerPolynomial_mass_le {B F α : Type*}
    [Fintype B] [Fintype F] [Fintype α] [DecidableEq α] (c : B → ℝ) (s : Finset α) :
    realPolynomialMass (booleanSamplerPolynomial (F := F) c s) ≤
      (2 : ℝ) ^ s.card * ((∑ b, |c b|) * ((Fintype.card α : ℝ) + 1) ^ Fintype.card F) := by
  classical
  apply booleanCoefficient_mass_le
  intro t _
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ b, |c b| * ((Fintype.card α : ℝ) + 1) ^ Fintype.card F := by
      apply Finset.sum_le_sum
      intro b _
      exact (realPolynomialMass_C_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (booleanBlockPolynomial_mass_le b t) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem booleanSamplerPolynomial_totalDegree_le {B F α : Type*}
    [Fintype B] [Fintype F] [Fintype α] [DecidableEq α] (c : B → ℝ) (s : Finset α) :
    (booleanSamplerPolynomial (F := F) c s).totalDegree ≤ Fintype.card F := by
  classical
  apply booleanCoefficient_totalDegree_le
  intro t _
  apply MvPolynomial.totalDegree_finsetSum_le
  intro b _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa only [MvPolynomial.totalDegree_C, zero_add] using booleanBlockPolynomial_totalDegree_le b t)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BooleanAffineInput
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanAffineInput_eval {I α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → MvPolynomial I ℝ) (t : Finset α) (x : I → ℝ) :
    MvPolynomial.eval x (booleanAffineInput a t) =
      ∑ r, (booleanFeature r t : ℝ) * MvPolynomial.eval x (a r) := by
  simp only [booleanAffineInput, map_sum, map_mul, MvPolynomial.eval_C]

theorem booleanAffineInput_mass_le {I α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → MvPolynomial I ℝ) (t : Finset α) {A : ℝ}
    (ha : ∀ r, realPolynomialMass (a r) ≤ A) :
    realPolynomialMass (booleanAffineInput a t) ≤ ((Fintype.card α : ℝ) + 1) * A := by
  classical
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _r : Option α, A := by
      apply Finset.sum_le_sum
      intro r _
      apply (realPolynomialMass_C_mul_le _ _).trans
      simpa only [one_mul] using mul_le_mul (booleanFeature_abs_le_one r t)
        (ha r) (realPolynomialMass_nonneg _) zero_le_one
    _ = _ := by simp

theorem booleanAffineInput_totalDegree_le {I α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → MvPolynomial I ℝ) (t : Finset α) {e : ℕ}
    (ha : ∀ r, (a r).totalDegree ≤ e) : (booleanAffineInput a t).totalDegree ≤ e := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro r _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa only [MvPolynomial.totalDegree_C, zero_add] using ha r)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficientTail_eval {T K I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (coefficient : T → MvPolynomial I ℝ)
    (exponent : T → K →₀ ℕ) (input : K → Option α → MvPolynomial I ℝ)
    (s : Finset α) (x : I → ℝ) :
    MvPolynomial.eval x (booleanCoefficientTail terms coefficient exponent input s) =
      booleanCoefficient (fun t => ∑ n ∈ terms, MvPolynomial.eval x (coefficient n) *
        ∏ k ∈ (exponent n).support,
          (∑ r, (booleanFeature r t : ℝ) * MvPolynomial.eval x (input k r)) ^ exponent n k) s := by
  simp only [booleanCoefficientTail, booleanCoefficient_map, map_sum, map_mul,
    polynomialMonomial_eval, booleanAffineInput_eval]

theorem booleanCoefficientTail_mass_le {T K I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (coefficient : T → MvPolynomial I ℝ)
    (exponent : T → K →₀ ℕ) (input : K → Option α → MvPolynomial I ℝ)
    (s : Finset α) {h : ℕ} (hdegree : ∀ n ∈ terms, (exponent n).sum (fun _ d => d) ≤ h)
    {A : ℝ} (hbase : 1 ≤ ((Fintype.card α : ℝ) + 1) * A)
    (hinput : ∀ k r, realPolynomialMass (input k r) ≤ A) :
    realPolynomialMass (booleanCoefficientTail terms coefficient exponent input s) ≤
      (2 : ℝ) ^ s.card * ((∑ n ∈ terms, realPolynomialMass (coefficient n)) *
        (((Fintype.card α : ℝ) + 1) * A) ^ h) := by
  classical
  apply booleanCoefficient_mass_le
  intro t _
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ terms, realPolynomialMass (coefficient n) *
        (((Fintype.card α : ℝ) + 1) * A) ^ h := by
      apply Finset.sum_le_sum
      intro n hn
      apply (realPolynomialMass_mul_le _ _).trans
      apply mul_le_mul_of_nonneg_left _ (realPolynomialMass_nonneg _)
      exact (polynomialMonomial_mass_le _ _
        (fun k _ => booleanAffineInput_mass_le _ _ (hinput k))).trans
          (pow_le_pow_right₀ hbase (hdegree n hn))
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem booleanCoefficientTail_totalDegree_le {T K I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (coefficient : T → MvPolynomial I ℝ)
    (exponent : T → K →₀ ℕ) (input : K → Option α → MvPolynomial I ℝ)
    (s : Finset α) {h e δ : ℕ}
    (hdegree : ∀ n ∈ terms, (exponent n).sum (fun _ d => d) ≤ h)
    (hcoefficient : ∀ n ∈ terms, (coefficient n).totalDegree ≤ δ)
    (hinput : ∀ k r, (input k r).totalDegree ≤ e) :
    (booleanCoefficientTail terms coefficient exponent input s).totalDegree ≤ δ + h * e := by
  classical
  apply booleanCoefficient_totalDegree_le
  intro t _
  apply MvPolynomial.totalDegree_finsetSum_le
  intro n hn
  apply (MvPolynomial.totalDegree_mul _ _).trans
  apply Nat.add_le_add (hcoefficient n hn)
  exact (polynomialMonomial_totalDegree_le _ _
    (fun k _ => booleanAffineInput_totalDegree_le _ _ (hinput k))).trans
      (Nat.mul_le_mul_right _ (hdegree n hn))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem polynomialParameterPoint_some {Z I : Type*} (t : ℝ) (z : Z → ℝ) (x : I → ℝ)
    (j : Z ⊕ I) : polynomialParameterPoint t z x (some j) = Sum.elim z x j := by
  cases j <;> rfl

theorem normalizedCoefficientTail_eval {T K Z I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (weight : T → ℝ) (exponent : T → K →₀ ℕ)
    (coefficientIndex : T → Z) (inputIndex : K → Option α → Z ⊕ I)
    (t : ℝ) (z : Z → ℝ) (x : I → ℝ) (s : Finset α) :
    MvPolynomial.eval (polynomialParameterPoint t z x)
        (normalizedCoefficientTail terms weight exponent coefficientIndex inputIndex s) =
      normalizedCoefficientTailValue terms weight exponent coefficientIndex inputIndex z x s := by
  simp only [normalizedCoefficientTail, normalizedCoefficientTailValue, booleanCoefficientTail_eval,
    map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, polynomialParameterPoint_some, Sum.elim_inl]

theorem normalizedCoefficientTail_mass_le {T K Z I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (weight : T → ℝ) (exponent : T → K →₀ ℕ)
    (coefficientIndex : T → Z) (inputIndex : K → Option α → Z ⊕ I) (s : Finset α)
    {h : ℕ} (hdegree : ∀ n ∈ terms, (exponent n).sum (fun _ d => d) ≤ h) :
    realPolynomialMass (normalizedCoefficientTail terms weight exponent coefficientIndex inputIndex s) ≤
      (2 : ℝ) ^ s.card * ((∑ n ∈ terms, |weight n|) * ((Fintype.card α : ℝ) + 1) ^ h) := by
  classical
  have he := booleanCoefficientTail_mass_le terms
    (fun n => MvPolynomial.C (weight n) * MvPolynomial.X (some (.inl (coefficientIndex n))))
    exponent (fun k r => MvPolynomial.X (some (inputIndex k r))) s hdegree
    (A := 1) (by simp) (fun k r => (realPolynomialMass_X _).le)
  simp only [mul_one] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro n _
  simpa only [realPolynomialMass_X, mul_one] using realPolynomialMass_C_mul_le (weight n)
    (MvPolynomial.X (some (.inl (coefficientIndex n))) : MvPolynomial (PolynomialParameter Z I) ℝ)

theorem normalizedCoefficientTail_totalDegree_le {T K Z I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (weight : T → ℝ) (exponent : T → K →₀ ℕ)
    (coefficientIndex : T → Z) (inputIndex : K → Option α → Z ⊕ I) (s : Finset α)
    {h : ℕ} (hdegree : ∀ n ∈ terms, (exponent n).sum (fun _ d => d) ≤ h) :
    (normalizedCoefficientTail terms weight exponent coefficientIndex inputIndex s).totalDegree ≤ h + 1 := by
  have he := booleanCoefficientTail_totalDegree_le terms
    (fun n => MvPolynomial.C (weight n) * MvPolynomial.X (some (.inl (coefficientIndex n))))
    exponent (fun k r => MvPolynomial.X (some (inputIndex k r))) s hdegree
    (δ := 1) (e := 1)
    (fun n _ => (MvPolynomial.totalDegree_mul _ _).trans (by simp)) (fun k r => by simp)
  simpa only [normalizedCoefficientTail, Nat.mul_one, Nat.add_comm] using he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointBooleanPolynomialPerturbation
namespace OAI

section

namespace Erdos3

theorem scalePerturbedPolynomial_eval {Z I : Type*}
    (p : MvPolynomial I ℝ) (r : MvPolynomial (PolynomialParameter Z I) ℝ)
    (t : ℝ) (z : Z → ℝ) (x : I → ℝ) :
    MvPolynomial.eval (polynomialParameterPoint t z x) (scalePerturbedPolynomial p r) =
      MvPolynomial.eval x p + t * MvPolynomial.eval (polynomialParameterPoint t z x) r := by
  simp only [scalePerturbedPolynomial, map_add, map_mul, MvPolynomial.eval_rename, MvPolynomial.eval_X]
  rfl

theorem scalePerturbedPolynomial_mass_le {Z I : Type*}
    (p : MvPolynomial I ℝ) (r : MvPolynomial (PolynomialParameter Z I) ℝ) :
    realPolynomialMass (scalePerturbedPolynomial p r) ≤ realPolynomialMass p + realPolynomialMass r := by
  apply (realPolynomialMass_add_le _ _).trans
  apply add_le_add (realPolynomialMass_rename_le _ _)
  exact (realPolynomialMass_mul_le _ _).trans (by simp only [realPolynomialMass_X, one_mul, le_refl])

theorem scalePerturbedPolynomial_totalDegree_le {Z I : Type*}
    (p : MvPolynomial I ℝ) (r : MvPolynomial (PolynomialParameter Z I) ℝ) :
    (scalePerturbedPolynomial p r).totalDegree ≤ max p.totalDegree (1 + r.totalDegree) := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le_max (MvPolynomial.totalDegree_rename_le _ _)
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp only [MvPolynomial.totalDegree_X, le_refl])

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D α : Type*} [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)]

theorem jointBooleanPolynomial_eval (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (x : JointBlockParameter B h α → ℝ) (o : Σ d, O d) :
    MvPolynomial.eval x (jointBooleanPolynomial h c sets o) = jointBooleanSampler h c sets x o := by
  rw [jointBooleanPolynomial, MvPolynomial.eval_rename]
  rfl

theorem jointBooleanPolynomial_mass_le (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (o : Σ d, O d) :
    realPolynomialMass (jointBooleanPolynomial h c sets o) ≤
      (2 : ℝ) ^ (sets o.1 o.2).card *
        ((∑ b, |c o.1 b|) * ((Fintype.card α : ℝ) + 1) ^ h o.1) := by
  apply (realPolynomialMass_rename_le _ _).trans
  simpa only [Fintype.card_fin] using
    booleanSamplerPolynomial_mass_le (F := Fin (h o.1)) (c o.1) (sets o.1 o.2)

theorem jointBooleanPolynomial_totalDegree_le (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (o : Σ d, O d) :
    (jointBooleanPolynomial h c sets o).totalDegree ≤ h o.1 := by
  apply (MvPolynomial.totalDegree_rename_le _ _).trans
  simpa only [Fintype.card_fin] using
    booleanSamplerPolynomial_totalDegree_le (F := Fin (h o.1)) (c o.1) (sets o.1 o.2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D α Z : Type*} [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)]

theorem jointBooleanPerturbedPolynomial_eval (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α)
    (r : (Σ d, O d) → MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ)
    (t : ℝ) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) (o : Σ d, O d) :
    MvPolynomial.eval (polynomialParameterPoint t z x) (jointBooleanPerturbedPolynomial h c sets r o) =
      jointBooleanSampler h c sets x o + t * MvPolynomial.eval (polynomialParameterPoint t z x) (r o) := by
  rw [jointBooleanPerturbedPolynomial, scalePerturbedPolynomial_eval, jointBooleanPolynomial_eval]

theorem jointBooleanPerturbedPolynomial_zero [Fintype D] [Fintype Z] [∀ d, Fintype (O d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (r : (Σ d, O d) → MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ)
    (z : Z → ℝ) :
    parameterPolynomialMap (jointBooleanPerturbedPolynomial h c sets r) 0 z = jointBooleanSampler h c sets := by
  funext x o
  change MvPolynomial.eval _ _ = _
  rw [jointBooleanPerturbedPolynomial_eval, zero_mul, add_zero]

theorem jointBooleanPerturbedPolynomial_bounds
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (r : (Σ d, O d) → MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ)
    {H e : ℕ} (hh : ∀ d, h d ≤ H) (hrdeg : ∀ o, (r o).totalDegree ≤ e)
    {C R : ℝ}
    (hC : ∀ o : Σ d, O d, (2 : ℝ) ^ (sets o.1 o.2).card *
      ((∑ b, |c o.1 b|) * ((Fintype.card α : ℝ) + 1) ^ h o.1) ≤ C)
    (hrmass : ∀ o, realPolynomialMass (r o) ≤ R) :
    (∀ o i, (jointBooleanPerturbedPolynomial h c sets r o).degreeOf i ≤ max H (1 + e)) ∧
      (∀ o m, |(jointBooleanPerturbedPolynomial h c sets r o).coeff m| ≤ C + R) := by
  constructor
  · intro o i
    apply (MvPolynomial.degreeOf_le_totalDegree _ _).trans
    apply (scalePerturbedPolynomial_totalDegree_le _ _).trans
    exact max_le_max ((jointBooleanPolynomial_totalDegree_le h c sets o).trans (hh o.1))
      (Nat.add_le_add_left (hrdeg o) 1)
  · intro o m
    apply (realPolynomialMass_coeff_le _ _).trans
    apply (scalePerturbedPolynomial_mass_le _ _).trans
    exact add_le_add ((jointBooleanPolynomial_mass_le h c sets o).trans (hC o)) (hrmass o)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BooleanJetMassBudget
namespace OAI

section

namespace Erdos3

theorem booleanJetMassBudget_nonneg (q h : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    0 ≤ booleanJetMassBudget q h W := by unfold booleanJetMassBudget; positivity

theorem booleanJetMassBudget_bound {α : Type*} [Fintype α] (s : Finset α)
    {h H : ℕ} (hh : h ≤ H) {w W : ℝ} (hw : 0 ≤ w) (hW : w ≤ W) :
    (2 : ℝ) ^ s.card * (w * ((Fintype.card α : ℝ) + 1) ^ h) ≤
      booleanJetMassBudget (Fintype.card α) H W := by
  have hb : (1 : ℝ) ≤ (Fintype.card α : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  apply mul_le_mul
  · exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ s)
  · exact mul_le_mul hW (pow_le_pow_right₀ hb hh) (by positivity) (hw.trans hW)
  · positivity
  · positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientTailScaling
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D K Z α : Type*} [Fintype α] [DecidableEq α]
  {B O T : D → Type*} [∀ d, Fintype (B d)]

theorem coefficientArraySampler_polynomial [Fintype D] [Fintype Z] [∀ d, Fintype (O d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α) (t : ℝ) (z : Z → ℝ) :
    coefficientArraySampler h c sets terms weight exponent coefficientIndex inputIndex t z =
      parameterPolynomialMap (jointBooleanPerturbedPolynomial h c sets
        (jointCoefficientTail h sets terms weight exponent coefficientIndex inputIndex)) t z := by
  funext x o
  symm
  change MvPolynomial.eval _ _ = _
  rw [jointBooleanPerturbedPolynomial_eval]
  unfold jointCoefficientTail
  rw [normalizedCoefficientTail_eval]
  rfl

omit [∀ d, Fintype (B d)] in
theorem jointCoefficientTail_degree (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α) {H : ℕ}
    (hdegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ H) (o : Σ d, O d) :
    (jointCoefficientTail h sets terms weight exponent coefficientIndex inputIndex o).totalDegree ≤ H + 1 :=
  normalizedCoefficientTail_totalDegree_le _ _ _ _ _ _ (hdegree o.1)

omit [∀ d, Fintype (B d)] in
theorem jointCoefficientTail_mass (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α) {H : ℕ}
    (hdegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ H)
    {W : ℝ} (hW : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ W) (o : Σ d, O d) :
    realPolynomialMass (jointCoefficientTail h sets terms weight exponent coefficientIndex inputIndex o) ≤
      booleanJetMassBudget (Fintype.card α) H W :=
  (normalizedCoefficientTail_mass_le _ _ _ _ _ _ (hdegree o.1)).trans
    (booleanJetMassBudget_bound _ le_rfl (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (hW o.1))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem coefficientArraySampler_polynomial_bounds
    {D K Z α : Type*} [Fintype α] [DecidableEq α]
    {B O T : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α)
    {H : ℕ} (hh : ∀ d, h d ≤ H)
    (hdegree : ∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ H)
    {C W : ℝ} (hc : ∀ d, (∑ b, |c d b|) ≤ C) (hw : ∀ d, (∑ n ∈ terms d, |weight d n|) ≤ W) :
    let p := jointBooleanPerturbedPolynomial h c sets
      (jointCoefficientTail h sets terms weight exponent coefficientIndex inputIndex)
    (∀ o i, (p o).degreeOf i ≤ H + 2) ∧
      (∀ o m, |(p o).coeff m| ≤
        booleanJetMassBudget (Fintype.card α) H C + booleanJetMassBudget (Fintype.card α) H W) := by
  have hrdeg := jointCoefficientTail_degree h sets terms weight exponent coefficientIndex inputIndex hdegree
  have hrmass := jointCoefficientTail_mass h sets terms weight exponent coefficientIndex inputIndex hdegree hw
  have hc' (o : Σ d, O d) := booleanJetMassBudget_bound (sets o.1 o.2) (hh o.1)
    (Finset.sum_nonneg (fun b (_ : b ∈ (Finset.univ : Finset (B o.1))) => abs_nonneg (c o.1 b))) (hc o.1)
  have he := jointBooleanPerturbedPolynomial_bounds h c sets _ hh hrdeg hc' hrmass
  have hmax : max H (1 + (H + 1)) = H + 2 := by omega
  simpa only [hmax] using he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BooleanSamplerMeasurability
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem jointBooleanSampler_formula {D α : Type*} [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (x : JointBlockParameter B h α → ℝ) (o : Σ d, O d) :
    jointBooleanSampler h c sets x o = booleanCoefficient
      (fun t => ∑ b : B o.1, c o.1 b * ∏ v : Fin (h o.1),
        ∑ r : Option α, (booleanFeature r t : ℝ) * x ⟨o.1, (b, v, r)⟩) (sets o.1 o.2) := by
  apply booleanSamplerMap_formula

theorem jointBooleanSampler_measurable_comp {Ω D α : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] {B O : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun ω => c ω d b))
    (x : Ω → JointBlockParameter B h α → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i)) :
    Measurable (fun ω => jointBooleanSampler h (c ω) sets (x ω)) := by
  apply measurable_pi_iff.mpr
  intro o
  simp_rw [jointBooleanSampler_formula, booleanCoefficient]
  fun_prop

theorem normalizedCoefficientTailValue_measurable_comp {Ω T K Z I α : Type*}
    [MeasurableSpace Ω] [Fintype Z] [Fintype I] [Fintype α] [DecidableEq α]
    (terms : Finset T) (weight : T → ℝ) (exponent : T → K →₀ ℕ)
    (coefficientIndex : T → Z) (inputIndex : K → Option α → Z ⊕ I) (s : Finset α)
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun ω => z ω j))
    (x : Ω → I → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i)) :
    Measurable (fun ω => normalizedCoefficientTailValue terms weight exponent coefficientIndex inputIndex
      (z ω) (x ω) s) := by
  have he : (fun ω => normalizedCoefficientTailValue terms weight exponent coefficientIndex inputIndex
      (z ω) (x ω) s) = fun ω => MvPolynomial.eval (polynomialParameterPoint 0 (z ω) (x ω))
        (normalizedCoefficientTail terms weight exponent coefficientIndex inputIndex s) :=
    funext (fun ω => (normalizedCoefficientTail_eval _ _ _ _ _ 0 _ _ _).symm)
  rw [he]
  apply (mvPolynomial_contDiff_eval _).continuous.measurable.comp
  apply measurable_pi_iff.mpr
  intro j
  rcases j with _ | (j | i)
  · exact measurable_const
  · exact hz j
  · exact hx i

theorem coefficientArraySampler_measurable_comp {Ω D K Z α : Type*}
    [MeasurableSpace Ω] [Fintype D] [Fintype Z] [Fintype α] [DecidableEq α]
    {B O T : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α) (t : ℝ)
    (c : Ω → ∀ d, B d → ℝ) (hc : ∀ d b, Measurable (fun ω => c ω d b))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun ω => z ω j))
    (x : Ω → JointBlockParameter B h α → ℝ) (hx : ∀ i, Measurable (fun ω => x ω i)) :
    Measurable (fun ω => coefficientArraySampler h (c ω) sets terms weight exponent
      coefficientIndex inputIndex t (z ω) (x ω)) := by
  apply measurable_pi_iff.mpr
  intro o
  exact ((measurable_pi_apply o).comp (jointBooleanSampler_measurable_comp h sets c hc x hx)).add
    (measurable_const.mul (normalizedCoefficientTailValue_measurable_comp (terms o.1) (weight o.1)
      (exponent o.1) (coefficientIndex o.1) inputIndex (sets o.1 o.2) z hz x hx))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RawCanonicalNormalizedPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_coefficient_split {K : Type*} [DecidableEq K] (p : MvPolynomial K ℝ)
    (selected : Finset (K →₀ ℕ)) :
    p = (∑ n ∈ selected, MvPolynomial.monomial n (p.coeff n)) +
      ∑ n ∈ p.support \ selected, MvPolynomial.monomial n (p.coeff n) := by
  classical
  ext n
  by_cases hs : n ∈ selected
  · simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hs]
  · by_cases hp : n ∈ p.support
    · simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hs, hp]
    · have hc := MvPolynomial.notMem_support_iff.mp hp
      simp [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hs, hp, hc]

theorem polynomial_coefficient_split_principal {K J : Type*} [Fintype J]
    (p : MvPolynomial K ℝ) (principal : J → K →₀ ℕ)
    (hinj : Function.Injective principal) (hzero : ∀ j, principal j ≠ 0) :
    p = MvPolynomial.C (p.coeff 0) +
      (∑ j, MvPolynomial.monomial (principal j) (p.coeff (principal j))) +
      ∑ n ∈ nonprincipalSupport p principal, MvPolynomial.monomial n (p.coeff n) := by
  classical
  have hnot : (0 : K →₀ ℕ) ∉ Finset.univ.image principal := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hzero
  have he := polynomial_coefficient_split p (insert 0 (Finset.univ.image principal))
  rw [Finset.sum_insert hnot, Finset.sum_image (fun i _ j _ hij => hinj hij)] at he
  exact he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FixedSupportRawArray
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem monomialArrayPolynomial_support_subset {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) :
    ∀ ⦃m⦄, m ∈ (monomialArrayPolynomial e a).support → m ∈ Set.range e := by
  intro m hm
  by_contra hn
  have hz := monomialArrayPolynomial_coeff_zero_of_not_mem e a m
    (fun j hj => hn ⟨j, hj⟩)
  exact (MvPolynomial.mem_support_iff.mp hm) hz

theorem polynomial_coefficient_split_principal_on {K J : Type*} [Fintype J]
    (p : MvPolynomial K ℝ) (S : Finset (K →₀ ℕ)) (hS : p.support ⊆ S)
    (principal : J → K →₀ ℕ) (hinj : Function.Injective principal) (hzero : ∀ j, principal j ≠ 0) :
    p = MvPolynomial.C (p.coeff 0) +
      (∑ j, MvPolynomial.monomial (principal j) (p.coeff (principal j))) +
      ∑ n ∈ fixedNonprincipalExponents S principal, MvPolynomial.monomial n (p.coeff n) := by
  classical
  unfold fixedNonprincipalExponents
  have hsub : nonprincipalSupport p principal ⊆ S \ insert 0 (Finset.univ.image principal) :=
    Finset.sdiff_subset_sdiff hS (Finset.Subset.refl _)
  have hsum : (∑ n ∈ nonprincipalSupport p principal, MvPolynomial.monomial n (p.coeff n)) =
      ∑ n ∈ S \ insert 0 (Finset.univ.image principal), MvPolynomial.monomial n (p.coeff n) := by
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hns : n ∉ p.support := by
      intro hp
      exact hnot (Finset.mem_sdiff.mpr ⟨hp, (Finset.mem_sdiff.mp hn).2⟩)
    simp only [MvPolynomial.notMem_support_iff.mp hns, map_zero]
  rw [← hsum]
  exact polynomial_coefficient_split_principal p principal hinj hzero

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

theorem affineProductProfile_compact {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : HasCompactSupport (affineProductProfile c w) :=
  tensorCutoffWeight_compact (fun i => affineProbabilityProfile (c i) (w i))
    (fun i => affineProbabilityProfile_compact (c i) (hw i))

theorem affineProductProfile_integrable {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : Integrable (affineProductProfile c w) :=
  (affineProductProfile_contDiff c w).continuous.integrable_of_hasCompactSupport
    (affineProductProfile_compact c w hw)

theorem affineProductProfile_integral {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : (∫ x, affineProductProfile c w x) = 1 := by
  change (∫ x, tensorCutoffWeight (fun i => affineProbabilityProfile (c i) (w i)) x) = 1
  rw [tensorCutoffWeight_integral]
  simp only [affineProbabilityProfile_integral _ (hw _), Finset.prod_const_one]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem affineProbabilityProfile_integral_test (c : ℝ) {w : ℝ} (hw : 0 < w) (φ : ℝ → ℝ) :
    (∫ x, affineProbabilityProfile c w x * φ x) =
      ∫ y, smoothProbabilityProfile y * φ (c + w*y) := by
  let g := fun y => smoothProbabilityProfile y * φ (c+w*y)
  have he (x : ℝ) : affineProbabilityProfile c w x * φ x = w⁻¹ * g ((x-c)/w) := by
    have hx : c + w*((x-c)/w) = x := by field_simp [hw.ne']; ring
    simp only [affineProbabilityProfile, g, hx]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_sub_right_eq_self (fun x => g (x/w)) c,
    Measure.integral_comp_div, smul_eq_mul, abs_of_pos hw, ← mul_assoc,
    inv_mul_cancel₀ hw.ne', one_mul]

theorem affineProbabilityProfile_law (c : ℝ) {w : ℝ} (hw : 0 < w) :
    (realDensityMeasure volume smoothProbabilityProfile).map (fun y => c + w*y) =
      realDensityMeasure volume (affineProbabilityProfile c w) := by
  have hψ : Integrable smoothProbabilityProfile :=
    smoothProbabilityProfile_contDiff.continuous.integrable_of_hasCompactSupport smoothProbabilityProfile_compact
  let : IsFiniteMeasure (realDensityMeasure volume smoothProbabilityProfile) :=
    realDensityMeasure_finite _ _ hψ (fun y => (smoothProbabilityProfile_range y).1)
  let : IsFiniteMeasure (realDensityMeasure volume (affineProbabilityProfile c w)) :=
    realDensityMeasure_finite _ _ (affineProbabilityProfile_integrable c hw) (affineProbabilityProfile_nonneg c hw)
  have hmap : Measurable (fun y : ℝ => c+w*y) := by fun_prop
  apply finiteMeasure_eq_of_integrals
  intro φ hφ
  rw [integral_map hmap.aemeasurable hφ.aestronglyMeasurable,
    realDensityMeasure_integral volume smoothProbabilityProfile
      smoothProbabilityProfile_contDiff.continuous.measurable (fun y => (smoothProbabilityProfile_range y).1),
    realDensityMeasure_integral volume (affineProbabilityProfile c w)
      (affineProbabilityProfile_contDiff c w).continuous.measurable (affineProbabilityProfile_nonneg c hw)]
  exact (affineProbabilityProfile_integral_test c hw φ).symm

theorem affineProductProfile_law {I : Type*} [Fintype I]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) :
    (realDensityMeasure volume (smoothProductProfile I)).map (fun y i => c i + w i * y i) =
      realDensityMeasure volume (affineProductProfile c w) := by
  have hψ : Integrable smoothProbabilityProfile :=
    smoothProbabilityProfile_contDiff.continuous.integrable_of_hasCompactSupport smoothProbabilityProfile_compact
  let : IsFiniteMeasure (realDensityMeasure volume smoothProbabilityProfile) :=
    realDensityMeasure_finite _ _ hψ (fun y => (smoothProbabilityProfile_range y).1)
  have hsrc := realDensityMeasure_pi (fun _ : I => (volume : Measure ℝ))
    (fun _ => smoothProbabilityProfile) (fun _ => hψ) (fun _ y => (smoothProbabilityProfile_range y).1)
  have hdst := realDensityMeasure_pi (fun _ : I => (volume : Measure ℝ))
    (fun i => affineProbabilityProfile (c i) (w i))
    (fun i => affineProbabilityProfile_integrable (c i) (hw i))
    (fun i => affineProbabilityProfile_nonneg (c i) (hw i))
  change (Measure.pi (fun _ : I => realDensityMeasure volume smoothProbabilityProfile)) =
    realDensityMeasure volume (smoothProductProfile I) at hsrc
  change (Measure.pi (fun i : I => realDensityMeasure volume (affineProbabilityProfile (c i) (w i)))) =
    realDensityMeasure volume (affineProductProfile c w) at hdst
  rw [← hsrc, Measure.pi_map_pi (fun i =>
    (show Measurable (fun y : ℝ => c i + w i * y) by fun_prop).aemeasurable)]
  simp_rw [affineProbabilityProfile_law _ (hw _)]
  exact hdst

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitCoefficientSourceMarginal
namespace OAI

section

namespace Erdos3

open MeasureTheory

instance unitCoefficientSource_probability (I : Type*) [Fintype I] :
    IsProbabilityMeasure (unitCoefficientSource I) :=
  realDensityMeasure_probability volume _
    ((smoothProductProfile_contDiff I).continuous.integrable_of_hasCompactSupport (smoothProductProfile_compact I))
    (fun r => (smoothProductProfile_range I r).1) (smoothProductProfile_integral I)

theorem unitCoefficientSource_affine_law {I : Type*} [Fintype I]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) :
    (unitCoefficientSource I).map (fun r i => c i+w i*r i) =
      realDensityMeasure volume (affineProductProfile c w) :=
  affineProductProfile_law c w hw

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RegularizedSigmaDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem affineProductProfile_measurable_center {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (c x : Ω → I → ℝ) (w : I → ℝ)
    (hc : ∀ i, Measurable (fun a => c a i)) (hx : ∀ i, Measurable (fun a => x a i)) :
    Measurable (fun a => affineProductProfile (c a) w (x a)) := by
  unfold affineProductProfile affineProbabilityProfile
  apply Finset.measurable_prod
  intro i _
  exact measurable_const.mul (smoothProbabilityProfile_contDiff.continuous.measurable.comp
    (((hx i).sub (hc i)).div_const (w i)))

theorem regularizedImageMap_measurable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (δ : ℝ≥0) (U : Ω → I → ℝ) (hU : Measurable U) : Measurable (regularizedImageMap δ U) :=
  (hU.comp measurable_fst).add (measurable_snd.const_smul (δ : ℝ))

theorem regularizedImageDensity_joint_measurable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (U : Ω → I → ℝ) (hU : Measurable U) (δ : ℝ≥0) :
    Measurable (fun p : Ω × (I → ℝ) => affineProductProfile (U p.1) (fun _ => (δ : ℝ)) p.2) :=
  affineProductProfile_measurable_center _ _ _
    (fun i => (measurable_pi_apply i).comp (hU.comp measurable_fst))
    (fun i => (measurable_pi_apply i).comp measurable_snd)

theorem regularizedImageDensity_measurable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [SFinite μ] (U : Ω → I → ℝ) (hU : Measurable U) (δ : ℝ≥0) :
    Measurable (regularizedImageDensity μ U δ) :=
  (regularizedImageDensity_joint_measurable U hU δ).stronglyMeasurable.integral_prod_left'.measurable

theorem regularizedImageDensity_probability {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    (∀ x, 0 ≤ regularizedImageDensity μ U δ x) ∧ Integrable (regularizedImageDensity μ U δ) ∧
      (∫ x, regularizedImageDensity μ U δ x) = 1 := by
  apply densityMixture_probability_density μ volume _ (regularizedImageDensity_joint_measurable U hU δ)
  exact Filter.Eventually.of_forall (fun a =>
    ⟨affineProductProfile_nonneg (U a) _ (fun _ => hδ),
      affineProductProfile_integrable (U a) _ (fun _ => hδ),
      affineProductProfile_integral (U a) _ (fun _ => hδ)⟩)

theorem regularizedImageDensity_image_law {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    (μ.prod (unitCoefficientSource I)).map (regularizedImageMap δ U) =
      realDensityMeasure volume (regularizedImageDensity μ U δ) := by
  apply densityMixture_image_law μ (unitCoefficientSource I) volume _
    (regularizedImageMap_measurable δ U hU)
    (fun a => affineProductProfile (U a) (fun _ => (δ : ℝ)))
    (regularizedImageDensity_joint_measurable U hU δ)
  · intro a
    exact ⟨affineProductProfile_nonneg (U a) _ (fun _ => hδ),
      affineProductProfile_integrable (U a) _ (fun _ => hδ),
      affineProductProfile_integral (U a) _ (fun _ => hδ)⟩
  · intro a
    exact unitCoefficientSource_affine_law (U a) (fun _ => (δ : ℝ)) (fun _ => hδ)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem conditionalRegularizedDensity_measurable {W X I : Type*}
    [MeasurableSpace W] [MeasurableSpace X] [Fintype I]
    (ν : Measure X) [SFinite ν] (U : W × X → I → ℝ) (hU : Measurable U) (δ : ℝ≥0) :
    Measurable (fun p : W × (I → ℝ) => regularizedImageDensity ν (fun x => U (p.1, x)) δ p.2) := by
  have hm := affineProductProfile_measurable_center
    (fun p : (W × (I → ℝ)) × X => U (p.1.1, p.2)) (fun p => p.1.2) (fun _ => (δ : ℝ))
    (fun i => (measurable_pi_apply i).comp (hU.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
    (fun i => (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

theorem conditionalRegularizedDensity_comparison {W X I : Type*}
    [MeasurableSpace W] [MeasurableSpace X] [Fintype I]
    (μ : Measure W) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (U V : W × X → I → ℝ) (hU : Measurable U) (hV : Measurable V) (δ : ℝ≥0) (hδ : 0 < δ) {ε : ℝ}
    (herr : ∀ᵐ w ∂μ, ∀ f : (I → ℝ) → ℝ, Measurable f → (∀ y, ‖f y‖ ≤ 1) →
      |(∫ y, regularizedImageDensity ν (fun x => U (w, x)) δ y*f y)-
        mappedTest ν (fun x => V (w, x)) f| ≤ ε)
    (φ : W × (I → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ p, ‖φ p‖ ≤ 1) :
    |(∫ p, regularizedImageDensity ν (fun x => U (p.1, x)) δ p.2*φ p ∂μ.prod volume) -
      ∫ p, φ (p.1, V p) ∂μ.prod ν| ≤ ε := by
  have hD := conditionalRegularizedDensity_measurable ν U hU δ
  have hp (w) := regularizedImageDensity_probability ν (fun x => U (w, x))
    (hU.comp (measurable_const.prodMk measurable_id)) δ hδ
  have hj := densityMixture_joint_integrable μ volume
    (fun w => regularizedImageDensity ν (fun x => U (w, x)) δ) hD (Filter.Eventually.of_forall hp)
  have hd : Integrable (fun p : W × (I → ℝ) =>
      regularizedImageDensity ν (fun x => U (p.1, x)) δ p.2*φ p) (μ.prod volume) :=
    hj.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hi := mappedTest_integrable (μ.prod ν) (fun p => (p.1, V p))
    (measurable_fst.prodMk hV) φ hφ hbound
  rw [integral_prod _ hd, integral_prod _ hi,
    ← integral_sub hd.integral_prod_left hi.integral_prod_left]
  have hb : ∀ᵐ w ∂μ, ‖(∫ y, regularizedImageDensity ν (fun x => U (w, x)) δ y*φ (w, y))-
      ∫ x, φ (w, V (w, x)) ∂ν‖ ≤ ε := by
    filter_upwards [herr] with w hw
    exact hw (fun y => φ (w, y)) (hφ.comp (measurable_const.prodMk measurable_id)) (fun y => hbound (w, y))
  have he := norm_integral_le_of_norm_le (integrable_const ε (μ := μ)) hb
  simpa only [Real.norm_eq_abs, integral_const, probReal_univ, one_smul] using he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanRegularization
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem regularizedImageDensity_test_integral {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) (φ : (I → ℝ) → ℝ) (hφ : Measurable φ) :
    (∫ x, regularizedImageDensity μ U δ x*φ x) =
      mappedTest (μ.prod (unitCoefficientSource I)) (regularizedImageMap δ U) φ :=
  (mappedTest_eq_density (μ.prod (unitCoefficientSource I)) volume (regularizedImageMap δ U)
    (regularizedImageMap_measurable δ U hU) (regularizedImageDensity μ U δ)
    (regularizedImageDensity_measurable μ U hU δ) (regularizedImageDensity_probability μ U hU δ hδ).1
    (regularizedImageDensity_image_law μ U hU δ hδ) φ hφ).symm

theorem regularizedImageDensity_translate_test {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) (b : I → ℝ) (φ : (I → ℝ) → ℝ) (hφ : Measurable φ) :
    (∫ x, regularizedImageDensity μ (fun a => b+U a) δ x*φ x) =
      ∫ x, regularizedImageDensity μ U δ x*φ (b+x) := by
  rw [regularizedImageDensity_test_integral μ (fun a => b+U a) (measurable_const.add hU) δ hδ φ hφ,
    regularizedImageDensity_test_integral μ U hU δ hδ (fun x => φ (b+x))
      (hφ.comp (measurable_const.add measurable_id))]
  simp only [mappedTest, regularizedImageMap, add_assoc]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConstantJetPostprocessing
namespace OAI

section

namespace Erdos3

theorem booleanConstantJet_measurable_comp {Ω D α : Type*} [MeasurableSpace Ω] [DecidableEq α]
    {O : D → Type*} (sets : ∀ d, O d → Finset α)
    (constant : Ω → D → ℝ) (hc : ∀ d, Measurable (fun a => constant a d)) :
    Measurable (fun a => booleanConstantJet sets (constant a)) := by
  apply measurable_pi_iff.mpr
  intro o
  by_cases hs : sets o.1 o.2 = ∅
  · simpa only [booleanConstantJet, hs, ite_true] using hc o.1
  · simpa only [booleanConstantJet, hs, ite_false] using
      (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NonprincipalDilation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mem_nonprincipalCoefficientSlots {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (j : C) :
    j ∈ nonprincipalCoefficientSlots e principal ↔
      e j ∈ fixedNonprincipalExponents (monomialExponentSet e) principal := by
  classical
  simp only [nonprincipalCoefficientSlots, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_monomialExponentSet {C K : Type*} [Fintype C]
    (e : C → K →₀ ℕ) (m : K →₀ ℕ) :
    m ∈ monomialExponentSet e ↔ ∃ j, e j = m := by
  classical
  simp only [monomialExponentSet, Finset.mem_image, Finset.mem_univ, true_and]

theorem mem_fixedNonprincipalExponents {B K : Type*} [Fintype B]
    (S : Finset (K →₀ ℕ)) (principal : B → K →₀ ℕ) (m : K →₀ ℕ) :
    m ∈ fixedNonprincipalExponents S principal ↔
      m ∈ S ∧ m ≠ 0 ∧ ∀ b, principal b ≠ m := by
  classical
  simp [fixedNonprincipalExponents]

theorem nonprincipalCoefficientSlots_image {C B K : Type*} [Fintype C] [Fintype B] [DecidableEq (K →₀ ℕ)]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) :
    (nonprincipalCoefficientSlots e principal).image e =
      fixedNonprincipalExponents (monomialExponentSet e) principal := by
  classical
  ext m
  constructor
  · intro hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    exact (mem_nonprincipalCoefficientSlots e principal j).mp hj
  · intro hm
    have hs : m ∈ monomialExponentSet e :=
      ((mem_fixedNonprincipalExponents _ principal m).mp hm).1
    obtain ⟨j, rfl⟩ := (mem_monomialExponentSet e m).mp hs
    have hj := (mem_nonprincipalCoefficientSlots e principal j).mpr hm
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩

theorem nonprincipalCoefficientSlots_sum {C B K R : Type*} [Fintype C] [Fintype B] [AddCommMonoid R]
    (e : C → K →₀ ℕ) (he : Function.Injective e) (principal : B → K →₀ ℕ) (f : (K →₀ ℕ) → R) :
    (∑ j ∈ nonprincipalCoefficientSlots e principal, f (e j)) =
      ∑ m ∈ fixedNonprincipalExponents (monomialExponentSet e) principal, f m := by
  classical
  rw [← nonprincipalCoefficientSlots_image e principal, Finset.sum_image (fun _ _ _ _ h => he h)]

theorem nonprincipalCoefficientSlots_not_principal {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (j : C) (b : B) (hj : e j = principal b) :
    j ∉ nonprincipalCoefficientSlots e principal := by
  classical
  intro hm
  have hn := ((mem_fixedNonprincipalExponents _ principal (e j)).mp
    ((mem_nonprincipalCoefficientSlots e principal j).mp hm)).2.2
  exact hn b hj.symm

theorem nonprincipalCoefficientSlots_not_zero {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (j : C) (hj : e j = 0) :
    j ∉ nonprincipalCoefficientSlots e principal := by
  classical
  intro hm
  have hn := ((mem_fixedNonprincipalExponents _ principal (e j)).mp
    ((mem_nonprincipalCoefficientSlots e principal j).mp hm)).2.1
  exact hn hj

end Erdos3

end

section

namespace Erdos3

theorem nonprincipalDilation_principal {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (j : C) (b : B)
    (hj : e j = principal b) : nonprincipalDilation e principal t j = 1 := by
  classical
  simp only [nonprincipalDilation, nonprincipalCoefficientSlots_not_principal e principal j b hj, ite_false]

theorem nonprincipalDilation_zero {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (j : C)
    (hj : e j = 0) : nonprincipalDilation e principal t j = 1 := by
  classical
  simp only [nonprincipalDilation, nonprincipalCoefficientSlots_not_zero e principal j hj, ite_false]

theorem nonprincipalDilation_mem {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (j : C)
    (hj : j ∈ nonprincipalCoefficientSlots e principal) : nonprincipalDilation e principal t j = t := by
  classical
  simp only [nonprincipalDilation, hj, ite_true]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SmallAffinePolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem monomialArrayPolynomial_indexed_split {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (he : Function.Injective e)
    (principal : B → K →₀ ℕ) (hp : Function.Injective principal) (hp0 : ∀ b, principal b ≠ 0)
    (index : B → C) (hindex : ∀ b, e (index b) = principal b) (a : C → ℝ) :
    monomialArrayPolynomial e a = MvPolynomial.C ((monomialArrayPolynomial e a).coeff 0) +
      (∑ b, MvPolynomial.monomial (principal b) (a (index b))) +
      ∑ j ∈ nonprincipalCoefficientSlots e principal, MvPolynomial.monomial (e j) (a j) := by
  classical
  have hS : (monomialArrayPolynomial e a).support ⊆ monomialExponentSet e := by
    intro m hm
    obtain ⟨j, rfl⟩ := monomialArrayPolynomial_support_subset e a hm
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hs := polynomial_coefficient_split_principal_on (monomialArrayPolynomial e a)
    (monomialExponentSet e) hS principal hp hp0
  rw [← nonprincipalCoefficientSlots_sum e he principal] at hs
  have hc (b) : (monomialArrayPolynomial e a).coeff (principal b) = a (index b) := by
    rw [← hindex b]
    exact monomialArrayPolynomial_coeff e he a (index b)
  simpa only [hc, monomialArrayPolynomial_coeff e he] using hs

theorem nonprincipalDilation_constant_coeff {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (a : C → ℝ) :
    (monomialArrayPolynomial e (fun j => nonprincipalDilation e principal t j*a j)).coeff 0 =
      (monomialArrayPolynomial e a).coeff 0 := by
  classical
  simp only [monomialArrayPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : e j = 0
  · simp only [hj, ite_true, nonprincipalDilation_zero e principal t j hj, one_mul]
  · simp only [hj, ite_false]

theorem monomialArrayPolynomial_dilated_split {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (he : Function.Injective e)
    (principal : B → K →₀ ℕ) (hp : Function.Injective principal) (hp0 : ∀ b, principal b ≠ 0)
    (index : B → C) (hindex : ∀ b, e (index b) = principal b) (t : ℝ) (a : C → ℝ) :
    monomialArrayPolynomial e (fun j => nonprincipalDilation e principal t j*a j) =
      MvPolynomial.C ((monomialArrayPolynomial e a).coeff 0) +
      (∑ b, MvPolynomial.monomial (principal b) (a (index b))) +
      ∑ j ∈ nonprincipalCoefficientSlots e principal, MvPolynomial.monomial (e j) (t*a j) := by
  have hs := monomialArrayPolynomial_indexed_split e he principal hp hp0 index hindex
    (fun j => nonprincipalDilation e principal t j*a j)
  rw [nonprincipalDilation_constant_coeff] at hs
  have hpv (b) : nonprincipalDilation e principal t (index b)*a (index b) = a (index b) := by
    rw [nonprincipalDilation_principal e principal t (index b) b (hindex b), one_mul]
  simp_rw [hpv] at hs
  rw [hs]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [nonprincipalDilation_mem e principal t j hj]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem monomialArrayPolynomial_affine_dilated_split {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (he : Function.Injective e)
    (principal : B → K →₀ ℕ) (hp : Function.Injective principal) (hp0 : ∀ b, principal b ≠ 0)
    (index : B → C) (hindex : ∀ b, e (index b) = principal b) (t : ℝ) (c w r : C → ℝ) :
    monomialArrayPolynomial e (fun j => nonprincipalDilation e principal t j*c j +
      (nonprincipalDilation e principal t j*w j)*r j) =
      MvPolynomial.C ((monomialArrayPolynomial e (fun j => c j+w j*r j)).coeff 0) +
      (∑ b, MvPolynomial.monomial (principal b) (c (index b)+w (index b)*r (index b))) +
      ∑ j ∈ nonprincipalCoefficientSlots e principal, MvPolynomial.monomial (e j) (t*(c j+w j*r j)) := by
  have ha : (fun j => nonprincipalDilation e principal t j*c j +
      (nonprincipalDilation e principal t j*w j)*r j) =
      (fun j => nonprincipalDilation e principal t j*(c j+w j*r j)) := by
    funext j
    ring
  rw [ha]
  exact monomialArrayPolynomial_dilated_split e he principal hp hp0 index hindex t _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveProfileNoise
namespace OAI

section

namespace Erdos3

theorem coefficientProfileCenter_mul {J : Type*} (P : Finset J) (R γ : ℝ) (j : J) :
    coefficientProfileCenter P (R * γ) j = R * coefficientProfileCenter P γ j := by
  classical
  unfold coefficientProfileCenter
  split_ifs <;> ring

theorem coefficientProfileWidth_mul {J : Type*} (P : Finset J) (j₀ : J)
    (R ρ γ ε : ℝ) (j : J) :
    coefficientProfileWidth P j₀ (R * ρ) (R * γ) (R * ε) j =
      R * coefficientProfileWidth P j₀ ρ γ ε j := by
  classical
  unfold coefficientProfileWidth
  split_ifs <;> ring

theorem principalProfileSize_mul (R S : ℝ) (b : ℕ) :
    principalProfileSize (R * S) b = R * principalProfileSize S b := by
  unfold principalProfileSize
  ring

theorem tailProfileSize_mul (R S σ : ℝ) (b : ℕ) :
    tailProfileSize (R * S) σ b = R * tailProfileSize S σ b := by
  unfold tailProfileSize
  ring

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {D G : Type*} [Fintype D] [Fintype G] {B : D → Type*}
variable [∀ d, Fintype (B d)] (h : D → ℕ) (d : D)

theorem bounded_mem_nonprincipalCoefficientSlots
    (e : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)) :
    e ∈ nonprincipalCoefficientSlots Subtype.val (canonicalPrincipalExponent h d) ↔
      e ≠ constantCoefficientSlot _ _ ∧ e ∉ principalCoefficientSlots h d := by
  classical
  rw [mem_nonprincipalCoefficientSlots, mem_fixedNonprincipalExponents]
  have hz : e.val = 0 ↔ e = constantCoefficientSlot _ _ := by
    constructor
    · intro he
      exact Subtype.ext he
    · intro he
      exact congrArg Subtype.val he
  have hp : (∃ b, canonicalPrincipalExponent h d b = e.val) ↔
      e ∈ principalCoefficientSlots h d := by
    rw [mem_principalCoefficientSlots]
    constructor <;> rintro ⟨b, hb⟩
    · exact ⟨b, Subtype.ext hb⟩
    · exact ⟨b, congrArg Subtype.val hb⟩
  have hm : e.val ∈ monomialExponentSet
      (Subtype.val : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → _) :=
    (mem_monomialExponentSet _ _).mpr ⟨e, rfl⟩
  simp only [hm, true_and, ← not_exists, hp]
  exact and_congr (not_congr hz) Iff.rfl

theorem boundedProfileCenter_dilation (γ t : ℝ)
    (e : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)) :
    coefficientProfileCenter (principalCoefficientSlots h d) γ e =
      nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) t e *
        coefficientProfileCenter (principalCoefficientSlots h d) γ e := by
  classical
  by_cases hp : e ∈ principalCoefficientSlots h d
  · obtain ⟨b, hb⟩ := (mem_principalCoefficientSlots h d e).mp hp
    rw [nonprincipalDilation_principal Subtype.val (canonicalPrincipalExponent h d)
      t e b (congrArg Subtype.val hb.symm), one_mul]
  · simp only [coefficientProfileCenter, hp, ite_false, mul_zero]

theorem boundedProfileWidth_dilation (ρ γ ε t : ℝ)
    (e : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)) :
    coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
        ρ γ (t * ε) e =
      nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) t e *
        coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
          ρ γ ε e := by
  classical
  by_cases hz : e = constantCoefficientSlot _ _
  · rw [nonprincipalDilation_zero Subtype.val (canonicalPrincipalExponent h d)
      t e (congrArg Subtype.val hz)]
    simp only [coefficientProfileWidth, hz, ite_true, one_mul]
  · by_cases hp : e ∈ principalCoefficientSlots h d
    · obtain ⟨b, hb⟩ := (mem_principalCoefficientSlots h d e).mp hp
      rw [nonprincipalDilation_principal Subtype.val (canonicalPrincipalExponent h d)
        t e b (congrArg Subtype.val hb.symm), one_mul]
      simp only [coefficientProfileWidth, hz, hp, ite_false, ite_true]
    · rw [nonprincipalDilation_mem Subtype.val (canonicalPrincipalExponent h d) t e
        ((bounded_mem_nonprincipalCoefficientSlots h d e).mpr ⟨hz, hp⟩)]
      simp only [coefficientProfileWidth, hz, hp, ite_false]

theorem boundedProfile_polynomial_split (hd : 0 < h d) (ρ γ ε t : ℝ)
    (r : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → ℝ) :
    monomialArrayPolynomial Subtype.val (fun e =>
      coefficientProfileCenter (principalCoefficientSlots h d) γ e +
        coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
          ρ γ (t * ε) e * r e) =
      MvPolynomial.C (ρ * r (constantCoefficientSlot _ _)) +
      (∑ b, MvPolynomial.monomial (canonicalPrincipalExponent h d b)
        (3 * γ / 2 + γ / 2 * r (principalCoefficientSlot h d b))) +
      ∑ e ∈ nonprincipalCoefficientSlots
          (Subtype.val : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → _)
          (canonicalPrincipalExponent h d),
        MvPolynomial.monomial e.val (t * (ε * r e)) := by
  classical
  let c := coefficientProfileCenter (principalCoefficientSlots (G := G) (B := B) h d) γ
  let w := coefficientProfileWidth (principalCoefficientSlots (G := G) (B := B) h d)
    (constantCoefficientSlot _ _) ρ γ ε
  have heq : (fun e => c e + coefficientProfileWidth (principalCoefficientSlots h d)
      (constantCoefficientSlot _ _) ρ γ (t * ε) e * r e) =
      (fun e => nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) t e * c e +
        (nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) t e * w e) * r e) := by
    funext e
    rw [boundedProfileWidth_dilation]
    congr 1
    exact boundedProfileCenter_dilation h d γ t e
  rw [heq, monomialArrayPolynomial_affine_dilated_split Subtype.val Subtype.val_injective
    (canonicalPrincipalExponent h d) (canonicalPrincipalExponent_injective h d hd)
    (canonicalPrincipalExponent_ne_zero h d hd) (principalCoefficientSlot h d) (fun _ => rfl)]
  have hc : (monomialArrayPolynomial Subtype.val (fun e => c e + w e * r e)).coeff 0 =
      ρ * r (constantCoefficientSlot _ _) := by
    rw [show (0 : SamplerTupleIndex G B h →₀ ℕ) =
      (constantCoefficientSlot (SamplerTupleIndex G B h) (h d)).val from rfl,
      monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]
    simp only [c, w, coefficientProfileCenter, coefficientProfileWidth,
      constantCoefficientSlot_not_principal h d hd, ite_false, ite_true, zero_add]
  rw [hc]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro b _
    have hp : principalCoefficientSlot h d b ∈ principalCoefficientSlots (G := G) h d :=
      (mem_principalCoefficientSlots h d _).mpr ⟨b, rfl⟩
    have hz : principalCoefficientSlot (G := G) h d b ≠ constantCoefficientSlot _ _ := by
      intro hz
      exact constantCoefficientSlot_not_principal h d hd (hz ▸ hp)
    simp only [c, w, coefficientProfileCenter, coefficientProfileWidth, hp, hz, ite_true, ite_false]
  · apply Finset.sum_congr rfl
    intro e he
    obtain ⟨hz, hp⟩ := (bounded_mem_nonprincipalCoefficientSlots h d e).mp he
    simp only [c, w, coefficientProfileCenter, coefficientProfileWidth, hz, hp, ite_false, zero_add]

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem partitionedProfileInput_principal {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}
    (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
    (d : {d // ¬P d}) (b : B d.val) (v : Fin (h d.val)) (a : Option α) :
    partitionedProfileInput (B := B) (h := h) P extra (.inr ⟨d.val, b, v⟩) a =
      .inr ⟨d, b, v, a⟩ := by
  simp [partitionedProfileInput, partitionedPrincipalInput, d.property]

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
variable {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)

theorem partitionedProfileJet_eq (hh : ∀ d, 0 < h d) (ρ γ ε : D → ℝ) (t : ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    partitionedProfileJet h P extra sets ρ γ ε t y x =
      booleanConstantJet sets (partitionedProfileConstant h P ρ y) +
      coefficientArraySampler (fun d : {d // ¬P d} => h d.val)
        (partitionedProfilePrincipal h P γ y) sets (partitionedProfileTerms (G := G) h P)
        (fun d _ => ε d.val) (fun _ e => e.val) (fun d e => .inr ⟨d.val, e⟩)
        (partitionedProfileInput P extra) t y x := by
  classical
  funext o
  let V := normalizedCubeTuple (partitionedProfileInput P extra) y x
  have hv (s : Finset α) : MvPolynomial.eval (V s)
      (monomialArrayPolynomial Subtype.val (fun e : SamplerCoefficientSlot G B h o.1.val =>
        coefficientProfileCenter (principalCoefficientSlots h o.1.val) (γ o.1.val) e +
          coefficientProfileWidth (principalCoefficientSlots h o.1.val) (constantCoefficientSlot _ _)
            (ρ o.1.val) (γ o.1.val) (t * ε o.1.val) e * y (.inr ⟨o.1.val, e⟩))) =
      partitionedProfileConstant h P ρ y o.1 +
      (∑ b, partitionedProfilePrincipal h P γ y o.1 b *
        ∏ v, V s (.inr ⟨o.1.val, b, v⟩)) +
      t * ∑ e ∈ partitionedProfileTerms (G := G) h P o.1,
        (ε o.1.val * y (.inr ⟨o.1.val, e⟩)) * ∏ k ∈ e.val.support, V s k ^ e.val k := by
    rw [boundedProfile_polynomial_split h o.1.val (hh o.1.val)]
    simp only [map_add, map_sum, MvPolynomial.eval_C]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro b _
      simp only [canonicalPrincipalExponent, productBlockExponent_monomial,
        map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X,
        partitionedProfilePrincipal]
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      simp only [MvPolynomial.eval_monomial, Finsupp.prod]
      ring
  have he : partitionedProfileJet h P extra sets ρ γ ε t y x o = _ :=
    congrArg (fun f : Finset α → ℝ => booleanCoefficient f (sets o.1 o.2)) (funext hv)
  rw [he]
  rw [booleanCoefficient_add, booleanCoefficient_add, booleanCoefficient_const,
    booleanCoefficient_const_mul]
  have hp : booleanCoefficient (fun s => ∑ b, partitionedProfilePrincipal h P γ y o.1 b *
      ∏ v, V s (.inr ⟨o.1.val, b, v⟩)) (sets o.1 o.2) =
      jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
        (partitionedProfilePrincipal h P γ y) sets x o := by
    rw [jointBooleanSampler_formula]
    simp only [V, normalizedCubeTuple, partitionedProfileInput_principal, Sum.elim_inr]
  rw [hp]
  change _ + _ + t * normalizedCoefficientTailValue _ _ _ _ _ y x _ = _
  simp only [Pi.add_apply, booleanConstantJet, coefficientArraySampler, add_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
variable {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)

theorem partitionedProfileJet_mul (R ρ γ ε : D → ℝ) (t : ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    partitionedProfileJet h P extra sets (fun d => R d * ρ d) (fun d => R d * γ d)
        (fun d => R d * ε d) t y x =
      fun o => R o.1.val * partitionedProfileJet h P extra sets ρ γ ε t y x o := by
  classical
  funext o
  unfold partitionedProfileJet
  have hscale : t * (R o.1.val * ε o.1.val) = R o.1.val * (t * ε o.1.val) := by ring
  simp_rw [hscale, coefficientProfileCenter_mul, coefficientProfileWidth_mul,
    monomialArrayPolynomial_eval]
  rw [← booleanCoefficient_const_mul]
  congr 1
  funext s
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem partitionedAllocatedProfileJet_scale (R : D → ℝ) (t : ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    partitionedAllocatedProfileJet h P extra sets R t y x =
      fun o => R o.1.val * partitionedAllocatedProfileJet h P extra sets (fun _ => 1) t y x o := by
  have hp (d : D) : principalProfileSize (R d) (Fintype.card (B d)) =
      R d * principalProfileSize 1 (Fintype.card (B d)) := by
    simpa only [mul_one] using principalProfileSize_mul (R d) 1 (Fintype.card (B d))
  have ht (d : D) : tailProfileSize (R d) 1 (Fintype.card (SamplerCoefficientSlot G B h d)) =
      R d * tailProfileSize 1 1 (Fintype.card (SamplerCoefficientSlot G B h d)) := by
    simpa only [mul_one] using tailProfileSize_mul (R d) 1 1 (Fintype.card (SamplerCoefficientSlot G B h d))
  unfold partitionedAllocatedProfileJet
  simp_rw [hp, ht, div_eq_mul_inv, one_mul]
  exact partitionedProfileJet_mul h P extra sets R (fun _ => 4⁻¹) _ _ t y x

omit [Fintype D] in
theorem unitProfilePrincipalSize_pos (d : D) : 0 < unitProfilePrincipalSize (B := B) d :=
  principalProfileSize_pos zero_lt_one _

theorem unitProfileTailSize_pos (d : D) : 0 < unitProfileTailSize (G := G) (B := B) h d :=
  tailProfileSize_pos zero_lt_one zero_lt_one _

omit [Fintype D] [Fintype G] [Fintype α] [DecidableEq α] [DecidablePred P] in
theorem partitionedProfilePrincipal_unit_bounds
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ) (hy : ∀ j, |y j| ≤ 1)
    (d : {d // ¬P d}) (b : B d.val) :
    unitProfilePrincipalSize (B := B) d.val ≤
        |partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y d b| ∧
      |partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y d b| ≤
        2 * unitProfilePrincipalSize (B := B) d.val := by
  have hγ := unitProfilePrincipalSize_pos (B := B) d.val
  obtain ⟨hl, hu⟩ := abs_le.mp (hy (.inr ⟨d.val, principalCoefficientSlot h d.val b⟩))
  have hlo : unitProfilePrincipalSize (B := B) d.val ≤
      partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y d b := by
    unfold partitionedProfilePrincipal
    nlinarith
  rw [abs_of_nonneg (hγ.le.trans hlo)]
  refine ⟨hlo, ?_⟩
  unfold partitionedProfilePrincipal
  nlinarith

omit [Fintype D] [Fintype G] [Fintype α] [DecidableEq α] [DecidablePred P] in
theorem partitionedProfilePrincipal_unit_sum
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ) (hy : ∀ j, |y j| ≤ 1)
    (d : {d // ¬P d}) :
    (∑ b, |partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y d b|) ≤ 1 := by
  have hb := allocatedProfile_budget (R := 1) (σ := 1) zero_le_one le_rfl (Fintype.card (B d.val)) 0
  simp only [Nat.cast_zero, mul_zero, add_zero] at hb
  calc
    _ ≤ ∑ _b : B d.val, 2 * unitProfilePrincipalSize (B := B) d.val :=
      Finset.sum_le_sum (fun b _ => (partitionedProfilePrincipal_unit_bounds h P y hy d b).2)
    _ = 2 * principalProfileSize 1 (Fintype.card (B d.val)) * Fintype.card (B d.val) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, unitProfilePrincipalSize]
      ring
    _ ≤ 1 := by linarith

omit [DecidablePred P] in
theorem partitionedProfileTail_unit_sum (d : {d // ¬P d}) :
    (∑ _e ∈ partitionedProfileTerms (G := G) (B := B) h P d,
      |unitProfileTailSize (G := G) (B := B) h d.val|) ≤ 1 := by
  have he := unitProfileTailSize_pos (G := G) (B := B) h d.val
  have hb := allocatedProfile_budget (R := 1) (σ := 1) zero_le_one le_rfl 0
    (Fintype.card (SamplerCoefficientSlot G B h d.val))
  simp only [Nat.cast_zero, mul_zero, add_zero] at hb
  rw [abs_of_pos he, Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ (Fintype.card (SamplerCoefficientSlot G B h d.val) : ℝ) *
        unitProfileTailSize (G := G) (B := B) h d.val :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) he.le
    _ ≤ 1 := by unfold unitProfileTailSize; nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RetainedSlicedCoefficientSource
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α Z K₀ : Type*} [Fintype Z] [DecidableEq Z]
  [fintypeD : Fintype D] [decidableEqD : DecidableEq D] [Fintype α]
  [decidableEqAlpha : DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [fintypeO : ∀ d, Fintype (O d)]
  [decidableEqB : ∀ d, DecidableEq (B d)] [decidableEqO : ∀ d, DecidableEq (O d)]
  [nonemptyO : ∀ d, Nonempty (O d)]

omit fintypeD decidableEqD fintypeO decidableEqB decidableEqO nonemptyO in
theorem jointAffineBooleanSampler_coordinateScale
    [Fintype D] [DecidableEq D] [∀ d, Fintype (O d)]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (hw : ∀ d i, width d i ≠ 0) :
    jointAffineBooleanSampler c sets
      (fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv) center =
      fun x => jointBooleanSampler h c sets (fun s => center s.1 s.2 + width s.1 s.2 * x s) := rfl

omit fintypeD decidableEqD decidableEqAlpha decidableEqB in
theorem sigmaAxisOperator_coordinateScale
    [Fintype D] [DecidableEq D] [DecidableEq α] [∀ d, DecidableEq (B d)] {h : D → ℕ}
    (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (hw : ∀ d i, width d i ≠ 0) :
    (fun x : JointBlockParameter B h α → ℝ => (fun s => center s.1 s.2) +
      sigmaAxisOperator (fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv.toContinuousLinearMap) x) =
      (fun x s => center s.1 s.2 + width s.1 s.2 * x s) := rfl

theorem exists_uniform_sliced_coefficient_array_source_with_scales
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (degree : ℕ) (hdegree : ∀ d, h d ≤ degree)
    (Csum Wsum : ℝ) (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) {E : ℝ} (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧
    (ρ : ℝ) = jointAffineSourceRadius (B := B) (O := O) (α := α) h c₀ C A T δ E ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    t = jointAffineCoefficientTolerance (Z := Z) (B := B) (O := O) (α := α)
      h c₀ C A T degree Csum Wsum δ E ∧
    ∀ (c : ∀ d, B d → ℝ), (∀ d o, c₀ d ≤ |c d (block d o)|) →
    (∀ d o, |c d (block d o)| ≤ C d) → (∀ d, (∑ b, |c d b|) ≤ Csum) →
    ∀ (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
      (hw : ∀ d z, width d z ≠ 0),
    (∀ d z, δ ≤ |width d z|) → (∀ d z, |center d z| + |width d z| ≤ 1) →
    let L := fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv
    let slice := fun x : JointBlockParameter B h α → ℝ =>
      (fun s => center s.1 s.2) + sigmaAxisOperator (fun d => (L d).toContinuousLinearMap) x
    let f := regularizedImageDensity (jointBooleanSource h) (jointAffineBooleanSampler c sets L center) ρ
    (∀ x, f x ∈ Set.Icc (0 : ℝ) (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    Integrable f ∧ (∫ x, f x) = 1 ∧ LipschitzWith (affineProductProfileLip (Σ d, O d) ρ) f ∧
    ∀ (Terms : D → Type*) (terms : ∀ d, Finset (Terms d)) (weight : ∀ d, Terms d → ℝ)
      (exponent : ∀ d, Terms d → K₀ →₀ ℕ) (coefficientIndex : ∀ d, Terms d → Z)
      (inputIndex : K₀ → Option α → Z ⊕ JointBlockParameter B h α),
    (∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree) →
    (∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum) →
    ∀ z : Z → ℝ, (∀ i, |z i| ≤ 1) →
    ∀ φ : ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ y, f y * φ y) - mappedTest (jointBooleanSource h) (coefficientArraySampler h c sets terms weight exponent coefficientIndex inputIndex t z ∘ slice) φ| ≤ E := by
  let Cp := booleanJetMassBudget (Fintype.card α) degree Csum +
    booleanJetMassBudget (Fintype.card α) degree Wsum
  have hCp : 0 ≤ Cp := add_nonneg (booleanJetMassBudget_nonneg _ _ hCsum)
    (booleanJetMassBudget_nonneg _ _ hWsum)
  obtain ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, hs⟩ := exists_uniform_joint_affine_polynomial_source_with_scales_s2 (Z := Z)
    h hh sets hsets hcard block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition
    (degree + 2) Cp hCp δ hδ hδone hE
  refine ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, ?_⟩
  intro c hclow hcup hcsum center width hw hwidth hbox
  have hd := hs c hclow hcup center width hw hwidth hbox
  refine ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, ?_⟩
  intro Terms terms weight exponent coefficientIndex inputIndex hdeg hweight z hz φ hφ hbound
  have hp := coefficientArraySampler_polynomial_bounds h c sets terms weight exponent coefficientIndex
    inputIndex hdegree hdeg hcsum hweight
  rw [coefficientArraySampler_polynomial]
  exact hd.2.2.2.2 _ hp.1 hp.2 z hz (jointBooleanPerturbedPolynomial_zero _ _ _ _ _) φ hφ hbound

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {Ω D α Z K₀ : Type*} [MeasurableSpace Ω] [Fintype Z] [DecidableEq Z] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

theorem exists_retained_sliced_coefficient_source_with_scales
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (degree : ℕ) (hdegree : ∀ d, h d ≤ degree)
    (Csum Wsum : ℝ) (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) {E : ℝ} (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧
    (ρ : ℝ) = jointAffineSourceRadius (B := B) (O := O) (α := α) h c₀ C A T δ E ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    t = jointAffineCoefficientTolerance (Z := Z) (B := B) (O := O) (α := α)
      h c₀ C A T degree Csum Wsum δ E ∧
    ∀ (Terms : D → Type*) (terms : ∀ d, Finset (Terms d)) (weight : ∀ d, Terms d → ℝ)
      (exponent : ∀ d, Terms d → K₀ →₀ ℕ) (coefficientIndex : ∀ d, Terms d → Z)
      (inputIndex : K₀ → Option α → Z ⊕ JointBlockParameter B h α),
    (∀ d n, n ∈ terms d → (exponent d n).sum (fun _ e => e) ≤ degree) →
    (∀ d, (∑ n ∈ terms d, |weight d n|) ≤ Wsum) →
    ∀ (c : Ω → ∀ d, B d → ℝ) (center width : Ω → JointBlockParameter B h α → ℝ)
      (z : Ω → Z → ℝ),
    (∀ d b, Measurable (fun a => c a d b)) →
    (∀ i, Measurable (fun a => center a i)) → (∀ i, Measurable (fun a => width a i)) →
    (∀ i, Measurable (fun a => z a i)) →
    ∀ μ : Measure Ω, IsProbabilityMeasure μ →
    (∀ᵐ a ∂μ, (∀ d o, c₀ d ≤ |c a d (block d o)|) ∧
      (∀ d o, |c a d (block d o)| ≤ C d) ∧ (∀ d, (∑ b, |c a d b|) ≤ Csum) ∧
      (∀ i, δ ≤ |width a i|) ∧ (∀ i, |center a i| + |width a i| ≤ 1) ∧
      (∀ i, |z a i| ≤ 1)) →
    let slice := fun p : Ω × (JointBlockParameter B h α → ℝ) =>
      fun i => center p.1 i + width p.1 i * p.2 i
    let U := fun p : Ω × (JointBlockParameter B h α → ℝ) => jointBooleanSampler h (c p.1) sets (slice p)
    let V := fun p : Ω × (JointBlockParameter B h α → ℝ) =>
      coefficientArraySampler h (c p.1) sets terms weight exponent coefficientIndex inputIndex t (z p.1) (slice p)
    ∀ φ : Ω × ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ p, regularizedImageDensity (jointBooleanSource (B := B) (α := α) h) (fun x => U (p.1, x)) ρ p.2 * φ p
          ∂μ.prod volume) - ∫ p, φ (p.1, V p) ∂μ.prod (jointBooleanSource (B := B) (α := α) h)| ≤ E := by
  obtain ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, hs⟩ := exists_uniform_sliced_coefficient_array_source_with_scales (Z := Z) (K₀ := K₀)
    h hh sets hsets hcard block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition
    degree hdegree Csum Wsum hCsum hWsum δ hδ hδone hE
  refine ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, ?_⟩
  intro Terms terms weight exponent coefficientIndex inputIndex hdeg hweight c center width z hc hb hw hz μ hμ
    hgood slice U V φ hφ hbound
  let : IsProbabilityMeasure μ := hμ
  have hx (i) : Measurable (fun p : Ω × (JointBlockParameter B h α → ℝ) => slice p i) :=
    ((hb i).comp measurable_fst).add (((hw i).comp measurable_fst).mul
      ((measurable_pi_apply i).comp measurable_snd))
  have hU : Measurable U := jointBooleanSampler_measurable_comp (Ω := Ω × (JointBlockParameter B h α → ℝ)) h sets (fun p => c p.1)
    (fun d b => (hc d b).comp measurable_fst) slice hx
  have hV : Measurable V := coefficientArraySampler_measurable_comp (Ω := Ω × (JointBlockParameter B h α → ℝ)) h sets terms weight exponent
    coefficientIndex inputIndex t (fun p => c p.1) (fun d b => (hc d b).comp measurable_fst)
    (fun p => z p.1) (fun i => (hz i).comp measurable_fst) slice hx
  apply conditionalRegularizedDensity_comparison μ (jointBooleanSource (B := B) (α := α) h) U V hU hV ρ hρ _ φ hφ hbound
  filter_upwards [hgood] with a ha
  let wa := fun d (i : BlockParameter (B d) (Fin (h d)) α) => width a ⟨d, i⟩
  have hwa (d) (i : BlockParameter (B d) (Fin (h d)) α) : wa d i ≠ 0 :=
    abs_pos.mp (hδ.trans_le (ha.2.2.2.1 ⟨d, i⟩))
  have hd := hs (c a) ha.1 ha.2.1 ha.2.2.1
    (fun d i => center a ⟨d, i⟩) wa hwa
    (fun d i => ha.2.2.2.1 ⟨d, i⟩) (fun d i => ha.2.2.2.2.1 ⟨d, i⟩)
  intro f hf hboundf
  have he := hd.2.2.2.2 Terms terms weight exponent coefficientIndex inputIndex hdeg hweight
    (z a) ha.2.2.2.2.2 f hf hboundf
  dsimp only at he
  rw [jointAffineBooleanSampler_coordinateScale,
    sigmaAxisOperator_coordinateScale (fun d i => center a ⟨d, i⟩) wa hwa] at he
  exact he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartitionedSlicedProfileComparison
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem exists_partitioned_sliced_profile_comparison_with_scales
    {Ω D G Z α : Type*} [MeasurableSpace Ω]
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z)
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d.val)
    (block : ∀ d, O d → B d.val) (hblock : ∀ d, Function.Injective (block d))
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    {δ E : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧
    (ρ : ℝ) = partitionedAffineSourceRadius (B := B) (O := O) (α := α) h P A T δ E ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    t = partitionedAffineSourceTolerance (G := G) (Z := Z) (B := B) (O := O) (α := α)
      h P A T degree δ E ∧
    ∀ (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ),
    (∀ j, Measurable (fun a => z a j)) →
    ∀ (center width : Ω → PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ),
    (∀ i, Measurable (fun a => center a i)) → (∀ i, Measurable (fun a => width a i)) →
    ∀ μ : Measure Ω, IsProbabilityMeasure μ →
    (∀ᵐ a ∂μ, (∀ j, |z a j| ≤ 1) ∧ (∀ i, δ ≤ |width a i|) ∧
      (∀ i, |center a i| + |width a i| ≤ 1)) →
    ∀ (R : D → ℝ) (f : Ω × ((Σ d, O d) → ℝ) → ℝ),
    Measurable f → (∀ p, ‖f p‖ ≤ 1) →
    let slice := fun a x i => center a i + width a i * x i
    let ideal := fun a => regularizedImageDensity
      (jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := α) (fun d => h d.val))
      (fun x => jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
        (partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z a)) sets (slice a x)) ρ
    let post := fun a (y : (Σ d, O d) → ℝ) o => R o.1.val *
      (booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) (z a)) o + y o)
    |(∫ p, ideal p.1 p.2 * f (p.1, post p.1 p.2) ∂μ.prod volume) -
      ∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R t (z p.1) (slice p.1 p.2))
        ∂μ.prod (jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := α) (fun d => h d.val))| ≤ E := by
  classical
  obtain ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, hcomp⟩ := exists_retained_sliced_coefficient_source_with_scales
    (Ω := Ω) (Z := PartitionedProfileNoiseIndex G Z α B h P) (K₀ := SamplerTupleIndex G B h)
    (fun d : {d // ¬P d} => h d.val) (fun d => hh d.val) sets hsets hcard block hblock
    (fun d => unitProfilePrincipalSize (B := B) d.val)
    (fun d => 2 * unitProfilePrincipalSize (B := B) d.val)
    (fun d => unitProfilePrincipalSize_pos (B := B) d.val)
    (fun d => mul_nonneg (by norm_num) (unitProfilePrincipalSize_pos (B := B) d.val).le)
    ψ hψ hrange hzero hone A T hLip hTransition degree (fun d => hdegree d.val)
    1 1 zero_le_one zero_le_one δ hδ hδone hE
  refine ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, ?_⟩
  intro z hz center width hcenter hwidth μ hμ hgood R f hf hfb slice ideal post
  let c := fun a => partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z a)
  have hc (d : {d // ¬P d}) (b : B d.val) : Measurable (fun a => c a d b) := by
    dsimp [c, partitionedProfilePrincipal]
    exact measurable_const.add (measurable_const.mul (hz _))
  let F : Ω × ((Σ d, O d) → ℝ) → Ω × ((Σ d, O d) → ℝ) := fun p =>
    (p.1, fun o => R o.1.val *
      (booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) (z p.1)) o + p.2 o))
  have hF : Measurable F := by
    apply measurable_fst.prodMk
    apply measurable_pi_iff.mpr
    intro o
    have hzj := (hz (.inr ⟨o.1.val, constantCoefficientSlot _ _⟩)).comp
      (measurable_fst : Measurable (Prod.fst : Ω × ((Σ d, O d) → ℝ) → Ω))
    dsimp [F, booleanConstantJet, partitionedProfileConstant]
    split_ifs <;> fun_prop
  have hFactual (s : ℝ) (a : Ω)
      (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
      F (a, coefficientArraySampler (fun d : {d // ¬P d} => h d.val) (c a) sets
        (partitionedProfileTerms (G := G) (B := B) h P)
        (fun d _ => unitProfileTailSize (G := G) (B := B) h d.val)
        (fun _ e => e.val) (fun d e => .inr ⟨d.val, e⟩) (partitionedProfileInput P extra) s (z a) x) =
      (a, partitionedAllocatedProfileJet h P extra sets R s (z a) x) := by
    apply Prod.ext
    · rfl
    dsimp only [F]
    rw [partitionedAllocatedProfileJet_scale]
    unfold partitionedAllocatedProfileJet
    rw [partitionedProfileJet_eq h P extra sets hh]
    rfl
  have hcoeff : ∀ᵐ a ∂μ,
      (∀ d o, unitProfilePrincipalSize (B := B) d.val ≤ |c a d (block d o)|) ∧
      (∀ d o, |c a d (block d o)| ≤ 2 * unitProfilePrincipalSize (B := B) d.val) ∧
      (∀ d, (∑ b, |c a d b|) ≤ 1) ∧ (∀ i, δ ≤ |width a i|) ∧
      (∀ i, |center a i| + |width a i| ≤ 1) ∧ (∀ j, |z a j| ≤ 1) := by
    filter_upwards [hgood] with a ha
    exact ⟨fun d o => (partitionedProfilePrincipal_unit_bounds h P (z a) ha.1 d (block d o)).1,
      fun d o => (partitionedProfilePrincipal_unit_bounds h P (z a) ha.1 d (block d o)).2,
      partitionedProfilePrincipal_unit_sum h P (z a) ha.1, ha.2.1, ha.2.2, ha.1⟩
  have he := hcomp (fun d : {d // ¬P d} => SamplerCoefficientSlot G B h d.val)
    (partitionedProfileTerms (G := G) (B := B) h P)
    (fun d _ => unitProfileTailSize (G := G) (B := B) h d.val)
    (fun _ e => e.val) (fun d e => .inr ⟨d.val, e⟩) (partitionedProfileInput P extra)
    (fun d e _ => e.property.trans (hdegree d.val)) (partitionedProfileTail_unit_sum h P)
    c center width z hc hcenter hwidth hz μ hμ hcoeff (f ∘ F) (hf.comp hF) (fun p => hfb (F p))
  dsimp only [Function.comp_apply] at he
  simp_rw [hFactual] at he
  exact he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PartitionedSlicedDensityComparison
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

theorem conditionalRegularizedDensity_translate_test {W X I : Type*}
    [MeasurableSpace W] [MeasurableSpace X] [Fintype I]
    (μ : Measure W) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (U : W × X → I → ℝ) (hU : Measurable U) (b : W → I → ℝ) (hb : Measurable b)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (φ : W × (I → ℝ) → ℝ) (hφ : Measurable φ)
    (hbound : ∀ p, ‖φ p‖ ≤ 1) :
    (∫ p, regularizedImageDensity ν (fun x => b p.1 + U (p.1, x)) ρ p.2 * φ p ∂μ.prod volume) =
      ∫ p, regularizedImageDensity ν (fun x => U (p.1, x)) ρ p.2 * φ (p.1, b p.1 + p.2)
        ∂μ.prod volume := by
  have hshift : Measurable (fun p : W × X => b p.1 + U p) := (hb.comp measurable_fst).add hU
  have hD := conditionalRegularizedDensity_measurable ν U hU ρ
  have hDshift := conditionalRegularizedDensity_measurable ν _ hshift ρ
  have hprob (w) := regularizedImageDensity_probability ν (fun x => U (w, x))
    (hU.comp (measurable_const.prodMk measurable_id)) ρ hρ
  have hprobshift (w) := regularizedImageDensity_probability ν (fun x => b w + U (w, x))
    (hshift.comp (measurable_const.prodMk measurable_id)) ρ hρ
  have hi := (densityMixture_joint_integrable μ volume _ hDshift
    (Filter.Eventually.of_forall hprobshift)).mul_bdd hφ.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  have htest : Measurable (fun p : W × (I → ℝ) => φ (p.1, b p.1 + p.2)) :=
    hφ.comp (measurable_fst.prodMk ((hb.comp measurable_fst).add measurable_snd))
  have hj := (densityMixture_joint_integrable μ volume _ hD
    (Filter.Eventually.of_forall hprob)).mul_bdd htest.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => hbound (p.1, b p.1 + p.2)))
  dsimp only [Function.uncurry] at hi hj
  rw [integral_prod _ hi, integral_prod _ hj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => regularizedImageDensity_translate_test ν _
    (hU.comp (measurable_const.prodMk measurable_id)) ρ hρ (b w) (fun y => φ (w, y))
    (hφ.comp (measurable_const.prodMk measurable_id)))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem exists_partitioned_sliced_density_comparison_with_scales_s2_oai
    {Ω D G Z α : Type*} [MeasurableSpace Ω]
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z)
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d.val)
    (block : ∀ d, O d → B d.val) (hblock : ∀ d, Function.Injective (block d))
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    {δ E : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧
    (ρ : ℝ) = partitionedAffineSourceRadius (B := B) (O := O) (α := α) h P A T δ E ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    t = partitionedAffineSourceTolerance (G := G) (Z := Z) (B := B) (O := O) (α := α)
      h P A T degree δ E ∧
    ∀ (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ),
    (∀ j, Measurable (fun a => z a j)) →
    ∀ (center width : Ω → PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ),
    (∀ i, Measurable (fun a => center a i)) → (∀ i, Measurable (fun a => width a i)) →
    ∀ μ : Measure Ω, IsProbabilityMeasure μ →
    (∀ᵐ a ∂μ, (∀ j, |z a j| ≤ 1) ∧ (∀ i, δ ≤ |width a i|) ∧
      (∀ i, |center a i| + |width a i| ≤ 1)) →
    ∀ (R : D → ℝ) (f : Ω × ((Σ d, O d) → ℝ) → ℝ),
    Measurable f → (∀ p, ‖f p‖ ≤ 1) →
    let slice := fun a x i => center a i + width a i * x i
    let ideal := fun a => partitionedSlicedRegularizedIdeal h P sets ρ (center a) (width a) (z a)
    let post := fun (y : (Σ d, O d) → ℝ) o => R o.1.val * y o
    |(∫ p, ideal p.1 p.2 * f (p.1, post p.2) ∂μ.prod volume) -
      ∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R t (z p.1) (slice p.1 p.2))
        ∂μ.prod (jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := α) (fun d => h d.val))| ≤ E := by
  classical
  obtain ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, hs⟩ := exists_partitioned_sliced_profile_comparison_with_scales
    (Ω := Ω) h hh P extra sets hsets hcard block hblock ψ hψ hrange hzero hone A T hLip hTransition
    hdegree hδ hδone hE
  refine ⟨ρ, hρ, hρone, hρeq, t, ht, htone, hteq, ?_⟩
  intro z hz center width hb hw μ hμ hgood R f hf hbound slice ideal post
  let : IsProbabilityMeasure μ := hμ
  let source := jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := α) (fun d => h d.val)
  let U := fun p : Ω ×
    (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) =>
      jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
        (partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z p.1)) sets (slice p.1 p.2)
  have hc (d : {d // ¬P d}) (b : B d.val) : Measurable (fun a =>
      partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z a) d b) := by
    dsimp [partitionedProfilePrincipal]
    exact measurable_const.add (measurable_const.mul (hz _))
  have hU : Measurable U := jointBooleanSampler_measurable_comp
    (Ω := Ω × (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ))
    (fun d : {d // ¬P d} => h d.val) sets _ (fun d b => (hc d b).comp measurable_fst)
    (fun p => slice p.1 p.2) (fun i => ((hb i).comp measurable_fst).add
      (((hw i).comp measurable_fst).mul ((measurable_pi_apply i).comp measurable_snd)))
  let b := fun a => booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) (z a))
  have hbm : Measurable b := by
    apply booleanConstantJet_measurable_comp
    intro d
    exact measurable_const.mul (hz _)
  let φ := fun p : Ω × ((Σ d, O d) → ℝ) => f (p.1, post p.2)
  have hφ : Measurable φ := hf.comp (measurable_fst.prodMk (measurable_pi_iff.mpr
    (fun o => measurable_const.mul ((measurable_pi_apply o).comp measurable_snd))))
  have heq := conditionalRegularizedDensity_translate_test μ source U hU b hbm ρ hρ φ hφ
    (fun p => hbound (p.1, post p.2))
  have he := hs z hz center width hb hw μ hμ hgood R f hf hbound
  dsimp only at he
  change (∫ p, ideal p.1 p.2 * f (p.1, post p.2) ∂μ.prod volume) =
    (∫ p, regularizedImageDensity source (fun x => U (p.1, x)) ρ p.2 *
      f (p.1, fun o => R o.1.val * (b p.1 o + p.2 o)) ∂μ.prod volume) at heq
  rw [heq]
  exact he

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.exists_partitioned_sliced_density_comparison_with_scales_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.exists_partitioned_sliced_density_comparison_with_scales_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
