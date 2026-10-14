-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedNormalizedLongJetDensity_zero_off_ball
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-11T13:14:21.634617+00:00
-- url     : https://prove2.me/submissions/5e8a0f23-3ce8-4860-8db8-ef4824cf6fde

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B169

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

theorem booleanCoefficient_div {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) (a : ℝ) :
    booleanCoefficient (fun t => f t / a) s = booleanCoefficient f s / a := by
  simp only [booleanCoefficient, ← mul_div_assoc, Finset.sum_div]

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

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

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.TranslatedMixtureL1
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] in
theorem pivotOutputDensity_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℝ) :
    pivotOutputDensity A B f v = inverseJacobian A * ∫ y, f (y, A.symm (v - B y)) := by
  exact integral_const_mul _ _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotJacobianBound
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] in
theorem coordinateMatrix_entry_le_norm (f : (J → ℝ) →L[ℝ] (I → ℝ)) (i : I) (j : J) :
    |(LinearMap.toMatrix' f.toLinearMap) i j| ≤ ‖f‖ := by
  rw [LinearMap.toMatrix'_apply]
  calc
    |f (Pi.single j 1) i| ≤ ‖f (Pi.single j 1)‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (f (Pi.single j 1)) i
    _ ≤ ‖f‖ * ‖(Pi.single j 1 : J → ℝ)‖ := f.le_opNorm (Pi.single j 1)
    _ = ‖f‖ := by rw [Pi.norm_single, norm_one, mul_one]

theorem inverseJacobian_le_norm_bound (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) {U : ℝ}
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ U) :
    inverseJacobian A ≤ (Fintype.card I).factorial * U ^ Fintype.card I := by
  have h := matrix_det_abs_le_uniform_bound
    (LinearMap.toMatrix' A.symm.toContinuousLinearMap.toLinearMap)
    (fun i j => (coordinateMatrix_entry_le_norm A.symm.toContinuousLinearMap i j).trans hA)
  rw [LinearMap.det_toMatrix'] at h
  exact h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PivotNormalizedMatrix
namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem normalizedIntegerPivot_entry (A : Matrix I I ℤ) (S P : I → ℝ) (i j : I) :
    normalizedIntegerPivot A S P i j = (A i j : ℝ) * S j / P i := by
  simp only [normalizedIntegerPivot, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.map_apply, Int.coe_castRingHom, div_eq_mul_inv]
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFiberUniformBound
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem normalizedPivotEquiv_coe (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedPivotEquiv A hA S P hS hP).toContinuousLinearMap =
      matrixSupCLM (normalizedIntegerPivot A S P) :=
  (matrixSupCLM_inverse_spec (normalizedIntegerPivot A S P)
    (normalizedIntegerPivot_det_ne_zero A hA S P hS hP)).1.choose_spec

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators NNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

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
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem splitInputProfile_integral (f : (J → ℝ) × (I → ℝ) → ℝ) :
    (∫ x, splitInputProfile f x) = ∫ p, f p :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : J ⊕ I => ℝ)).integral_comp
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ I => ℝ)).measurableEmbedding f

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

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

theorem booleanCoefficient_abs_le {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) {M : ℝ}
    (hf : ∀ t ∈ s.powerset, |f t| ≤ M) :
    |booleanCoefficient f s| ≤ (2 : ℝ) ^ s.card * M := by
  unfold booleanCoefficient
  calc
    _ ≤ ∑ t ∈ s.powerset, |(-1 : ℝ) ^ (s \ t).card * f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ s.powerset, M := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hf t ht
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem realAffineCube_abs_le {α K : Type*} [Fintype α]
    (root : K → ℝ) (difference : α → K → ℝ)
    (hroot : ∀ k, |root k| ≤ 1) (hd : ∀ r k, |difference r k| ≤ 1)
    (t : Finset α) (k : K) :
    |realAffineCube root difference t k| ≤ (Fintype.card α : ℝ) + 1 := by
  unfold realAffineCube
  calc
    _ ≤ |root k| + |∑ r ∈ t, difference r k| := abs_add_le _ _
    _ ≤ 1 + ∑ r ∈ t, |difference r k| :=
      add_le_add (hroot k) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 1 + ∑ _r ∈ t, (1 : ℝ) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun r _ => hd r k))
    _ = 1 + t.card := by simp
    _ ≤ (Fintype.card α : ℝ) + 1 := by
      have hc : (t.card : ℝ) ≤ Fintype.card α := by exact_mod_cast Finset.card_le_univ t
      linarith

theorem real_monomial_eval_abs_le {K : Type*} (e : K →₀ ℕ) (x : K → ℝ)
    {C : ℝ} (hC : 1 ≤ C) (hx : ∀ k, |x k| ≤ C) {h : ℕ}
    (he : e.sum (fun _ n => n) ≤ h) :
    |MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℝ))| ≤ C ^ h := by
  classical
  rw [MvPolynomial.eval_monomial, one_mul]
  change |∏ k ∈ e.support, x k ^ e k| ≤ _
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ k ∈ e.support, C ^ e k := by
      apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
      intro k _
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hx k) _
    _ = C ^ e.sum (fun _ n => n) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ C ^ h := pow_le_pow_right₀ hC he

theorem boundedDegreeRealJetMatrix_entry_bound {α K O : Type*}
    [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ)
    (hroot : ∀ k, |root k| ≤ 1) (hd : ∀ r k, |difference r k| ≤ 1)
    (h : ℕ) (rows : O → Finset α) (o : O) (e : BoundedIntegerExponent K h) :
    |boundedDegreeRealJetMatrix root difference h rows o e| ≤
      (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ h := by
  have hb := booleanCoefficient_abs_le
    (fun t => MvPolynomial.eval (realAffineCube root difference t)
      (MvPolynomial.monomial e.val (1 : ℝ))) (rows o)
    (fun t _ => real_monomial_eval_abs_le e.val _ (le_add_of_nonneg_left (Nat.cast_nonneg _))
      (realAffineCube_abs_le root difference hroot hd t) e.property)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem booleanJetColumnPolynomial_mass_le {K P α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ) (s : Finset α)
    {d : ℕ} (hd : e.sum (fun _ n => n) ≤ d) {A : ℝ}
    (hA : 1 ≤ ((Fintype.card α : ℝ)+1)*A) (hi : ∀ k r, realPolynomialMass (input k r) ≤ A) :
    realPolynomialMass (booleanJetColumnPolynomial e input s) ≤
      2^s.card * (((Fintype.card α : ℝ)+1)*A)^d := by
  apply booleanCoefficient_mass_le
  intro t _
  exact (polynomialMonomial_mass_le _ _ (fun k _ => booleanAffineInput_mass_le _ _ (hi k))).trans
    (pow_le_pow_right₀ hA hd)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

theorem splitFreeProfile_zero_outside {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} {R S : ℝ}
    (hf : ∀ p, R < ‖p‖ → f p = 0) (hg : ∀ n, S < ‖n‖ → g n = 0)
    (p : (J ⊕ N → ℝ) × (I → ℝ)) (hp : max R S < ‖p‖) :
    splitFreeProfile f g p = 0 := by
  let y : J → ℝ := fun j => p.1 (.inl j)
  let n : N → ℝ := fun n => p.1 (.inr n)
  by_cases hy : R < ‖(y, p.2)‖
  · exact mul_eq_zero_of_left (hf _ hy) _
  · have hn : S < ‖n‖ := by
      by_contra! hn
      have hy' : ‖(y, p.2)‖ ≤ R := le_of_not_gt hy
      have hnorm : ‖p‖ ≤ max R S := by
        rw [Prod.norm_def]
        apply max_le
        · rw [← splitCoordinates_norm p.1, Prod.norm_def]
          exact max_le ((norm_fst_le (y, p.2)).trans (hy'.trans (le_max_left _ _)))
            (hn.trans (le_max_right _ _))
        · exact (norm_snd_le (y, p.2)).trans (hy'.trans (le_max_left _ _))
      exact (not_le_of_gt hp) hnorm
    exact mul_eq_zero_of_right _ (hg _ hn)

theorem splitFreeProfile_slice_integrable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (v : I → ℝ) :
    Integrable (fun p : (J → ℝ) × (N → ℝ) =>
      f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2) := by
  have hc : Continuous (fun p : (J → ℝ) × (N → ℝ) =>
      f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2) := by fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : (J → ℝ) × (N → ℝ)) (max R S))
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  apply hp
  have heq : ‖Sum.elim p.1 p.2‖ = ‖p‖ := (splitCoordinates_norm (Sum.elim p.1 p.2)).symm
  have hz := splitFreeProfile_zero_outside hfs hgs
    (Sum.elim p.1 p.2, A.symm (v - (B p.1 + C p.2)))
    (h.trans_le (heq ▸ norm_fst_le
      (Sum.elim p.1 p.2, A.symm (v - (B p.1 + C p.2)))))
  exact hz

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {I J N : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]

theorem normalizedIntegerColumns_entry (B : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ)
    (i : I) (j : J) : normalizedIntegerColumns B T P i j = (P i)⁻¹ * B i j * T j := by
  simp [normalizedIntegerColumns, Matrix.diagonal_mul, Matrix.mul_diagonal]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

end Erdos3

end

section

namespace Erdos3

theorem normalizedIntegerColumns_entry_div {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) (i : I) (j : J) :
    normalizedIntegerColumns A T P i j = (A i j : ℝ) * T j / P i := by
  rw [normalizedIntegerColumns_entry]
  simp only [div_eq_mul_inv]
  ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem selectedCoefficientProfile_zero_outside {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} {R : ℝ}
    (hf : ∀ x, R < ‖x‖ → f x = 0) :
    ∀ p, R < ‖p‖ → selectedCoefficientProfile s f p = 0 := by
  intro p hp
  exact hf _ (by rwa [selectedCoefficientEquiv_norm])

end Erdos3

end

section

namespace Erdos3

variable {I J R : Type*} [Fintype I] (s : I ↪ J)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeProductSupport
namespace OAI

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

namespace Erdos3

open MeasureTheory

theorem integerScalarCubeBox_normalized_norm_le {I : Type*} [Fintype I] {L : ℕ}
    (hL : 0 < L) (z : IntegerScalarCubeBox I L) : ‖fun i => (z i : ℝ) / L‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  have hz := Finset.mem_Ico.mp (z i).property
  have hbound : |(z i : ℝ)| ≤ L := abs_le.mpr
    ⟨by exact_mod_cast hz.1, by exact_mod_cast hz.2.le⟩
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by exact_mod_cast hL : (0 : ℝ) < L)]
  exact (div_le_one (by exact_mod_cast hL)).mpr hbound

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedJetColumns
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem frozenTupleCoordinate_mass_le {Z P : Type*} (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1) (i : Z ⊕ P) :
    realPolynomialMass (frozenTupleCoordinate z i) ≤ 1 := by
  cases i with
  | inl j => exact (realPolynomialMass_C (z j)).le.trans (hz j)
  | inr i => exact (realPolynomialMass_X i).le

theorem normalizedJetColumn_mass_le {Z P K α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (s : Finset α) {d : ℕ} (hd : e.sum (fun _ n => n) ≤ d) :
    realPolynomialMass (normalizedJetColumn e input z s) ≤
      (2 : ℝ)^Fintype.card α * ((Fintype.card α : ℝ)+1)^d := by
  have he := booleanJetColumnPolynomial_mass_le e _ s hd (A := 1) (by simp)
    (fun k r => frozenTupleCoordinate_mass_le z hz (input k r))
  simp only [mul_one] at he
  exact he.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Finset.card_le_univ s)) (by positivity))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PivotDensitySupport
namespace OAI

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

theorem splitPivotDensity_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (v : I → ℝ) :
    pivotOutputDensity A (splitFreeColumns B C) (splitFreeProfile f g) v =
      ∫ n, g n * pivotOutputDensity A B f (v - C n) := by
  let F : (J → ℝ) × (N → ℝ) → ℝ := fun p =>
    f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2
  have hi : Integrable F := splitFreeProfile_slice_integrable A B C hf hg hfs hgs v
  rw [pivotOutputDensity_formula]
  change inverseJacobian A * (∫ y, splitInputProfile F y) = _
  rw [splitInputProfile_integral, Measure.volume_eq_prod, integral_prod_symm _ hi,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with n
  have heq (y : J → ℝ) : v - (B y + C n) = (v - C n) - B y := by abel
  simp only [F, heq, integral_mul_const, pivotOutputDensity_formula]
  ring

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

namespace Erdos3

open MeasureTheory

theorem pivotOutputDensity_zero_outside {I J : Type*} [Fintype I] [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {R : ℝ}
    (hs : ∀ p, R < ‖p‖ → f p = 0) (v : I → ℝ)
    (hv : (‖A.toContinuousLinearMap‖+‖B‖)*R < ‖v‖) :
    pivotOutputDensity A B f v = 0 := by
  have he (y : J → ℝ) : f (y,A.symm (v-B y)) = 0 := by
    by_contra hn
    have hp : ‖(y,A.symm (v-B y))‖ ≤ R := le_of_not_gt (fun h => hn (hs _ h))
    have hy := (norm_fst_le (y,A.symm (v-B y))).trans hp
    have ha := (norm_snd_le (y,A.symm (v-B y))).trans hp
    have hv' : v = A (A.symm (v-B y)) + B y := by rw [A.apply_symm_apply]; abel
    have hb : ‖v‖ ≤ (‖A.toContinuousLinearMap‖+‖B‖)*R := by
      calc
        ‖v‖ = ‖A (A.symm (v-B y)) + B y‖ := congrArg norm hv'
        _ ≤ ‖A (A.symm (v-B y))‖ + ‖B y‖ := norm_add_le _ _
        _ ≤ ‖A.toContinuousLinearMap‖*‖A.symm (v-B y)‖ + ‖B‖*‖y‖ :=
          add_le_add (A.toContinuousLinearMap.le_opNorm _) (B.le_opNorm _)
        _ ≤ ‖A.toContinuousLinearMap‖*R + ‖B‖*R := by gcongr
        _ = _ := by ring
    exact (not_le_of_gt hv) hb
  rw [pivotOutputDensity_formula]
  simp only [he, integral_zero, mul_zero]

theorem splitPivotDensity_zero_outside {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) {R S T : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (hC : ‖C‖ ≤ T) (v : I → ℝ) (hv : (‖A.toContinuousLinearMap‖+‖B‖)*R+T*S < ‖v‖) :
    pivotOutputDensity A (splitFreeColumns B C) (splitFreeProfile f g) v = 0 := by
  rw [splitPivotDensity_formula A B C hf hg hfs hgs v]
  have he (n : N → ℝ) : g n * pivotOutputDensity A B f (v-C n) = 0 := by
    by_cases hn : g n = 0
    · simp only [hn, zero_mul]
    · have hnS : ‖n‖ ≤ S := le_of_not_gt (fun h => hn (hgs n h))
      have hCn : ‖C n‖ ≤ T*S := (C.le_opNorm n).trans
        (mul_le_mul hC hnS (norm_nonneg _) ((norm_nonneg C).trans hC))
      have hdiff : (‖A.toContinuousLinearMap‖+‖B‖)*R < ‖v-C n‖ := by
        have ht : ‖v‖ ≤ ‖v-C n‖+‖C n‖ := by
          simpa only [sub_add_cancel] using norm_add_le (v-C n) (C n)
        linarith
      rw [pivotOutputDensity_zero_outside A B hfs _ hdiff, mul_zero]
  simp only [he, integral_zero]

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialColumnSupport
namespace OAI

section

namespace Erdos3

theorem polynomialColumns_norm_le_on_box {P I J : Type*} [Fintype P] [Fintype I] [Fintype J]
    (p : I → J → MvPolynomial P ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i j, realPolynomialMass (p i j) ≤ C) (x : P → ℝ) (hx : ‖x‖ ≤ 1) :
    ‖polynomialColumns p x‖ ≤ Fintype.card J * C := by
  apply matrixSupCLM_norm_le _ hC
  intro i j
  exact (mvPolynomial_eval_abs_le_sum_coeff (p i j) x
    (fun k => (norm_le_pi_norm x k).trans hx)).trans (hc i j)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedJetDensitySupport
namespace OAI

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

namespace Erdos3

open scoped NNReal

theorem normalizedJetDensity_zero_outside {Z P K α I J N : Type*}
    [Fintype P] [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (rows : I → Finset α) {degree : ℕ} (hd : ∀ n, (e n).sum (fun _ k => k) ≤ degree)
    (R S : ℝ≥0) {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfs : ∀ u, (R : ℝ) < ‖u‖ → f u = 0) (hgs : ∀ n, (S : ℝ) < ‖n‖ → g n = 0)
    (x : P → ℝ) (hx : ‖x‖ ≤ 1) (v : I → ℝ)
    (hv : (normalizedJetOutputRadius α N A F degree R S : ℝ) < ‖v‖) :
    normalizedJetDensity A F e input z rows f g x v = 0 := by
  have hmass (o) (n) : realPolynomialMass (normalizedJetColumn (e n) input z (rows o)) ≤
      (normalizedJetMass α degree : ℝ) := normalizedJetColumn_mass_le (e n) input z hz (rows o) (hd n)
  have hcols := polynomialColumns_norm_le_on_box _ (normalizedJetMass α degree).coe_nonneg hmass x hx
  exact splitPivotDensity_zero_outside A F _ hf hg hfs hgs hcols v hv

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerNormalizedJetColumns
namespace OAI

namespace Erdos3

open scoped BigOperators

theorem real_monomial_eval_div_scale {K : Type*} (e : K →₀ ℕ) (x T : K → ℝ) :
    MvPolynomial.eval (fun k => x k / T k) (MvPolynomial.monomial e (1 : ℝ)) =
      MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℝ)) / monomialScale T e := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul, monomialScale, Finsupp.prod,
    div_pow, Finset.prod_div_distrib]

theorem integer_monomial_eval_cast {K : Type*} (e : K →₀ ℕ) (x : K → ℤ) :
    (MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℤ)) : ℝ) =
      MvPolynomial.eval (fun k => (x k : ℝ)) (MvPolynomial.monomial e (1 : ℝ)) := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, Int.cast_prod, Int.cast_pow]

theorem normalizedIntegerMonomialJetMatrix_eq {α K O J : Type*} [DecidableEq α]
    [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
    (e : J → K →₀ ℕ) (vertices : Finset α → K → ℤ) (rows : O → Finset α)
    (T : K → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns
      (integerJetMatrix (fun j => MvPolynomial.monomial (e j) 1) vertices rows)
      (fun j => H / monomialScale T (e j)) (fun _ => H) =
    realJetMatrix (fun j => MvPolynomial.monomial (e j) 1)
      (fun t k => (vertices t k : ℝ) / T k) rows := by
  ext o j
  rw [normalizedIntegerColumns_entry_div]
  change ((booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
    (MvPolynomial.monomial (e j) (1 : ℤ))) (rows o) : ℤ) : ℝ) *
      (H / monomialScale T (e j)) / H =
    booleanCoefficient (fun t => MvPolynomial.eval (fun k => (vertices t k : ℝ) / T k)
      (MvPolynomial.monomial (e j) (1 : ℝ))) (rows o)
  have hcast := booleanCoefficient_map (Int.castRingHom ℝ)
    (fun t => MvPolynomial.eval (vertices t) (MvPolynomial.monomial (e j) (1 : ℤ))) (rows o)
  change ((booleanCoefficient _ (rows o) : ℤ) : ℝ) =
    booleanCoefficient (fun t => (MvPolynomial.eval (vertices t)
      (MvPolynomial.monomial (e j) (1 : ℤ)) : ℝ)) (rows o) at hcast
  rw [hcast]
  simp only [real_monomial_eval_div_scale, integer_monomial_eval_cast]
  rw [booleanCoefficient_div]
  simp [div_eq_mul_inv, hH, mul_assoc, mul_comm]

theorem realAffineCube_normalized_integer {α K : Type*}
    (root : K → ℤ) (difference : α → K → ℤ) (T : K → ℝ) (t : Finset α) (k : K) :
    realAffineCube (fun k => (root k : ℝ) / T k)
      (fun r k => (difference r k : ℝ) / T k) t k =
        (integerAffineCube root difference t k : ℝ) / T k := by
  simp only [realAffineCube, integerAffineCube, Int.cast_add, Int.cast_sum,
    add_div, Finset.sum_div]

theorem normalizedBoundedIntegerJetMatrix_eq {α K O : Type*}
    [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℤ) (difference : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α)
    (T : K → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns (boundedDegreeIntegerJetMatrix root difference h rows)
      (fun e => H / monomialScale T e.val) (fun _ => H) =
    boundedDegreeRealJetMatrix (fun k => (root k : ℝ) / T k)
      (fun r k => (difference r k : ℝ) / T k) h rows := by
  have hv : (fun t k => (integerAffineCube root difference t k : ℝ) / T k) =
      realAffineCube (fun k => (root k : ℝ) / T k)
        (fun r k => (difference r k : ℝ) / T k) := by
    funext t k
    exact (realAffineCube_normalized_integer root difference T t k).symm
  have he := normalizedIntegerMonomialJetMatrix_eq
    (fun e : BoundedIntegerExponent K h => e.val) (integerAffineCube root difference) rows T hH
  rw [hv] at he
  exact he

end Erdos3

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelJetAllowances
namespace OAI

section

namespace Erdos3

theorem kernelJetInterpolationAllowance_pos (q h : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < kernelJetInterpolationAllowance q h κ := by
  unfold kernelJetInterpolationAllowance
  positivity

theorem kernelJetEntryAllowance_pos (q h : ℕ) : 0 < kernelJetEntryAllowance q h := by
  unfold kernelJetEntryAllowance
  positivity

theorem kernelJetMinorThreshold_pos (q n j h : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < kernelJetMinorThreshold q n j h κ := by
  have := kernelJetInterpolationAllowance_pos q h hκ
  unfold kernelJetMinorThreshold
  positivity

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScaleIndependence
namespace OAI

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

theorem normalizedIntegerColumns_submatrix {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (S : J → ℝ) (P : I → ℝ) (p : I → J) :
    (normalizedIntegerColumns A S P).submatrix id p =
      normalizedIntegerPivot (A.submatrix id p) (fun i => S (p i)) P := by
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, normalizedIntegerColumns_entry_div,
    normalizedIntegerPivot_entry]

open scoped Matrix

theorem normalized_remainingMatrixColumns {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (P : I → ℝ) :
    normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P =
      remainingMatrixColumns (normalizedIntegerColumns A S P) s := by
  classical
  ext i j
  simp only [remainingMatrixColumns, Matrix.submatrix_apply, id_eq,
    normalizedIntegerColumns_entry_div]

end Erdos3

namespace Erdos3

theorem normalizedScalarKernelJet_eq {I J O : Type*}
    [DecidableEq I] [Fintype J] [Fintype O] [DecidableEq O] {L : ℕ}
    (x : J → IntegerScalarCubeBox I L) (h : ℕ) (rows : O → Finset I)
    {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns (scalarKernelIntegerJet x h rows)
      (fun e => H / monomialScale (fun _ => (L : ℝ)) e.val) (fun _ => H) =
      normalizedScalarKernelJet x h rows :=
  normalizedBoundedIntegerJetMatrix_eq _ _ _ _ _ hH

theorem normalized_scalarKernel_pivot {I J O : Type*} [DecidableEq I] [Fintype J]
    [Fintype O] [DecidableEq O] {L : ℕ} (x : J → IntegerScalarCubeBox I L)
    (h : ℕ) (rows : O → Finset I) (p : O → BoundedIntegerExponent J h)
    {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerPivot ((scalarKernelIntegerJet x h rows).submatrix id p)
      (fun o => kernelJetCoefficientScale J h L H (p o)) (fun _ => H) =
      (normalizedScalarKernelJet x h rows).submatrix id p := by
  have he := congrArg (fun A : Matrix O (BoundedIntegerExponent J h) ℝ => A.submatrix id p)
    (normalizedScalarKernelJet_eq x h rows hH)
  rw [normalizedIntegerColumns_submatrix] at he
  exact he

theorem scalarKernel_pivot_scale_independent {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ}
    (hL : 0 < L) (x : J → IntegerScalarCubeBox α L) (degree : ℕ)
    (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent J degree)
    (hs : ((scalarKernelIntegerJet x degree rows).submatrix id s).det ≠ 0)
    {H : ℝ} (hH : 0 < H) :
    normalizedPivotEquiv _ hs (fun i => kernelJetCoefficientScale J degree L H (s i))
      (fun _ => H) (fun i => kernelJetCoefficientScale_pos J degree (by exact_mod_cast hL) hH (s i))
      (fun _ => hH) = scalarKernelFixedPivot hL x degree rows s hs := by
  ext v i
  change ((normalizedPivotEquiv _ hs _ _ _ _).toContinuousLinearMap v) i =
    ((scalarKernelFixedPivot hL x degree rows s hs).toContinuousLinearMap v) i
  simp only [scalarKernelFixedPivot, normalizedPivotEquiv_coe,
    normalized_scalarKernel_pivot x degree rows s hH.ne',
    normalized_scalarKernel_pivot x degree rows s one_ne_zero]

theorem scalarKernel_free_scale_independent {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ}
    (x : J → IntegerScalarCubeBox α L) (degree : ℕ)
    (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent J degree)
    {H : ℝ} (hH : H ≠ 0) :
    matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (scalarKernelIntegerJet x degree rows) s)
      (fun j => kernelJetCoefficientScale J degree L H j.val) (fun _ => H)) =
      scalarKernelFixedFree x degree rows s := by
  rw [normalized_remainingMatrixColumns]
  unfold scalarKernelFixedFree
  apply congrArg matrixSupCLM
  ext i j
  change normalizedIntegerColumns (scalarKernelIntegerJet x degree rows)
    (kernelJetCoefficientScale J degree L H) (fun _ => H) i j.val =
      normalizedScalarKernelJet x degree rows i j.val
  have he := congrFun (congrFun (normalizedScalarKernelJet_eq x degree rows hH) i) j.val
  simpa only [normalizedIntegerColumns_entry_div, kernelJetCoefficientScale] using he

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JetOutputRadiusLogBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem normalizedJetMass_le_exp (α : Type*) [Fintype α] (d : ℕ) :
    (normalizedJetMass α d : ℝ) ≤ Real.exp ((Fintype.card α : ℝ)*(d+1)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    convert Real.add_one_le_exp (1 : ℝ) using 1
    norm_num
  have hbase := Real.add_one_le_exp (Fintype.card α : ℝ)
  change (2 : ℝ)^Fintype.card α * ((Fintype.card α : ℝ)+1)^d ≤ _
  calc
    _ ≤ (Real.exp 1)^Fintype.card α * (Real.exp (Fintype.card α : ℝ))^d :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) htwo _) (pow_le_pow_left₀ (by positivity) hbase _)
        (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem jetOutputRadiusLog_nonneg (q n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ jetOutputRadiusLog q n d P := by unfold jetOutputRadiusLog; positivity

theorem normalizedJetOutputRadius_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (α N : Type*) [Fintype α] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (degree : ℕ) (R S : ℝ≥0) {P : ℝ} (hP : 0 ≤ P)
    (hA : ‖A.toContinuousLinearMap‖ ≤ Real.exp P) (hF : ‖F‖ ≤ Real.exp P)
    (hR : (R : ℝ) ≤ Real.exp P) (hS : (S : ℝ) ≤ Real.exp P) :
    (normalizedJetOutputRadius α N A F degree R S : ℝ) ≤
      Real.exp (jetOutputRadiusLog (Fintype.card α) (Fintype.card N) degree P) := by
  have hAF := add_le_exp_add_one hP hP hA hF
  have hlinear : (‖A.toContinuousLinearMap‖+‖F‖)*(R : ℝ) ≤ Real.exp (3*P+1) := by
    calc
      _ ≤ Real.exp (P+P+1)*Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmass : (normalizedJetMass α degree : ℝ) ≤
      Real.exp (Fintype.card α+(degree : ℝ)*Fintype.card α) := by
    have he : (Fintype.card α : ℝ)*(degree+1) = Fintype.card α+(degree : ℝ)*Fintype.card α := by ring
    simpa only [he] using normalizedJetMass_le_exp α degree
  have hn : (Fintype.card N : ℝ) ≤ Real.exp (Fintype.card N : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card N : ℝ)]
  have htail : (Fintype.card N : ℝ)*(normalizedJetMass α degree : ℝ)*(S : ℝ) ≤
      Real.exp (Fintype.card N+Fintype.card α+(degree : ℝ)*Fintype.card α+P) := by
    calc
      _ ≤ Real.exp (Fintype.card N : ℝ)*Real.exp (Fintype.card α+(degree : ℝ)*Fintype.card α)*Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hs := add_le_exp_add_one (show 0 ≤ 3*P+1 by positivity)
    (show 0 ≤ (Fintype.card N : ℝ)+Fintype.card α+(degree : ℝ)*Fintype.card α+P by positivity) hlinear htail
  change (‖A.toContinuousLinearMap‖+‖F‖)*(R : ℝ)+
    (Fintype.card N : ℝ)*(normalizedJetMass α degree : ℝ)*(S : ℝ) ≤ _
  apply hs.trans_eq
  congr 1
  unfold jetOutputRadiusLog
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointPivotProfileBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem profileWidthPower_le_exp (n : ℕ) {δ t : ℝ} (hδ : 0 < δ)
    (hi : δ⁻¹ ≤ Real.exp t) : δ⁻¹ ^ n ≤ Real.exp ((n : ℝ) * t) := by
  calc
    _ ≤ (Real.exp t)^n := by gcongr
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem affineProductProfileLip_le_exp (I : Type*) [Fintype I]
    {δ : ℝ≥0} {t : ℝ} (hi : (δ : ℝ)⁻¹ ≤ Real.exp t) :
    (affineProductProfileLip I δ : ℝ) ≤ Real.exp (affineProfileLogBound (Fintype.card I) t) := by
  have hn : (Fintype.card I : ℝ) ≤ Real.exp (Fintype.card I : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I : ℝ)]
  have hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp (probabilityProfileLipschitz : ℝ) := by
    linarith [Real.add_one_le_exp (probabilityProfileLipschitz : ℝ)]
  simp only [affineProductProfileLip, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_inv]
  calc
    _ ≤ Real.exp (Fintype.card I : ℝ) * Real.exp (probabilityProfileLipschitz : ℝ) *
        (Real.exp t)^(Fintype.card I + 1) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [affineProfileLogBound, Nat.cast_add, Nat.cast_one]

theorem affineProductProfile_cap_le_exp (n : ℕ) {δ t : ℝ} (hδ : 0 < δ)
    (ht : 0 ≤ t) (hi : δ⁻¹ ≤ Real.exp t) :
    δ⁻¹ ^ n ≤ Real.exp (affineProfileLogBound n t) := by
  apply (profileWidthPower_le_exp n hδ hi).trans
  apply Real.exp_le_exp.mpr
  unfold affineProfileLogBound
  nlinarith [NNReal.coe_nonneg probabilityProfileLipschitz, Nat.cast_nonneg n (α := ℝ)]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem inverseJacobian_le_exp {I : Type*} [Fintype I]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) {P : ℝ}
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ Real.exp P) :
    inverseJacobian A ≤ Real.exp ((Fintype.card I : ℝ)^2+Fintype.card I*P) := by
  classical
  apply (inverseJacobian_le_norm_bound A hA).trans
  calc
    _ ≤ Real.exp ((Fintype.card I : ℝ)^2)*(Real.exp P)^Fintype.card I := by
      gcongr
      exact factorial_le_exp_sq _
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

theorem pivotKernelCap_le_exp {I : Type*} [Fintype I] (J : Type*) [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (R H : ℝ≥0) {P Q : ℝ}
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ Real.exp P)
    (hR : (R : ℝ) ≤ Real.exp P) (hH : (H : ℝ) ≤ Real.exp Q) :
    (pivotKernelCap J A R H : ℝ) ≤
      Real.exp ((Fintype.card I : ℝ)^2+Fintype.card I*P+Q+Fintype.card J*(P+1)) := by
  have hJ := inverseJacobian_le_exp A hA
  have hJ0 := (inverseJacobian_pos A).le
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h2R : 2*(R : ℝ) ≤ Real.exp (P+1) := by
    calc
      _ ≤ Real.exp 1*Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  change inverseJacobian A*(H : ℝ)*(2*(R : ℝ))^Fintype.card J ≤ _
  calc
    _ ≤ Real.exp ((Fintype.card I : ℝ)^2+Fintype.card I*P)*Real.exp Q*
        (Real.exp (P+1))^Fintype.card J := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]

theorem pivotKernelLip_le_exp {I : Type*} [Fintype I] (J : Type*) [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (R K : ℝ≥0) {P Q : ℝ}
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ Real.exp P)
    (hR : (R : ℝ) ≤ Real.exp P) (hK : (K : ℝ) ≤ Real.exp Q) :
    (pivotKernelLip J A R K : ℝ) ≤
      Real.exp ((Fintype.card I : ℝ)^2+(Fintype.card I+1)*P+Q+Fintype.card J*(P+1)) := by
  have hcap := pivotKernelCap_le_exp J A R K hA hR hK
  change (pivotKernelCap J A R K : ℝ)*‖A.symm.toContinuousLinearMap‖ ≤ _
  calc
    _ ≤ Real.exp ((Fintype.card I : ℝ)^2+Fintype.card I*P+Q+Fintype.card J*(P+1))*Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D] {O J : D → Type*}
  [∀ d, Fintype (O d)] [∀ d, Fintype (J d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineL1Parameter
namespace OAI

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem affineSelectedJetDensity_output_support {Z X K α I J N : Type*}
    [Fintype X] [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (rows : I → Finset α) {degree : ℕ} (hd : ∀ n, (e n).sum (fun _ k => k) ≤ degree)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    (x : X → ℝ) (hx : ‖x‖ ≤ 1) (v : I → ℝ)
    (hv : (normalizedJetOutputRadius α N A F degree R R : ℝ) < ‖v‖) :
    affineSelectedJetDensity s A F e input z rows c w x v = 0 := by
  exact normalizedJetDensity_zero_outside A F e input z hz rows hd R R
    ((affineProductProfile_contDiff _ _).continuous.comp (selectedCoefficientEquiv_lipschitz s).continuous)
    (affineProductProfile_contDiff _ _).continuous
    (selectedCoefficientProfile_zero_outside s
      (affineProductProfile_zero_outside _ _ (fun j => hw (.inl j)) R.coe_nonneg (fun j => hsupport (.inl j))))
    (affineProductProfile_zero_outside _ _ (fun n => hw (.inr n)) R.coe_nonneg (fun n => hsupport (.inr n)))
    x hx v hv

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem principalTupleNormalized_norm_le {D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (y : PrincipalIntegerTuples B h α L) : ‖principalTupleNormalized L y‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro a
  exact (norm_le_pi_norm (fun i => (y ⟨a.1, a.2.1, a.2.2.1⟩ i : ℝ)/L ⟨a.1, a.2.1, a.2.2.1⟩) a.2.2.2).trans
    (integerScalarCubeBox_normalized_norm_le (hL _) (y _))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}

variable [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {D α : Type*} [Fintype α] [DecidableEq α]
variable (B : D → Type*) (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

end Erdos3

end

section

namespace Erdos3

variable {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}

theorem partitionedPrincipalInput_frozen_bound [Fintype D] [∀ d, Fintype (B d)]
    [Fintype α] [DecidableEq α] (P : D → Prop) [DecidablePred P]
    (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (u : PrincipalAxisTuples (α := α) P L)
    (j : Z ⊕ PrincipalAxisParameter (B := B) (h := h) (α := α) P) :
    |Sum.elim zr (principalTupleNormalized (principalAxisLength P L) u) j| ≤ 1 := by
  cases j with
  | inl j => exact hz j
  | inr j =>
    have hb : ‖principalTupleNormalized (principalAxisLength P L) u‖ ≤ 1 :=
      principalTupleNormalized_norm_le
        (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (fun k => hL ⟨k.1.val, k.2⟩) u
    exact (norm_le_pi_norm (principalTupleNormalized (principalAxisLength P L) u) j).trans hb

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {G : Type*} [Fintype G] [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "degree" => layerSamplerDegree I n

section Law

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]

end Law

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

omit [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)] in
theorem allocatedNonkernelExponent_degree (j : Fin m) (d : AllocatedNonkernelCoefficient (G := G) B j) :
    (allocatedNonkernelExponent B j d).sum (fun _ r => r) ≤ j.val+1 := d.val.property

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i

include hR hσ hσ1 in
theorem allocatedKernelProfile_bound (d) : |centers d|+widths d ≤ R j :=
  (allocatedProfile_term_bound (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (layerIntegerPrincipalSlots_not_constant B j i) (hR j) (hσ j) hσ1 d).trans (by linarith [hR j])


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

include hR hσ in
theorem allocatedContinuousProfileWidths_pos (j : Fin m) (i : I j) (d) :
    0 < allocatedContinuousProfileWidths (G := G) B R σ j i d :=
  coefficientProfileWidth_pos _ _ (div_pos (hR j) (by norm_num))
    (principalProfileSize_pos (hR j) _) (tailProfileSize_pos (hR j) (hσ j) _) d

include hR hσ in
theorem allocatedContinuousProfile_bound (j : Fin m) (i : I j) (hσ1 : σ j ≤ 1) (d) :
    |allocatedContinuousProfileCenters (G := G) B R j i d| +
      allocatedContinuousProfileWidths B R σ j i d ≤ R j :=
  (allocatedProfile_term_bound (layerContinuousPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (layerContinuousPrincipalSlots_not_constant B j i) (hR j) (hσ j) hσ1 d).trans (by linarith [hR j])

variable (j : Fin m) (i : I j)


local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators Matrix Classical

theorem allocatedUnitProfileWidth_pos {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (a : ℕ) :
    0 < allocatedUnitProfileWidth R σ a :=
  allocatedWidthFloor_pos hR hσ zero_lt_one 0 a

theorem allocatedUnitProfileWidth_inverse_exp (a : ℕ) {R σ P : ℝ}
    (hP : 0 ≤ P) (hR : 0 < R) (hσ : 0 < σ)
    (hRP : R⁻¹ ≤ Real.exp P) (hσP : σ⁻¹ ≤ Real.exp P) (haP : (a : ℝ)+1 ≤ Real.exp P) :
    (allocatedUnitProfileWidth R σ a)⁻¹ ≤ Real.exp (4*(P+8)) := by
  let X := Real.exp (P+8)
  have hPX : Real.exp P ≤ X := Real.exp_le_exp.mpr (by linarith)
  have hX : 8 ≤ X := by dsimp [X]; linarith [Real.add_one_le_exp (P+8)]
  have hLX : ((1 : ℕ) : ℝ) ≤ X := by norm_num; linarith
  have h := allocatedWidthFloor_inverse_power_bound 1 0 0 a le_rfl hR hσ hX
    (hRP.trans hPX) (hσP.trans hPX) (haP.trans hPX) hLX
  simpa only [allocatedUnitProfileWidth, X, ← Real.exp_nat_mul, Nat.zero_add, Nat.cast_ofNat] using h

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : I j)

local notation "unitWidth" => allocatedUnitProfileWidth (R j) (σ j)
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) 1

theorem allocatedPartitionedInput_frozen_bound (t) : |fixedReal t| ≤ 1 := by
  apply partitionedPrincipalInput_frozen_bound grid _ _ sides (allocatedPrincipalSides_pos B U basis S) u t
  intro ga
  have h := (norm_le_pi_norm (fun a => ((x ga.1 a : ℤ) : ℝ)/(S.value : ℝ)) ga.2).trans
    (integerScalarCubeBox_normalized_norm_le S.positive (x ga.1))
  simpa only [Real.norm_eq_abs] using h

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget
namespace OAI

section

namespace Erdos3

theorem kernelJetInterpolationAllowance_le_exp (q h : ℕ) {κ b : ℝ}
    (hκ : 0 < κ) (hb : 0 ≤ b) (hi : κ⁻¹ ≤ Real.exp b) :
    kernelJetInterpolationAllowance q h κ ≤
      Real.exp ((h : ℝ) * ((q : ℝ)^2 + q + b + 2)) := by
  have hq : (q : ℝ) ≤ Real.exp q := by linarith [Real.add_one_le_exp (q : ℝ)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hterm : (q : ℝ) * (2 * (q.factorial / κ)) ≤
      Real.exp ((q : ℝ)^2 + q + b + 1) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp q * (Real.exp 1 * (Real.exp ((q : ℝ)^2) * Real.exp b)) := by
        gcongr
        exact factorial_le_exp_sq q
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have he : 1 ≤ Real.exp ((q : ℝ)^2 + q + b + 1) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hbase : 1 + (q : ℝ) * (2 * (q.factorial / κ)) ≤
      Real.exp ((q : ℝ)^2 + q + b + 2) := by
    calc
      _ ≤ 2 * Real.exp ((q : ℝ)^2 + q + b + 1) := by linarith
      _ ≤ Real.exp 1 * Real.exp ((q : ℝ)^2 + q + b + 1) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  unfold kernelJetInterpolationAllowance
  calc
    _ ≤ (Real.exp ((q : ℝ)^2 + q + b + 2)) ^ h := by gcongr
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem kernelJetEntryAllowance_le_exp (q h : ℕ) :
    kernelJetEntryAllowance q h ≤ Real.exp ((q : ℝ) * (h + 1)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hq := Real.add_one_le_exp (q : ℝ)
  unfold kernelJetEntryAllowance
  calc
    _ ≤ (Real.exp 1) ^ q * (Real.exp q) ^ h := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem kernelJetMinorThreshold_inv_le_exp (q n j h : ℕ) {κ b : ℝ}
    (hκ : 0 < κ) (hb : 0 ≤ b) (hi : κ⁻¹ ≤ Real.exp b) :
    (kernelJetMinorThreshold q n j h κ)⁻¹ ≤
      Real.exp ((j : ℝ) * (h * n + h * ((q : ℝ)^2 + q + b + 2))) := by
  have hn := Real.add_one_le_exp (n : ℝ)
  have hQ := kernelJetInterpolationAllowance_le_exp q h hκ hb hi
  have hQpos := (kernelJetInterpolationAllowance_pos q h hκ).le
  simp only [kernelJetMinorThreshold, one_div, inv_inv]
  calc
    _ ≤ ((Real.exp n) ^ h *
        Real.exp ((h : ℝ) * ((q : ℝ)^2 + q + b + 2))) ^ j := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]

theorem kernelJetInverseAllowance_le_exp (q n j h : ℕ) {κ b : ℝ}
    (hκ : 0 < κ) (hb : 0 ≤ b) (hi : κ⁻¹ ≤ Real.exp b) :
    kernelJetInverseAllowance q n j h κ ≤
      Real.exp ((j : ℝ) + (j : ℝ)^2 +
        (j - 1 : ℕ) * ((q : ℝ) * (h + 1)) +
        j * (h * n + h * ((q : ℝ)^2 + q + b + 2))) := by
  have hj : (j : ℝ) ≤ Real.exp j := by linarith [Real.add_one_le_exp (j : ℝ)]
  have hE := kernelJetEntryAllowance_le_exp q h
  have hEin := (kernelJetEntryAllowance_pos q h).le
  have hminor := kernelJetMinorThreshold_inv_le_exp q n j h hκ hb hi
  have hminorpos := (kernelJetMinorThreshold_pos q n j h hκ).le
  unfold kernelJetInverseAllowance
  rw [div_eq_mul_inv]
  calc
    _ ≤ Real.exp j * ((Real.exp ((j : ℝ)^2) *
        (Real.exp ((q : ℝ) * (h + 1))) ^ (j - 1)) *
        Real.exp ((j : ℝ) * (h * n + h * ((q : ℝ)^2 + q + b + 2)))) := by
      gcongr
      exact factorial_le_exp_sq j
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem scalarKernel_real_entry_bound {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] {L : ℕ} (hL : 0 < L)
    (x : J → IntegerScalarCubeBox α L) (degree : ℕ) (rows : O → Finset α)
    (i : O) (a : BoundedIntegerExponent J degree) :
    |normalizedScalarKernelJet x degree rows i a| ≤ kernelJetEntryAllowance (Fintype.card α) degree := by
  have hc (j : J) (i : Option α) : |(x j i : ℝ) / L| ≤ 1 :=
    (norm_le_pi_norm (fun i => (x j i : ℝ) / L) i).trans
      (integerScalarCubeBox_normalized_norm_le hL (x j))
  exact boundedDegreeRealJetMatrix_entry_bound _ _ (fun j => hc j none)
    (fun i j => hc j (some i)) degree rows i a

theorem scalarKernelFixed_operator_bounds {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ} (hL : 0 < L)
    (x : J → IntegerScalarCubeBox α L) (degree : ℕ) (rows : O → Finset α)
    (s : O ↪ BoundedIntegerExponent J degree)
    (hs : ((scalarKernelIntegerJet x degree rows).submatrix id s).det ≠ 0) :
    ‖(scalarKernelFixedPivot hL x degree rows s hs).toContinuousLinearMap‖ ≤
      Fintype.card O * kernelJetEntryAllowance (Fintype.card α) degree ∧
    ‖scalarKernelFixedFree x degree rows s‖ ≤
      Fintype.card (UnselectedColumn s) * kernelJetEntryAllowance (Fintype.card α) degree := by
  constructor
  · rw [scalarKernelFixedPivot, normalizedPivotEquiv_coe,
      normalized_scalarKernel_pivot x degree rows s one_ne_zero]
    exact matrixSupCLM_norm_le _ (kernelJetEntryAllowance_pos _ _).le
      (fun i j => scalarKernel_real_entry_bound hL x degree rows i (s j))
  · exact matrixSupCLM_norm_le _ (kernelJetEntryAllowance_pos _ _).le
      (fun i j => scalarKernel_real_entry_bound hL x degree rows i j.val)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem kernelGeometryLog_bounds (q n j k d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ kernelGeometryLog q n j k d p ∧ p ≤ kernelGeometryLog q n j k d p ∧
    kernelInverseLog q n j d p ≤ kernelGeometryLog q n j k d p ∧
    (j : ℝ) + (q : ℝ) * (d + 1) ≤ kernelGeometryLog q n j k d p ∧
    (k : ℝ) + (q : ℝ) * (d + 1) ≤ kernelGeometryLog q n j k d p := by
  have hi : 0 ≤ kernelInverseLog q n j d p := by unfold kernelInverseLog; positivity
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have he : 0 ≤ (q : ℝ) * (d + 1) := by positivity
  unfold kernelGeometryLog
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem nat_mul_kernelEntry_le_exp (a q d : ℕ) :
    (a : ℝ) * kernelJetEntryAllowance q d ≤ Real.exp ((a : ℝ) + (q : ℝ) * (d + 1)) := by
  have ha : (a : ℝ) ≤ Real.exp a := by linarith [Real.add_one_le_exp (a : ℝ)]
  calc
    _ ≤ Real.exp a * Real.exp ((q : ℝ) * (d + 1)) :=
      mul_le_mul ha (kernelJetEntryAllowance_le_exp q d) (kernelJetEntryAllowance_pos q d).le (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

theorem fixedKernel_geometry_le_exp {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L M : ℕ} (hL : 0 < L) (hM : 0 < M)
    (x : J → IntegerScalarCubeBox α L) (d : ℕ) (rows : O → Finset α)
    (s : O ↪ BoundedIntegerExponent J d)
    (hs : ((scalarKernelIntegerJet x d rows).submatrix id s).det ≠ 0)
    (hi : ‖(scalarKernelFixedPivot hL x d rows s hs).symm.toContinuousLinearMap‖ ≤
      kernelJetInverseAllowance (Fintype.card α) (Fintype.card J) (Fintype.card O) d (1/(M : ℝ)))
    {p : ℝ} (hp : 0 ≤ p) (hMp : (M : ℝ) ≤ Real.exp p) :
    let P := kernelGeometryLog (Fintype.card α) (Fintype.card J) (Fintype.card O)
      (Fintype.card (BoundedIntegerExponent J d)) d p
    ‖(scalarKernelFixedPivot hL x d rows s hs).toContinuousLinearMap‖ ≤ Real.exp P ∧
    ‖(scalarKernelFixedPivot hL x d rows s hs).symm.toContinuousLinearMap‖ ≤ Real.exp P ∧
    ‖scalarKernelFixedFree x d rows s‖ ≤ Real.exp P := by
  dsimp only
  have hb := kernelGeometryLog_bounds (Fintype.card α) (Fintype.card J) (Fintype.card O)
    (Fintype.card (BoundedIntegerExponent J d)) d hp
  have he := scalarKernelFixed_operator_bounds hL x d rows s hs
  have hcard : Fintype.card (UnselectedColumn s) ≤ Fintype.card (BoundedIntegerExponent J d) :=
    Fintype.card_subtype_le _
  refine ⟨he.1.trans ((nat_mul_kernelEntry_le_exp _ _ _).trans (Real.exp_le_exp.mpr hb.2.2.2.1)), ?_, ?_⟩
  · apply hi.trans
    apply (kernelJetInverseAllowance_le_exp (Fintype.card α) (Fintype.card J) (Fintype.card O) d
      (one_div_pos.mpr (by exact_mod_cast hM)) hp (by simpa only [one_div, inv_inv] using hMp)).trans
    exact Real.exp_le_exp.mpr hb.2.2.1
  · apply he.2.trans
    apply (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard : (Fintype.card (UnselectedColumn s) : ℝ) ≤
      Fintype.card (BoundedIntegerExponent J d)) (kernelJetEntryAllowance_pos _ _).le).trans
    exact (nat_mul_kernelEntry_le_exp _ _ _).trans (Real.exp_le_exp.mpr hb.2.2.2.2)

theorem kernelRowOutputLog_nonneg (q n j k u d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ kernelRowOutputLog q n j k u d p := by
  have hP := (kernelGeometryLog_bounds q n j k d hp).1
  have hf := affineProfileLogBound_nonneg k hp
  have hr := jetOutputRadiusLog_nonneg q u d hP
  unfold kernelRowOutputLog
  positivity

theorem fixedKernel_output_le_exp {α J O N : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] [Fintype N]
    {L M : ℕ} (hL : 0 < L) (hM : 0 < M)
    (x : J → IntegerScalarCubeBox α L) (d : ℕ) (rows : O → Finset α)
    (s : O ↪ BoundedIntegerExponent J d)
    (hs : ((scalarKernelIntegerJet x d rows).submatrix id s).det ≠ 0)
    (hi : ‖(scalarKernelFixedPivot hL x d rows s hs).symm.toContinuousLinearMap‖ ≤
      kernelJetInverseAllowance (Fintype.card α) (Fintype.card J) (Fintype.card O) d (1/(M : ℝ)))
    (δ R : ℝ≥0) (hδ : 0 < δ) {p : ℝ} (hp : 0 ≤ p) (hMp : (M : ℝ) ≤ Real.exp p)
    (hR : (R : ℝ) ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let E := scalarKernelFixedPivot hL x d rows s hs
    let F := scalarKernelFixedFree x d rows s
    let B := kernelRowOutputLog (Fintype.card α) (Fintype.card J) (Fintype.card O)
      (Fintype.card (BoundedIntegerExponent J d)) (Fintype.card N) d p
    (pivotKernelCap (UnselectedColumn s) E R (δ⁻¹^Fintype.card (BoundedIntegerExponent J d)) : ℝ) ≤ Real.exp B ∧
    (pivotKernelLip (UnselectedColumn s) E R (affineProductProfileLip (BoundedIntegerExponent J d) δ) : ℝ) ≤ Real.exp B ∧
    (normalizedJetOutputRadius α N E F d R R : ℝ) ≤ Real.exp B := by
  dsimp only
  let P := kernelGeometryLog (Fintype.card α) (Fintype.card J) (Fintype.card O)
    (Fintype.card (BoundedIntegerExponent J d)) d p
  have hb := kernelGeometryLog_bounds (Fintype.card α) (Fintype.card J) (Fintype.card O)
    (Fintype.card (BoundedIntegerExponent J d)) d hp
  have hnorm := fixedKernel_geometry_le_exp hL hM x d rows s hs hi hp hMp
  have hP : 0 ≤ P := hb.1
  have hRP : (R : ℝ) ≤ Real.exp P := hR.trans (Real.exp_le_exp.mpr hb.2.1)
  have hprof := affineProfileLogBound_nonneg (Fintype.card (BoundedIntegerExponent J d)) hp
  have hrad := jetOutputRadiusLog_nonneg (Fintype.card α) (Fintype.card N) d hb.1
  have hcard : (Fintype.card (UnselectedColumn s) : ℝ) ≤ Fintype.card (BoundedIntegerExponent J d) :=
    by exact_mod_cast Fintype.card_subtype_le (fun a : BoundedIntegerExponent J d => a ∉ Set.range s)
  have hmul := mul_le_mul_of_nonneg_right hcard (by linarith : 0 ≤ P + 1)
  have hcap : ((δ⁻¹^Fintype.card (BoundedIntegerExponent J d) : ℝ≥0) : ℝ) ≤
      Real.exp (affineProfileLogBound (Fintype.card (BoundedIntegerExponent J d)) p) := by
    simpa only [NNReal.coe_pow, NNReal.coe_inv] using
      affineProductProfile_cap_le_exp _ (show (0 : ℝ) < δ from hδ) hp hδp
  refine ⟨?_, ?_, ?_⟩
  · apply (pivotKernelCap_le_exp _ _ R _ hnorm.2.1 hRP hcap).trans
    apply Real.exp_le_exp.mpr
    dsimp [kernelRowOutputLog]
    nlinarith [hb.1]
  · apply (pivotKernelLip_le_exp _ _ R _ hnorm.2.1 hRP
      (affineProductProfileLip_le_exp (BoundedIntegerExponent J d) hδp)).trans
    apply Real.exp_le_exp.mpr
    dsimp [kernelRowOutputLog]
    linarith
  · apply (normalizedJetOutputRadius_le_exp α N _ _ d R R hb.1 hnorm.1 hnorm.2.2 hRP hRP).trans
    apply Real.exp_le_exp.mpr
    have hbase : 0 ≤ (Fintype.card O : ℝ)^2 + (Fintype.card O + 1) * P +
        affineProfileLogBound (Fintype.card (BoundedIntegerExponent J d)) p +
        Fintype.card (BoundedIntegerExponent J d) * (P + 1) := by positivity
    dsimp [kernelRowOutputLog]
    linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelComparisonScales
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem kernelFamilyOutputLog_nonneg {Q α J : Type*} [Fintype Q] [Fintype α] [Fintype J]
    (O N : Q → Type*) [∀ q, Fintype (O q)] [∀ q, Fintype (N q)] (degree : Q → ℕ)
    {p : ℝ} (hp : 0 ≤ p) : 0 ≤ kernelFamilyOutputLog (α := α) (J := J) O N degree p := by
  unfold kernelFamilyOutputLog
  exact add_nonneg zero_le_one (Finset.sum_nonneg (fun q _ => kernelRowOutputLog_nonneg _ _ _ _ _ _ hp))

theorem kernelRowOutputLog_le_family {Q α J : Type*} [Fintype Q] [Fintype α] [Fintype J]
    (O N : Q → Type*) [∀ q, Fintype (O q)] [∀ q, Fintype (N q)] (degree : Q → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (q : Q) :
    kernelRowOutputLog (Fintype.card α) (Fintype.card J) (Fintype.card (O q))
      (Fintype.card (BoundedIntegerExponent J (degree q))) (Fintype.card (N q)) (degree q) p ≤
        kernelFamilyOutputLog (α := α) (J := J) O N degree p := by
  unfold kernelFamilyOutputLog
  exact (Finset.single_le_sum (fun r _ => kernelRowOutputLog_nonneg (Fintype.card α) (Fintype.card J)
      (Fintype.card (O r)) (Fintype.card (BoundedIntegerExponent J (degree r))) (Fintype.card (N r)) (degree r) hp)
    (Finset.mem_univ q)).trans (le_add_of_nonneg_left zero_le_one)

theorem fixedKernel_family_output_bound {Q α J : Type*}
    [Fintype Q] [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    {O N : Q → Type*} [∀ q, Fintype (O q)] [∀ q, DecidableEq (O q)] [∀ q, Fintype (N q)]
    {L M : ℕ} (hL : 0 < L) (hM : 0 < M) (x : J → IntegerScalarCubeBox α L)
    (degree : Q → ℕ) (rows : ∀ q, O q → Finset α)
    (s : ∀ q, O q ↪ BoundedIntegerExponent J (degree q))
    (hs : ∀ q, ((scalarKernelIntegerJet x (degree q) (rows q)).submatrix id (s q)).det ≠ 0)
    (hi : ∀ q, ‖(scalarKernelFixedPivot hL x (degree q) (rows q) (s q) (hs q)).symm.toContinuousLinearMap‖ ≤
      kernelJetInverseAllowance (Fintype.card α) (Fintype.card J) (Fintype.card (O q)) (degree q) (1/(M : ℝ)))
    (δ R : Q → ℝ≥0) (hδ : ∀ q, 0 < δ q) {p : ℝ} (hp : 0 ≤ p) (hMp : (M : ℝ) ≤ Real.exp p)
    (hR : ∀ q, (R q : ℝ) ≤ Real.exp p) (hδp : ∀ q, (δ q : ℝ)⁻¹ ≤ Real.exp p)
    (H : Q → ℝ) (hH : ∀ q, 0 < H q) :
    let C : ℝ≥0 := ⟨Real.exp (kernelFamilyOutputLog (α := α) (J := J) O N degree p), (Real.exp_pos _).le⟩
    let E := fun q => normalizedPivotEquiv _ (hs q)
      (fun i => kernelJetCoefficientScale J (degree q) L (H q) (s q i)) (fun _ => H q)
      (fun i => kernelJetCoefficientScale_pos J (degree q) (by exact_mod_cast hL) (hH q) (s q i))
      (fun _ => hH q)
    let F := fun q => matrixSupCLM (normalizedIntegerColumns
      (remainingMatrixColumns (scalarKernelIntegerJet x (degree q) (rows q)) (s q))
      (fun j => kernelJetCoefficientScale J (degree q) L (H q) j.val) (fun _ => H q))
    1 ≤ C ∧
    (∀ q, pivotKernelCap (UnselectedColumn (s q)) (E q) (R q)
      ((δ q)⁻¹^Fintype.card (BoundedIntegerExponent J (degree q))) ≤ C) ∧
    (∀ q, pivotKernelLip (UnselectedColumn (s q)) (E q) (R q)
      (affineProductProfileLip (BoundedIntegerExponent J (degree q)) (δ q)) ≤ C) ∧
    (∀ q, normalizedJetOutputRadius α (N q) (E q) (F q) (degree q) (R q) (R q) ≤ C) := by
  dsimp only
  have hE (q) := scalarKernel_pivot_scale_independent hL x (degree q) (rows q) (s q) (hs q) (hH q)
  have hF (q) := scalarKernel_free_scale_independent x (degree q) (rows q) (s q) (hH q).ne'
  simp_rw [hE, hF]
  have hrow (q) := fixedKernel_output_le_exp (N := N q) hL hM x (degree q) (rows q) (s q) (hs q)
    (hi q) (δ q) (R q) (hδ q) hp hMp (hR q) (hδp q)
  have hbound (q) := Real.exp_le_exp.mpr (kernelRowOutputLog_le_family (α := α) (J := J) O N degree hp q)
  refine ⟨?_, fun q => ?_, fun q => ?_, fun q => ?_⟩
  · exact_mod_cast Real.one_le_exp_iff.mpr (kernelFamilyOutputLog_nonneg (α := α) (J := J) O N degree hp)
  · exact_mod_cast (hrow q).1.trans (hbound q)
  · exact_mod_cast (hrow q).2.1.trans (hbound q)
  · exact_mod_cast (hrow q).2.2.trans (hbound q)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedDensityParameterBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedDensityLog_bounds (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P : ℝ} (hP : 0 ≤ P) :
    let K := kernelFamilyOutputLog (α := α) (J := G) O
      (AllocatedNonkernelCoefficient (G := G) B) (fun j => j.val+1) (4*(P+8))
    0 ≤ allocatedDensityLog (G := G) B α O P ∧
      K ≤ allocatedDensityLog (G := G) B α O P ∧
      ∀ j, K + allocatedDensityColumnLog (G := G) B α j + P ≤
        allocatedDensityLog (G := G) B α O P := by
  dsimp only
  have hK := kernelFamilyOutputLog_nonneg (α := α) (J := G) O
    (AllocatedNonkernelCoefficient (G := G) B) (fun j => j.val+1)
    (show 0 ≤ 4*(P+8) by positivity)
  have hj (j : Fin m) : 0 ≤ allocatedDensityColumnLog (G := G) B α j := by
    unfold allocatedDensityColumnLog
    positivity
  have hs := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hj j)
  unfold allocatedDensityLog
  refine ⟨by positivity, by linarith, ?_⟩
  intro j
  have h := Finset.single_le_sum (fun k _ => hj k) (Finset.mem_univ j)
  linarith

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m,
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)

local notation "budget" => allocatedDensityLog (G := G) B α O P

include hR hσ hM hi hP hMP hRP hRi hσi hcount

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "bound" => NNReal.mk (Real.exp (allocatedDensityLog (G := G) B α O P))
  (le_of_lt (Real.exp_pos _))
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)

include hR hσ hM hi hP hMP hRP hRi hσi hcount

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedJetSupportBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedJetSupportLog_bounds (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ allocatedJetSupportLog (G := G) B α O P ∧
      allocatedDensityLog (G := G) B α O P ≤ allocatedJetSupportLog (G := G) B α O P ∧
      ∀ j : Fin m,
        (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) +
          (Fintype.card α : ℝ)*((j.val+1 : ℕ)+1) + P ≤ allocatedJetSupportLog (G := G) B α O P := by
  have hQ := (allocatedDensityLog_bounds (G := G) B α O hP).1
  have hj (j : Fin m) : 0 ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) +
        (Fintype.card α : ℝ)*((j.val+1 : ℕ)+1) := by positivity
  have hs := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hj j)
  unfold allocatedJetSupportLog
  refine ⟨by positivity, by linarith, ?_⟩
  intro j
  have he := Finset.single_le_sum (fun k _ => hj k) (Finset.mem_univ j)
  linarith

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalZeroSpatialDensity
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

theorem sigmaAxisWeight_zero_outside (f : ∀ d, (I d → ℝ) → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hf : ∀ d x, R < ‖x‖ → f d x = 0)
    (x : (Σ d, I d) → ℝ) (hx : R < ‖x‖) : sigmaAxisWeight f x = 0 := by
  classical
  have hlarge : ∃ d, R < ‖sigmaAxisProjection I d x‖ := by
    by_contra hn
    have hnorm : ‖x‖ ≤ R := by
      apply (pi_norm_le_iff_of_nonneg hR).2
      intro i
      exact (norm_le_pi_norm (sigmaAxisProjection I i.1 x) i.2).trans
        (le_of_not_gt (fun hi => hn ⟨i.1, hi⟩))
    exact (not_lt_of_ge hnorm) hx
  obtain ⟨d, hd⟩ := hlarge
  change (∏ a, f a (sigmaAxisProjection I a x)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ d) (hf d _ hd)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped Matrix NNReal BigOperators

variable {I J X : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype X]
variable (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

variable [IsEmpty I]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m)
variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixed" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ)/(S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

section Continuous

variable (i : I j)
local notation "scale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) 1
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => scale (s o)) (fun _ => 1)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1) (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) zero_lt_one (s o))
  (fun _ => zero_lt_one)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => scale (Subtype.val d)) (fun _ => 1))

include hσ in
theorem allocatedContinuousKernelDensity_support_data (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ)
    (hy : ‖y‖ ≤ 1) (z : O → ℝ)
    (hz : (normalizedJetOutputRadius α (AllocatedNonkernelCoefficient (G := G) B j)
      pivot free (j.val+1) radius radius : ℝ) < ‖z‖) :
    allocatedContinuousKernelDensity B U basis S j i x u rows s hA y z = 0 := by
  have hs := affineSelectedJetDensity_output_support s pivot free (allocatedNonkernelExponent B j)
    input fixed (allocatedPartitionedInput_frozen_bound B U basis S x u) rows
    (allocatedNonkernelExponent_degree B j)
    (allocatedContinuousProfileCenters (G := G) B R j i ∘ reindex)
    (allocatedContinuousProfileWidths (G := G) B R σ j i ∘ reindex)
    (fun d => allocatedContinuousProfileWidths_pos B hR hσ j i (reindex d)) radius
    (fun d => allocatedContinuousProfile_bound B hR hσ j i hσ1 (reindex d)) y hy z hz
  exact hs

end Continuous

section Integer

variable (i : Fin (n j))
local notation "height" => (basisAxisScale (basis j) i : ℝ)
local notation "heightPos" => Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
local notation "scale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) height
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => scale (s o)) (fun _ => height)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1) (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) heightPos (s o))
  (fun _ => heightPos)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => scale (Subtype.val d)) (fun _ => height))

include hσ in
theorem allocatedIntegerKernelDensity_support_data (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ)
    (hy : ‖y‖ ≤ 1) (z : O → ℝ)
    (hz : (normalizedJetOutputRadius α (AllocatedNonkernelCoefficient (G := G) B j)
      pivot free (j.val+1) radius radius : ℝ) < ‖z‖) :
    allocatedIntegerKernelDensity B U basis S j i x u rows s hA y z = 0 := by
  have hs := affineSelectedJetDensity_output_support s pivot free (allocatedNonkernelExponent B j)
    input fixed (allocatedPartitionedInput_frozen_bound B U basis S x u) rows
    (allocatedNonkernelExponent_degree B j)
    (allocatedIntegerProfileCenters (G := G) B R j i ∘ reindex)
    (allocatedIntegerProfileWidths (G := G) B R σ j i ∘ reindex)
    (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)) radius
    (fun d => allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d)) y hy z hz
  exact hs

end Integer
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [dG : DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m,
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "radius" j => NNReal.mk (R j) (le_of_lt (hR j))
local notation "delta" j => NNReal.mk
  (allocatedUnitProfileWidth (R j) (σ j)
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (Fin.val j+1))))
  (le_of_lt (allocatedUnitProfileWidth_pos (hR j) (hσ j) _))
local notation "outputRadius" => Real.exp (allocatedJetSupportLog (G := G) B α O P)

include hR hσ hM hi hP hMP hRP hRi hσi hcount

theorem allocatedKernelRadius_bound (j : Fin m) {H : ℝ} (hH : 0 < H) :
    let E := normalizedPivotEquiv _ (hA j)
      (fun o => kernelJetCoefficientScale G (j.val+1) S.value H (s j o)) (fun _ => H)
      (fun o => kernelJetCoefficientScale_pos G (j.val+1) (Nat.cast_pos.mpr S.positive) hH (s j o))
      (fun _ => hH)
    let F := matrixSupCLM (normalizedIntegerColumns
      (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) (rows j)) (s j))
      (fun d => kernelJetCoefficientScale G (j.val+1) S.value H d.val) (fun _ => H))
    (normalizedJetOutputRadius α (AllocatedNonkernelCoefficient (G := G) B j) E F
      (j.val+1) (radius j) (radius j) : ℝ) ≤ outputRadius := by
  have hp' : 0 ≤ 4*(P+8) := by positivity
  have hPP : Real.exp P ≤ Real.exp (4*(P+8)) := Real.exp_le_exp.mpr (by linarith)
  have hf := fixedKernel_family_output_bound (N := AllocatedNonkernelCoefficient (G := G) B)
    S.positive hM x (fun j : Fin m => j.val+1) rows s hA hi
    (fun j => delta j) (fun j => radius j)
    (fun j => allocatedUnitProfileWidth_pos (hR j) (hσ j) _) hp' (hMP.trans hPP)
    (fun j => (hRP j).trans hPP)
    (fun j => allocatedUnitProfileWidth_inverse_exp _ hP (hR j) (hσ j) (hRi j) (hσi j) (hcount j))
    (fun _ => H) (fun _ => hH)
  have hlog := (allocatedDensityLog_bounds (G := G) B α O hP).2.1.trans
    (allocatedJetSupportLog_bounds (G := G) B α O hP).2.1
  exact (NNReal.coe_le_coe.mpr (hf.2.2.2 j)).trans (Real.exp_le_exp.mpr hlog)

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

theorem allocatedContinuousKernelDensity_zero_off_box (hσ1 : ∀ j, σ j ≤ 1)
    (j : Fin m) (i : I j)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ)
    (hy : ‖y‖ ≤ 1) (z : O j → ℝ) (hz : outputRadius < ‖z‖) :
    allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y z = 0 := by
  cases Subsingleton.elim dG (Classical.decEq G)
  have hr := allocatedKernelRadius_bound B U basis hR hσ S x rows s hA hM hi hP hMP hRP hRi hσi hcount j
    (H := 1) zero_lt_one
  have hz' := hr.trans_lt hz
  exact allocatedContinuousKernelDensity_support_data B U basis hR hσ S j x u (rows j) (s j) (hA j) i
    (hσ1 j) y hy z hz'

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedProxyOutputSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [dG : DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "radius" => Real.exp (allocatedJetSupportLog (G := G) B α O P)
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

include hR hσ hM hi hP hMP hRP hRi hσi hcount

theorem allocatedNormalizedLongJetFactor_zero_off_ball (hσ1 : ∀ j, σ j ≤ 1)
    (y : input → ℝ) (hy : ‖y‖ ≤ 1) (a : {a // ¬grid a})
    (z : O a.val.1 → ℝ) (hz : radius < ‖z‖) :
    allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a z = 0 := by
  cases Subsingleton.elim dG (Classical.decEq G)
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    exact allocatedContinuousKernelDensity_zero_off_box B U basis hR hσ S x rows s hA
      hM hi hP hMP hRP hRi hσi hcount u hσ1 j i y hy z hz
  | inr i =>
    have hr := allocatedKernelRadius_bound B U basis hR hσ S x rows s hA
      hM hi hP hMP hRP hRi hσi hcount j
      (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
    exact allocatedIntegerKernelDensity_support_data B U basis hR hσ S j x u
      (rows j) (s j) (hA j) i (hσ1 j) y hy z (hr.trans_lt hz)

theorem allocatedNormalizedLongJetDensity_zero_off_ball (hσ1 : ∀ j, σ j ≤ 1)
    (y : input → ℝ) (hy : ‖y‖ ≤ 1) (v : output → ℝ) (hv : radius < ‖v‖) :
    allocatedNormalizedLongJetDensity B U basis S x u rows s hA y v = 0 :=
  sigmaAxisWeight_zero_outside _ (Real.exp_pos _).le
    (allocatedNormalizedLongJetFactor_zero_off_ball B U basis hR hσ S x rows s hA
      hM hi hP hMP hRP hRi hσi hcount u hσ1 y hy) v hv

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedNormalizedLongJetDensity_zero_off_ball.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedNormalizedLongJetDensity_zero_off_ball.{u_1, u_2, u_3, u_4, u_5, u_6}
