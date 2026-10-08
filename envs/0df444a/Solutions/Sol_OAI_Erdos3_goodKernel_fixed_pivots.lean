-- Prove2me | solution 1 for OAI.Erdos3.goodKernel_fixed_pivots
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:21:44.569993+00:00
-- url     : https://prove2.me/submissions/e0c0c266-a6a2-474f-a61b-d6b86cd87ea9

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BoundedRealPolynomialBasis
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

open scoped BigOperators

theorem boundedRealPolynomial_expansion {K : Type*} [Fintype K]
    (p : MvPolynomial K ℝ) (h : ℕ) (hp : p.totalDegree ≤ h) :
    (∑ e : BoundedIntegerExponent K h,
      MvPolynomial.C (p.coeff e.val) * MvPolynomial.monomial e.val 1) = p := by
  classical
  simp only [MvPolynomial.C_mul_monomial, mul_one]
  ext m
  rw [MvPolynomial.coeff_sum]
  by_cases hm : m.sum (fun _ n => n) ≤ h
  · let e : BoundedIntegerExponent K h := ⟨m, hm⟩
    rw [Finset.sum_eq_single e]
    · simp [e, MvPolynomial.coeff_monomial]
    · intro d _ hde
      have hdm : d.val ≠ m := fun heq => hde (Subtype.ext heq)
      simp [MvPolynomial.coeff_monomial, hdm]
    · simp
  · have hzero : p.coeff m = 0 := by
      apply MvPolynomial.notMem_support_iff.mp
      intro hmem
      exact hm ((MvPolynomial.le_totalDegree hmem).trans hp)
    rw [hzero]
    apply Finset.sum_eq_zero
    intro e _
    have hem : e.val ≠ m := fun heq => hm (heq ▸ e.property)
    simp [MvPolynomial.coeff_monomial, hem]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAffineResidues
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

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

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem realAffineDualPolynomial_eval {α I K : Type*} [Fintype I]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : I → K)
    (n : I → ℝ) (t : Finset α) :
    MvPolynomial.eval (realAffineCube root difference t)
      (realAffineDualPolynomial root selection n) =
        ∑ r ∈ t, ∑ j, n j * difference r (selection j) := by
  simp only [realAffineDualPolynomial, map_sum, map_mul, map_sub,
    MvPolynomial.eval_C, MvPolynomial.eval_X, realAffineCube,
    add_sub_cancel_left, Finset.mul_sum]
  exact Finset.sum_comm

theorem realAffineDualPolynomial_boolean {α I K : Type*}
    [DecidableEq α] [Fintype I]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : I → K)
    (n : α → I → ℝ)
    (hdual : ∀ r s, (∑ j, n r j * difference s (selection j)) =
      if r = s then 1 else 0) (r : α) (t : Finset α) :
    MvPolynomial.eval (realAffineCube root difference t)
      (realAffineDualPolynomial root selection (n r)) = if r ∈ t then 1 else 0 := by
  rw [realAffineDualPolynomial_eval]
  simp only [hdual, Finset.sum_ite_eq]

theorem realAffineDualPolynomial_degree {I K : Type*} [Fintype I]
    (root : K → ℝ) (selection : I → K) (n : I → ℝ) :
    (realAffineDualPolynomial root selection n).totalDegree ≤ 1 := by
  unfold realAffineDualPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_sub_C_le _ _).trans (by simp)

theorem realAffineDualPolynomial_mass {I K : Type*} [Fintype I]
    (root : K → ℝ) (selection : I → K) (n : I → ℝ)
    (hroot : ∀ j, |root (selection j)| ≤ 1) {V : ℝ} (hV : 0 ≤ V)
    (hn : ∀ j, |n j| ≤ V) :
    realPolynomialMass (realAffineDualPolynomial root selection n) ≤
      (Fintype.card I : ℝ) * (2 * V) := by
  unfold realAffineDualPolynomial
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : I, 2 * V := by
      apply Finset.sum_le_sum
      intro j _
      apply (realPolynomialMass_C_mul_le _ _).trans
      have hm : realPolynomialMass
          (MvPolynomial.X (selection j) - MvPolynomial.C (root (selection j))) ≤ 2 := by
        apply (realPolynomialMass_sub_le _ _).trans
        simp only [realPolynomialMass_X, realPolynomialMass_C]
        linarith [hroot j]
      calc
        _ ≤ V * 2 := mul_le_mul (hn j) hm (realPolynomialMass_nonneg _) hV
        _ = 2 * V := mul_comm _ _
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealBooleanInterpolation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem realBooleanInterpolant_eval {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℝ) (s : Finset α) (vertices : Finset α → K → ℝ)
    (hq : ∀ r t, MvPolynomial.eval (vertices t) (q r) = if r ∈ t then 1 else 0)
    (t : Finset α) :
    MvPolynomial.eval (vertices t) (realBooleanInterpolant q s) =
      if s ⊆ t then 1 else 0 := by
  rw [realBooleanInterpolant, map_prod]
  by_cases hst : s ⊆ t
  · rw [if_pos hst]
    exact Finset.prod_eq_one (fun r hr => by rw [hq, if_pos (hst hr)])
  · rw [if_neg hst]
    obtain ⟨r, hrs, hrt⟩ := Finset.not_subset.mp hst
    exact Finset.prod_eq_zero hrs (by rw [hq, if_neg hrt])

theorem realBooleanInterpolant_jet {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℝ) (s : Finset α) (vertices : Finset α → K → ℝ)
    (hq : ∀ r t, MvPolynomial.eval (vertices t) (q r) = if r ∈ t then 1 else 0)
    (row : Finset α) :
    booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
      (realBooleanInterpolant q s)) row = if row = s then 1 else 0 := by
  simp_rw [realBooleanInterpolant_eval q s vertices hq]
  exact booleanCoefficient_monomial s row

theorem realBooleanInterpolant_degree {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℝ) (s : Finset α)
    (hq : ∀ r ∈ s, (q r).totalDegree ≤ 1) :
    (realBooleanInterpolant q s).totalDegree ≤ s.card := by
  apply (MvPolynomial.totalDegree_finsetProd s q).trans
  simpa using Finset.sum_le_sum hq

theorem realBooleanInterpolant_mass {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℝ) (s : Finset α) {H : ℝ} (hH : 1 ≤ H)
    (hq : ∀ r ∈ s, realPolynomialMass (q r) ≤ H) {h : ℕ} (hs : s.card ≤ h) :
    realPolynomialMass (realBooleanInterpolant q s) ≤ H ^ h := by
  apply (realPolynomialMass_prod_le s q).trans
  calc
    _ ≤ ∏ _r ∈ s, H := Finset.prod_le_prod (fun r _ => realPolynomialMass_nonneg (q r)) hq
    _ = H ^ s.card := by simp
    _ ≤ H ^ h := pow_le_pow_right₀ hH hs

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealKernelJetInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem realJetMatrix_apply_coefficients {α K O J : Type*} [DecidableEq α] [Fintype J]
    (basis : J → MvPolynomial K ℝ) (vertices : Finset α → K → ℝ)
    (rows : O → Finset α) (c : J → ℝ) (o : O) :
    (realJetMatrix basis vertices rows *ᵥ c) o =
      booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
        (∑ j, MvPolynomial.C (c j) * basis j)) (rows o) := by
  simp only [map_sum, map_mul, MvPolynomial.eval_C,
    booleanCoefficient_sum, booleanCoefficient_const_mul]
  change (∑ j, realJetMatrix basis vertices rows o j * c j) = _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem boundedDegreeRealJetMatrix_interpolation {α K O : Type*}
    [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℝ) (difference : α → K → ℝ) (h : ℕ) (rows : O → Finset α)
    (p : O → MvPolynomial K ℝ) (hp : ∀ o, (p o).totalDegree ≤ h)
    (hjet : ∀ i j, booleanCoefficient
      (fun t => MvPolynomial.eval (realAffineCube root difference t) (p j)) (rows i) =
        if i = j then 1 else 0) :
    boundedDegreeRealJetMatrix root difference h rows *
      Matrix.of (fun (e : BoundedIntegerExponent K h) j => (p j).coeff e.val) = 1 := by
  ext i j
  change (realJetMatrix _ _ rows *ᵥ
    (fun e : BoundedIntegerExponent K h => (p j).coeff e.val)) i = _
  rw [realJetMatrix_apply_coefficients, boundedRealPolynomial_expansion (p j) h (hp j)]
  exact hjet i j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem realDifferencePivot_inverse_dual {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℝ) (selection : α → K)
    (hd : (realDifferencePivot difference selection).det ≠ 0) (r s : α) :
    (∑ j, (realDifferencePivot difference selection)⁻¹ j r * difference s (selection j)) =
      if r = s then 1 else 0 := by
  have hm := Matrix.mul_nonsing_inv (realDifferencePivot difference selection)
    (isUnit_iff_ne_zero.mpr hd)
  have he := congrFun (congrFun hm s) r
  simpa only [Matrix.mul_apply, realDifferencePivot, Matrix.one_apply, mul_comm, eq_comm] using he

theorem realKernelInterpolant_degree {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K) (s : Finset α) :
    (realKernelInterpolant root difference selection s).totalDegree ≤ s.card :=
  realBooleanInterpolant_degree _ _ (fun _ _ => realAffineDualPolynomial_degree _ _ _)

theorem realKernelInterpolant_jet {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (hd : (realDifferencePivot difference selection).det ≠ 0) (s row : Finset α) :
    booleanCoefficient (fun t => MvPolynomial.eval (realAffineCube root difference t)
      (realKernelInterpolant root difference selection s)) row =
        if row = s then 1 else 0 := by
  apply realBooleanInterpolant_jet
  exact realAffineDualPolynomial_boolean root difference selection _
    (realDifferencePivot_inverse_dual difference selection hd)

theorem realKernelInterpolant_mass {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (hroot : ∀ j, |root (selection j)| ≤ 1)
    (hentry : ∀ i j, |difference i (selection j)| ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) (hd : κ ≤ |(realDifferencePivot difference selection).det|)
    {h : ℕ} (s : Finset α) (hs : s.card ≤ h) :
    realPolynomialMass (realKernelInterpolant root difference selection s) ≤
      (1 + (Fintype.card α : ℝ) * (2 * ((Fintype.card α).factorial / κ))) ^ h := by
  apply realBooleanInterpolant_mass _ s (le_add_of_nonneg_right (by positivity)) _ hs
  intro r _
  have hi : ∀ j, |(realDifferencePivot difference selection)⁻¹ j r| ≤
      (Fintype.card α).factorial / κ := by
    intro j
    simpa only [one_pow, mul_one] using
      matrix_inverse_entry_abs_le (realDifferencePivot difference selection) hentry hκ hd j r
  exact (realAffineDualPolynomial_mass root selection _ hroot (by positivity) hi).trans
    (by linarith)

end Erdos3

end

section

namespace Erdos3

theorem realKernelJetRightInverse_spec {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (hd : (realDifferencePivot difference selection).det ≠ 0)
    (h : ℕ) (rows : O → Finset α) (hr : Function.Injective rows)
    (hrows : ∀ o, (rows o).card ≤ h) :
    boundedDegreeRealJetMatrix root difference h rows *
      realKernelJetRightInverse root difference selection h rows = 1 := by
  apply boundedDegreeRealJetMatrix_interpolation
  · intro o
    exact (realKernelInterpolant_degree root difference selection (rows o)).trans (hrows o)
  · intro i j
    rw [realKernelInterpolant_jet root difference selection hd]
    simp only [hr.eq_iff]

theorem realKernelJetRightInverse_entry_bound {α K O : Type*}
    [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (hroot : ∀ j, |root (selection j)| ≤ 1)
    (hentry : ∀ i j, |difference i (selection j)| ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) (hd : κ ≤ |(realDifferencePivot difference selection).det|)
    (h : ℕ) (rows : O → Finset α) (hrows : ∀ o, (rows o).card ≤ h)
    (e : BoundedIntegerExponent K h) (o : O) :
    |realKernelJetRightInverse root difference selection h rows e o| ≤
      (1 + (Fintype.card α : ℝ) * (2 * ((Fintype.card α).factorial / κ))) ^ h := by
  exact (realPolynomialMass_coeff_le _ _).trans
    (realKernelInterpolant_mass root difference selection hroot hentry hκ hd (rows o) (hrows o))

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedRightInverseMinor
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem submatrix_columns_injective_of_det_ne_zero {I J : Type*}
    [Fintype I] [DecidableEq I] (A : Matrix I J ℝ) (p : I → J)
    (hp : (A.submatrix id p).det ≠ 0) : Function.Injective p := by
  intro i j hij
  by_contra hne
  apply hp
  exact Matrix.det_zero_of_column_eq hne (fun k => by simp [Matrix.submatrix_apply, hij])

theorem boundedRightInverse_exists_minor {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Nonempty J]
    (A : Matrix I J ℝ) (B : Matrix J I ℝ) (hAB : A * B = 1)
    {Q : ℝ} (hQ : 0 < Q) (hB : ∀ j i, |B j i| ≤ Q) :
    ∃ p : I → J, Function.Injective p ∧
      1 / ((Fintype.card (I → J) : ℝ) * Q ^ Fintype.card I) ≤
        |(A.submatrix id p).det| := by
  classical
  have hM : (0 : ℝ) < Fintype.card (I → J) := by exact_mod_cast Fintype.card_pos
  have hpow : 0 < Q ^ Fintype.card I := pow_pos hQ _
  have hsum : 1 ≤ ∑ p : I → J, |(A.submatrix id p).det| * Q ^ Fintype.card I := by
    calc
      1 = |∑ p : I → J, (A.submatrix id p).det * ∏ i, B (p i) i| := by
        rw [← rectangular_det_expansion, hAB, Matrix.det_one, abs_one]
      _ ≤ ∑ p : I → J, |(A.submatrix id p).det * ∏ i, B (p i) i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p _
        rw [abs_mul, Finset.abs_prod]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hprod : (∏ i : I, |B (p i) i|) ≤ ∏ _i : I, Q :=
          Finset.prod_le_prod (fun index _ => abs_nonneg (B (p index) index))
            (fun index _ => hB (p index) index)
        simpa only [Finset.prod_const, Finset.card_univ] using hprod
  have hconstant : (∑ _p : I → J, (Fintype.card (I → J) : ℝ)⁻¹) = 1 := by
    simp
  obtain ⟨p, _, hp⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty
    (hconstant.trans_le hsum)
  have hdet : 1 / ((Fintype.card (I → J) : ℝ) * Q ^ Fintype.card I) ≤
      |(A.submatrix id p).det| := by
    have := (div_le_iff₀ hpow).mpr hp
    simpa only [one_div, mul_inv_rev, div_eq_mul_inv, one_mul, mul_comm] using this
  refine ⟨p, submatrix_columns_injective_of_det_ne_zero A p ?_, hdet⟩
  exact abs_pos.mp ((by positivity : 0 <
    1 / ((Fintype.card (I → J) : ℝ) * Q ^ Fintype.card I)).trans_le hdet)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialPivotNormalization
namespace OAI

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

theorem normalizedPivotEquiv_inverse_eq {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (S P : I → ℝ)
    (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap =
      (matrixSupCLM (normalizedIntegerPivot A S P)).inverse := by
  rw [← normalizedPivotEquiv_coe A hA S P hS hP, ContinuousLinearMap.inverse_equiv]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarCubeMinorPolynomial
namespace OAI

section

namespace Erdos3

theorem scalarCubeMinorPolynomial_grid_eval {I J : Type*} [Fintype I] [DecidableEq I]
    {N L : ℕ} (e : J × Option I ≃ Fin N) (s : I → J) (x : J → IntegerScalarCubeBox I L) :
    MvPolynomial.eval (fun i => (scalarCubeGrid e x i : ℝ) / L) (scalarCubeMinorPolynomial e s) =
      normalizedScalarCubeMinor s x := by
  rw [scalarCubeMinorPolynomial, coordinateMatrixPolynomial_eval]
  let A := (scalarCubeDifferenceMatrix x).submatrix id s
  have hm : ((fun i j => (scalarCubeGrid e x (e (s j, some i)) : ℝ) / L) : Matrix I I ℝ) =
      (L : ℝ)⁻¹ • A.map (Int.castRingHom ℝ) := by
    ext i j
    simp [A, scalarCubeGrid, scalarCubeDifferenceMatrix, sampledColumnMatrix,
      Matrix.submatrix_apply, div_eq_mul_inv, mul_comm]
  have hcast : (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) :=
    ((Int.castRingHom ℝ).map_det A).symm
  rw [hm, Matrix.det_smul, hcast, inv_pow]
  change ((L : ℝ) ^ Fintype.card I)⁻¹ * (A.det : ℝ) = (A.det : ℝ) / (L : ℝ) ^ Fintype.card I
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI

namespace Erdos3

theorem normalizedScalarCubePivot_det {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {L : ℕ}
    (s : I → J) (x : J → IntegerScalarCubeBox I L) :
    (normalizedScalarCubePivot s x).det = normalizedScalarCubeMinor s x := by
  let e := Fintype.equivFin (J × Option I)
  have h := scalarCubeMinorPolynomial_grid_eval e s x
  rw [scalarCubeMinorPolynomial, coordinateMatrixPolynomial_eval] at h
  change Matrix.det (fun i j => ((x (s j) (some i) : ℤ) : ℝ) / (L : ℝ)) = _
  simpa only [scalarCubeGrid, e.symm_apply_apply] using h

end Erdos3

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

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

theorem realKernelJet_exists_minor {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (hroot : ∀ j, |root (selection j)| ≤ 1)
    (hentry : ∀ i j, |difference i (selection j)| ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) (hd : κ ≤ |(realDifferencePivot difference selection).det|)
    (h : ℕ) (rows : O → Finset α) (hr : Function.Injective rows)
    (hrows : ∀ o, (rows o).card ≤ h) :
    ∃ p : O → BoundedIntegerExponent K h, Function.Injective p ∧
      kernelJetMinorThreshold (Fintype.card α) (Fintype.card K) (Fintype.card O) h κ ≤
        |((boundedDegreeRealJetMatrix root difference h rows).submatrix id p).det| := by
  classical
  let Q := kernelJetInterpolationAllowance (Fintype.card α) h κ
  have hQ : 0 < Q := kernelJetInterpolationAllowance_pos _ _ hκ
  have hdet : (realDifferencePivot difference selection).det ≠ 0 :=
    abs_pos.mp (hκ.trans_le hd)
  obtain ⟨p, hp, hminor⟩ := boundedRightInverse_exists_minor
    (boundedDegreeRealJetMatrix root difference h rows)
    (realKernelJetRightInverse root difference selection h rows)
    (realKernelJetRightInverse_spec root difference selection hdet h rows hr hrows)
    hQ (realKernelJetRightInverse_entry_bound root difference selection hroot hentry hκ hd h rows hrows)
  refine ⟨p, hp, le_trans ?_ hminor⟩
  have hc : (Fintype.card (BoundedIntegerExponent K h) : ℝ) ≤
      ((Fintype.card K : ℝ) + 1) ^ h := by
    exact_mod_cast boundedIntegerExponent_card_le K h
  have hcard : (Fintype.card (O → BoundedIntegerExponent K h) : ℝ) ≤
      (((Fintype.card K : ℝ) + 1) ^ h) ^ Fintype.card O := by
    simp only [Fintype.card_fun, Nat.cast_pow]
    exact pow_le_pow_left₀ (by positivity) hc _
  have hpos : (0 : ℝ) < Fintype.card (O → BoundedIntegerExponent K h) := by
    exact_mod_cast Fintype.card_pos
  change 1 / ((((Fintype.card K : ℝ) + 1) ^ h) * Q) ^ Fintype.card O ≤ _
  rw [mul_pow]
  apply one_div_le_one_div_of_le (mul_pos hpos (pow_pos hQ _))
  exact mul_le_mul_of_nonneg_right hcard (pow_nonneg hQ.le _)

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

theorem integerPivot_det_ne_zero_of_normalized {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (hd : (normalizedIntegerPivot A S P).det ≠ 0) : A.det ≠ 0 := by
  intro hz
  have he := normalizedIntegerPivot_abs_det A S P hS hP
  rw [hz] at he
  simp only [Int.natAbs_zero, Nat.cast_zero, zero_mul, zero_div] at he
  exact hd (abs_eq_zero.mp he)

theorem normalizedBoundedIntegerJet_exists_pivot {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℤ) (difference : Matrix α K ℤ) (T : K → ℝ) (hT : ∀ k, 0 < T k)
    (selection : α → K)
    (hroot : ∀ k, |(root k : ℝ) / T k| ≤ 1)
    (hentry : ∀ i k, |(difference i k : ℝ) / T k| ≤ 1)
    {κ H : ℝ} (hκ : 0 < κ) (hH : 0 < H)
    (hd : κ ≤ |(realDifferencePivot (fun i k => (difference i k : ℝ) / T k) selection).det|)
    (h : ℕ) (rows : O → Finset α) (hr : Function.Injective rows)
    (hrows : ∀ o, (rows o).card ≤ h) :
    ∃ p : O → BoundedIntegerExponent K h, Function.Injective p ∧
      ((boundedDegreeIntegerJetMatrix root difference h rows).submatrix id p).det ≠ 0 ∧
      (matrixSupCLM (normalizedIntegerPivot
        ((boundedDegreeIntegerJetMatrix root difference h rows).submatrix id p)
        (fun o => H / monomialScale T (p o).val) (fun _ => H))).IsInvertible ∧
      ‖(matrixSupCLM (normalizedIntegerPivot
        ((boundedDegreeIntegerJetMatrix root difference h rows).submatrix id p)
        (fun o => H / monomialScale T (p o).val) (fun _ => H))).inverse‖ ≤
          kernelJetInverseAllowance (Fintype.card α) (Fintype.card K) (Fintype.card O) h κ := by
  obtain ⟨p, hp, hminor⟩ := realKernelJet_exists_minor
    (fun k => (root k : ℝ) / T k) (fun i k => (difference i k : ℝ) / T k) selection
    (fun j => hroot (selection j)) (fun i j => hentry i (selection j)) hκ hd h rows hr hrows
  have he := congrArg (fun A : Matrix O (BoundedIntegerExponent K h) ℝ => A.submatrix id p)
    (normalizedBoundedIntegerJetMatrix_eq root difference h rows T hH.ne')
  rw [normalizedIntegerColumns_submatrix] at he
  have hn := matrixSupCLM_inverse_norm_le
    ((boundedDegreeRealJetMatrix (fun k => (root k : ℝ) / T k)
      (fun i k => (difference i k : ℝ) / T k) h rows).submatrix id p)
    (kernelJetEntryAllowance_pos (Fintype.card α) h).le
    (fun i j => boundedDegreeRealJetMatrix_entry_bound _ _ hroot hentry h rows i (p j))
    (kernelJetMinorThreshold_pos _ _ _ _ hκ) hminor
  rw [← he] at hn
  refine ⟨p, hp, ?_, hn⟩
  apply integerPivot_det_ne_zero_of_normalized _ _ _
    (fun o => div_pos hH (monomialScale_pos T hT (p o).val)) (fun _ => hH)
  rw [he]
  exact abs_pos.mp ((kernelJetMinorThreshold_pos _ _ _ _ hκ).trans_le hminor)

open scoped Matrix

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

theorem goodScalarKernelTuple_integer_jet_pivot {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L B : ℕ} {κ H : ℝ}
    (hL : 0 < L) (selection : I → J) (hκ : 0 < κ) (hH : 0 < H)
    (x : J → IntegerScalarCubeBox I L) (hx : GoodScalarKernelTuple selection κ B x)
    (h : ℕ) (rows : O → Finset I) (hr : Function.Injective rows)
    (hrows : ∀ o, (rows o).card ≤ h) :
    ∃ p : O → BoundedIntegerExponent J h, Function.Injective p ∧
      ((scalarKernelIntegerJet x h rows).submatrix id p).det ≠ 0 ∧
      (matrixSupCLM (normalizedIntegerPivot ((scalarKernelIntegerJet x h rows).submatrix id p)
        (fun o => H / monomialScale (fun _ => (L : ℝ)) (p o).val) (fun _ => H))).IsInvertible ∧
      ‖(matrixSupCLM (normalizedIntegerPivot ((scalarKernelIntegerJet x h rows).submatrix id p)
        (fun o => H / monomialScale (fun _ => (L : ℝ)) (p o).val) (fun _ => H))).inverse‖ ≤
          kernelJetInverseAllowance (Fintype.card I) (Fintype.card J) (Fintype.card O) h κ := by
  have hc (j : J) (i : Option I) : |(x j i : ℝ) / L| ≤ 1 :=
    (norm_le_pi_norm (fun i => (x j i : ℝ) / L) i).trans
      (integerScalarCubeBox_normalized_norm_le hL (x j))
  have hd : κ ≤ |(realDifferencePivot
      (fun i j => (scalarCubeDifferenceMatrix x i j : ℝ) / L) selection).det| := by
    change κ ≤ |(normalizedScalarCubePivot selection x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  exact normalizedBoundedIntegerJet_exists_pivot _ _ (fun _ => (L : ℝ))
    (fun _ => by exact_mod_cast hL) selection (fun j => hc j none)
    (fun i j => hc j (some i)) hκ hH hd h rows hr hrows

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

theorem goodScalarKernelTuple_fixed_jet_pivot {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L B : ℕ} {κ : ℝ}
    (hL : 0 < L) (selection : I → J) (hκ : 0 < κ)
    (x : J → IntegerScalarCubeBox I L) (hx : GoodScalarKernelTuple selection κ B x)
    (h : ℕ) (rows : O → Finset I) (hr : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ h) :
    ∃ s : O ↪ BoundedIntegerExponent J h,
      ((scalarKernelIntegerJet x h rows).submatrix id s).det ≠ 0 ∧
      ∀ H : ℝ, H ≠ 0 →
        ‖(matrixSupCLM (normalizedIntegerPivot ((scalarKernelIntegerJet x h rows).submatrix id s)
          (fun o => kernelJetCoefficientScale J h L H (s o)) (fun _ => H))).inverse‖ ≤
            kernelJetInverseAllowance (Fintype.card I) (Fintype.card J) (Fintype.card O) h κ := by
  obtain ⟨p, hp, hd, _, hn⟩ := goodScalarKernelTuple_integer_jet_pivot hL selection hκ
    (show (0 : ℝ) < 1 by norm_num) x hx h rows hr hrows
  refine ⟨⟨p, hp⟩, hd, fun H hH => ?_⟩
  change ‖(matrixSupCLM (normalizedIntegerPivot ((scalarKernelIntegerJet x h rows).submatrix id p)
    (fun o => kernelJetCoefficientScale J h L H (p o)) (fun _ => H))).inverse‖ ≤ _
  rw [normalized_scalarKernel_pivot x h rows p hH]
  change ‖(matrixSupCLM (normalizedIntegerPivot ((scalarKernelIntegerJet x h rows).submatrix id p)
    (fun o => kernelJetCoefficientScale J h L 1 (p o)) (fun _ => 1))).inverse‖ ≤ _ at hn
  rwa [normalized_scalarKernel_pivot x h rows p one_ne_zero] at hn

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget
namespace OAI

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

theorem goodKernel_fixed_pivots {Q α J : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    {O : Q → Type*} [∀ q, Fintype (O q)] [∀ q, DecidableEq (O q)]
    {L B : ℕ} {κ : ℝ} (hL : 0 < L) (selection : α ↪ J) (hκ : 0 < κ)
    (x : J → IntegerScalarCubeBox α L) (hx : GoodScalarKernelTuple selection κ B x)
    (degree : Q → ℕ) (rows : ∀ q, O q → Finset α)
    (hinj : ∀ q, Function.Injective (rows q)) (hrows : ∀ q i, (rows q i).card ≤ degree q) :
    ∃ s : ∀ q, O q ↪ BoundedIntegerExponent J (degree q),
    ∃ hs : ∀ q, ((scalarKernelIntegerJet x (degree q) (rows q)).submatrix id (s q)).det ≠ 0,
      ∀ q, ‖(scalarKernelFixedPivot hL x (degree q) (rows q) (s q) (hs q)).symm.toContinuousLinearMap‖ ≤
        kernelJetInverseAllowance (Fintype.card α) (Fintype.card J) (Fintype.card (O q)) (degree q) κ := by
  classical
  have hc (q) := goodScalarKernelTuple_fixed_jet_pivot hL selection hκ x hx
    (degree q) (rows q) (hinj q) (hrows q)
  choose s hs hi using hc
  refine ⟨s, hs, fun q => ?_⟩
  rw [scalarKernelFixedPivot, normalizedPivotEquiv_inverse_eq]
  exact hi q 1 one_ne_zero

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.goodKernel_fixed_pivots.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.goodKernel_fixed_pivots.{u_1, u_2, u_3, u_4}
