-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_aeval_le_of_support_monomials
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:32:05.018759+00:00
-- url     : https://prove2.me/submissions/42ac8d52-90eb-4170-9ceb-5ffac1169779

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

namespace S38SM

variable {E : Type} [Field E] [Algebra Complex E]

lemma le_val_sum {ι : Type} (nu : PolynomialCurvePlace E) (s : Finset ι) (t : ι → E)
    (g : WithTop Int) (h : ∀ a ∈ s, g ≤ nu.1 (t a)) : g ≤ nu.1 (∑ a ∈ s, t a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddValuation.map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact AddValuation.map_le_add _ (h a (Finset.mem_insert_self a s))
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

end S38SM

open S38SM in
theorem solution
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (P : MvPolynomial (Fin d) Complex) (C : Real) (hC : 0 ≤ C)
    (hterm : ∀ a ∈ P.support,
      max 0 (-(polynomialCurveOrder nu
        (MvPolynomial.aeval x (MvPolynomial.monomial a (P.coeff a))) : Real)) ≤ C) :
    max 0 (-(polynomialCurveOrder nu (MvPolynomial.aeval x P) : Real)) ≤ C := by
  set m : Int := -⌊C⌋ with hm
  have key : ∀ y : E, ((m : Int) : WithTop Int) ≤ nu.1 y →
      max 0 (-(polynomialCurveOrder nu y : Real)) ≤ C := by
    intro y hy
    apply max_le hC
    unfold polynomialCurveOrder
    generalize hv : nu.1 y = v at hy
    induction v using WithTop.recTopCoe with
    | top => simpa using hC
    | coe z =>
      rw [WithTop.untop₀_coe]
      have h1 : m ≤ z := WithTop.coe_le_coe.mp hy
      have h2 : ((⌊C⌋ : Int) : Real) ≤ C := Int.floor_le C
      have h3 : (m : Real) ≤ z := by exact_mod_cast h1
      rw [hm] at h3; push_cast at h3; linarith
  have back : ∀ y : E, max 0 (-(polynomialCurveOrder nu y : Real)) ≤ C →
      ((m : Int) : WithTop Int) ≤ nu.1 y := by
    intro y hy
    have hy' := (le_max_right _ _).trans hy
    unfold polynomialCurveOrder at hy'
    generalize hv : nu.1 y = v at hy'
    induction v using WithTop.recTopCoe with
    | top => exact le_top
    | coe z =>
      rw [WithTop.untop₀_coe] at hy'
      apply WithTop.coe_le_coe.mpr
      have : -C ≤ (z : Real) := by linarith
      have h4 : -(z : Int) ≤ ⌊C⌋ := Int.le_floor.mpr (by push_cast; linarith)
      rw [hm]; omega
  apply key
  have hP : P = ∑ a ∈ P.support, MvPolynomial.monomial a (P.coeff a) :=
    (MvPolynomial.support_sum_monomial_coeff P).symm
  rw [hP, map_sum]
  apply le_val_sum
  intro a ha
  exact back _ (hterm a ha)
