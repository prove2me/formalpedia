-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomial_curve_mass_le_zero_divisor
-- status  : ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:34:19.10805+00:00
-- url     : https://prove2.me/submissions/e3db4083-73f9-4b50-ab15-6a9dbe27fd80

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution {E : Type} [Field E] [Algebra Complex E]
    (f : E) (a r : Real) (ha : 0 < a) (hr : 0 < r)
    (b : PolynomialCurvePlace E → Real) (hb : ∀ nu, 0 ≤ b nu)
    (hlocal : ∀ nu, 0 < b nu →
      a * b nu ≤ r * (polynomialCurveOrder nu f : Real))
    (hpositiveFinite :
      {nu : PolynomialCurvePlace E | 0 < polynomialCurveOrder nu f}.Finite) :
    a * (∑ᶠ nu : PolynomialCurvePlace E, b nu) ≤
      r * (∑ᶠ nu : PolynomialCurvePlace E,
        max (polynomialCurveOrder nu f : Real) 0) := by
  classical
  have hb_support : Set.Finite {nu | b nu ≠ 0} := by
    refine hpositiveFinite.subset ?_
    intro nu hnu
    have hbpos : 0 < b nu := lt_of_le_of_ne (hb nu) (Ne.symm hnu)
    have hbound := hlocal nu hbpos
    have : 0 < (polynomialCurveOrder nu f : Real) := by
      by_contra h
      push_neg at h
      have hnonpos : r * (polynomialCurveOrder nu f : Real) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hr) h
      have hab : 0 < a * b nu := mul_pos ha hbpos
      linarith [hab, hbound, hnonpos]
    exact_mod_cast this
  have hmax_support :
      Set.Finite {nu | max (polynomialCurveOrder nu f : Real) 0 ≠ 0} := by
    refine hpositiveFinite.subset ?_
    intro nu hnu
    have hposMax : 0 < max (polynomialCurveOrder nu f : Real) 0 :=
      lt_of_le_of_ne (le_max_right _ _) (Ne.symm hnu)
    have : 0 < (polynomialCurveOrder nu f : Real) :=
      (lt_max_iff.mp hposMax).resolve_right (lt_irrefl _)
    exact_mod_cast this
  let s := hb_support.toFinset ∪ hmax_support.toFinset
  have hb_sub : Function.support b ⊆ ↑s := by
    intro nu hnu
    simp only [Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union, s]
    left
    simpa [Function.mem_support] using hnu
  have hmax_sub :
      Function.support (fun nu => max (polynomialCurveOrder nu f : Real) 0) ⊆ ↑s := by
    intro nu hnu
    simp only [Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union, s]
    right
    simpa [Function.mem_support] using hnu
  have hb_sum : ∑ᶠ nu, b nu = ∑ nu ∈ s, b nu :=
    finsum_eq_finsetSum_of_support_subset b hb_sub
  have hmax_sum :
      ∑ᶠ nu, max (polynomialCurveOrder nu f : Real) 0 =
        ∑ nu ∈ s, max (polynomialCurveOrder nu f : Real) 0 :=
    finsum_eq_finsetSum_of_support_subset _ hmax_sub
  rw [hb_sum, hmax_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro nu _
  by_cases hbpos : 0 < b nu
  · have hbound := hlocal nu hbpos
    have hord : 0 < (polynomialCurveOrder nu f : Real) := by
      by_contra h
      push_neg at h
      have hnonpos : r * (polynomialCurveOrder nu f : Real) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hr) h
      have hab : 0 < a * b nu := mul_pos ha hbpos
      linarith [hab, hbound, hnonpos]
    have hmaxEq :
        max (polynomialCurveOrder nu f : Real) 0 =
          (polynomialCurveOrder nu f : Real) := max_eq_left (le_of_lt hord)
    rw [hmaxEq]
    exact hbound
  · have hb0 : b nu = 0 := le_antisymm (le_of_not_gt hbpos) (hb nu)
    rw [hb0, mul_zero]
    exact mul_nonneg (le_of_lt hr) (le_max_right _ _)
