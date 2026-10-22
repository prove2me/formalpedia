-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_poles_invariant_sub_const
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:24:22.301479+00:00
-- url     : https://prove2.me/submissions/d6dc7855-9043-4441-92df-62848444a55a

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_transcendental_finiteDimensional_adjoin_of_trdeg_eq_one
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finsum_max_neg_polynomialCurveOrder_eq_finrank
import Mathlib.Tactic

open scoped BigOperators
open IntermediateField
open OAI.PiExponent.FormalInterpolation
open AlgebraicCurve

theorem solution
    {E : Type} [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (z : E)
    (hz : Transcendental Complex z) (b : Complex) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      max (-(polynomialCurveOrder nu (z - algebraMap Complex E b) : Real)) 0) =
      ∑ᶠ nu : PolynomialCurvePlace E,
        max (-(polynomialCurveOrder nu z : Real)) 0 := by
  obtain ⟨t, ht, hfin⟩ :=
    exists_transcendental_finiteDimensional_adjoin_of_trdeg_eq_one htrdeg
  haveI : FiniteDimensional (adjoin Complex ({t} : Set E)) E := hfin
  have hfinz : FiniteDimensional (adjoin Complex ({z} : Set E)) E :=
    finiteDimensional_adjoin_of_transcendental (K := Complex) (F := E) t hz
  set zb := z - algebraMap Complex E b
  have hadj : adjoin Complex ({zb} : Set E) = adjoin Complex ({z} : Set E) := by
    refine le_antisymm ?_ ?_
    · rw [adjoin_simple_le_iff]
      exact sub_mem (mem_adjoin_simple_self Complex z)
        (Subalgebra.algebraMap_mem (adjoin Complex ({z} : Set E)).toSubalgebra b)
    · rw [adjoin_simple_le_iff]
      have hzmem : z ∈ adjoin Complex ({zb} : Set E) := by
        have hzeq : z = zb + algebraMap Complex E b := by simp [zb]
        rw [hzeq]
        exact add_mem (mem_adjoin_simple_self Complex zb)
          (Subalgebra.algebraMap_mem (adjoin Complex ({zb} : Set E)).toSubalgebra b)
      exact hzmem
  have hzb : Transcendental Complex zb := by
    intro h
    refine hz ?_
    have hb : IsAlgebraic Complex (algebraMap Complex E b) := isAlgebraic_algebraMap b
    have hint : IsIntegral Complex z := by
      have hzeq : z = zb + algebraMap Complex E b := by simp [zb]
      rw [hzeq]
      exact IsIntegral.add (IsAlgebraic.isIntegral h) (IsAlgebraic.isIntegral hb)
    exact hint.isAlgebraic
  have hfinzb : FiniteDimensional (adjoin Complex ({zb} : Set E)) E := by
    rwa [hadj]
  rw [finsum_max_neg_polynomialCurveOrder_eq_finrank zb hzb hfinzb,
    finsum_max_neg_polynomialCurveOrder_eq_finrank z hz hfinz]
  have hfr : Module.finrank (adjoin Complex ({zb} : Set E)) E =
      Module.finrank (adjoin Complex ({z} : Set E)) E := by
    rw [hadj]
  exact_mod_cast hfr
