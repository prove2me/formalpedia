-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.homogeneous_span_representation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:21:02.586156+00:00
-- url     : https://prove2.me/submissions/ed951182-5ecc-408a-ae5d-dd50cb351fbd

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_mul

open scoped BigOperators

theorem solution
    {d k : Nat} (w : Fin d → Real) (D E : Real)
    (f : Fin k → MvPolynomial (Fin d) Complex)
    (hf : ∀ j, MvPolynomial.IsWeightedHomogeneous w (f j) D)
    (p : MvPolynomial (Fin d) Complex)
    (hp : MvPolynomial.IsWeightedHomogeneous w p E)
    (hmem : p ∈ Ideal.span (Set.range f)) :
    ∃ q : Fin k → MvPolynomial (Fin d) Complex,
      p = ∑ j : Fin k, q j * f j ∧
        ∀ j, MvPolynomial.IsWeightedHomogeneous w (q j) (E - D) := by
  classical
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  refine ⟨fun j => MvPolynomial.weightedHomogeneousComponent w (E - D) (c j), ?_, ?_⟩
  · calc
      p = MvPolynomial.weightedHomogeneousComponent w E p :=
        hp.weightedHomogeneousComponent_same.symm
      _ = MvPolynomial.weightedHomogeneousComponent w E (∑ j : Fin k, c j * f j) :=
        congrArg (MvPolynomial.weightedHomogeneousComponent w E) hc.symm
      _ = ∑ j : Fin k, MvPolynomial.weightedHomogeneousComponent w E (c j * f j) :=
        map_sum (MvPolynomial.weightedHomogeneousComponent w E) _ _
      _ = ∑ j : Fin k,
          MvPolynomial.weightedHomogeneousComponent w (E - D) (c j) * f j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact OAI.PiExponent.FormalInterpolation.weighted_component_mul
          w D E (c j) (f j) (hf j)
  · intro j
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _