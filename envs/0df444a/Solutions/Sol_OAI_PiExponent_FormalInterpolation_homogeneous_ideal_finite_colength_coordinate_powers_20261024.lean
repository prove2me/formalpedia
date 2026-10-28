-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.homogeneous_ideal_finite_colength_coordinate_powers_20261024
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T15:22:43.117972+00:00
-- url     : https://prove2.me/submissions/deeb3b71-0b57-4662-9c36-580aff8a637e

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_span_components_mem_20261024
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_coordinate_power_relation_20261024
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_component_relation_extracts_coordinate_power_20261024

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (q : Rat) (hq : 0 < q) (S : Set (MvPolynomial (Fin d) Complex))
    (hhom : ∀ p ∈ S, ∃ g,
      p = MvPolynomial.weightedHomogeneousComponent
        (fun j => (w j : Rat)) q g)
    (hfinite : Module.Finite Complex
      (MvPolynomial (Fin d) Complex ⧸ Ideal.span S)) :
    ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      MvPolynomial.X i ^ n ∈ Ideal.span S := by
  intro i
  obtain ⟨N, c, hc, hrel⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_quotient_coordinate_power_relation_20261024
      (Ideal.span S) hfinite i
  exact
    OAI.PiExponent.FormalInterpolation.component_relation_extracts_coordinate_power_20261024
      w hw (Ideal.span S)
      (OAI.PiExponent.FormalInterpolation.span_components_mem_20261024 w q S hhom)
      i ⟨N, c, hc, hrel⟩