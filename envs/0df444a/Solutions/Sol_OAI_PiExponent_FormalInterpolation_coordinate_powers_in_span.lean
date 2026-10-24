-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_powers_in_span
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T11:45:57.558412+00:00
-- url     : https://prove2.me/submissions/d5d8766f-73b7-4106-a272-6fd05ae00505

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_span_mem_weightedHomogeneousComponent
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_graded_quotient_coordinate_nilpotent

open scoped BigOperators

theorem solution {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D) (m : Nat)
    (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (hquot : Module.Finite ℂ
      (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range p))) :
    ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n ∈ Ideal.span (Set.range p) := by
  have hcomponents :=
    OAI.PiExponent.FormalInterpolation.span_mem_weightedHomogeneousComponent
      w (D : ℚ) (by exact_mod_cast hD) p hp
  exact
    OAI.PiExponent.FormalInterpolation.finite_graded_quotient_coordinate_nilpotent
      w (fun i => by exact_mod_cast hw i) (Ideal.span (Set.range p))
      (by
        intro f hf r
        exact hcomponents f hf r)
      hquot
