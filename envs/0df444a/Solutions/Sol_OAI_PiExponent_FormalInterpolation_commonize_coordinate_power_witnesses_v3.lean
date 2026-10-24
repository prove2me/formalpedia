-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.commonize_coordinate_power_witnesses_v3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:37:05.105185+00:00
-- url     : https://prove2.me/submissions/19278546-b9db-4562-9507-527e74c1d42e

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_commonize_coordinate_power_witnesses

open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (eps : Real) (heps : 0 < eps)
    (hcoord : ∀ i : Fin d, ∃ s n : Nat, 0 < s ∧ 0 < n ∧
      MvPolynomial.X i ^ n ∈ I ^ s ∧
      (n : Real) * (w i : Real) < (s : Real) * ((rho : Real) + eps / 2)) :
    ∃ s : Nat, 0 < s ∧ ∃ n : Fin d → Nat,
      (∀ i, 0 < n i) ∧
      (∀ i, MvPolynomial.X i ^ n i ∈ I ^ s) ∧
      (∀ i, (n i : Real) * (w i : Real) <
        (s : Real) * ((rho : Real) + eps / 2)) := by
  exact OAI.PiExponent.FormalInterpolation.finite_commonize_coordinate_power_witnesses
    I (fun i => MvPolynomial.X i) (fun i => (w i : Real))
    (rho : Real) eps heps hcoord