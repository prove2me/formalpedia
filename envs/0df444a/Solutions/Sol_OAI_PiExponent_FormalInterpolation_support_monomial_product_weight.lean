-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.support_monomial_product_weight
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T11:57:55.811225+00:00
-- url     : https://prove2.me/submissions/a81c9ae6-4ad0-46c1-93e5-027888587ea5

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_weight_bound_pow
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_weight_bound_fintype_prod

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d m : Nat} (w : Fin d → Rat) (D : Nat)
    (g : Fin m → MvPolynomial (Fin d) Complex)
    (hdeg : ∀ j, ∀ b ∈ (g j).support,
      ∑ k, (w k : Real) * (b k : Real) ≤ (D : Real))
    (u : Fin m →₀ Nat) (a : Fin d →₀ Nat)
    (ha : a ∈ (∏ j : Fin m, (g j) ^ (u j)).support) :
    ∑ k, (w k : Real) * (a k : Real) ≤
      (∑ j, (u j : Real)) * (D : Real) := by
  have hp : ∀ j, ∀ b ∈ (g j ^ u j).support,
      ∑ k, (w k : Real) * (b k : Real) ≤ (u j : Real) * (D : Real) := by
    intro j
    exact OAI.PiExponent.FormalInterpolation.support_weight_bound_pow
      w (D : Real) (g j) (hdeg j) (u j)
  have hprod :=
    OAI.PiExponent.FormalInterpolation.support_weight_bound_fintype_prod
      (σ := Fin d) (ι := Fin m) w (fun j => (g j) ^ (u j))
      (fun j => (u j : Real) * (D : Real)) hp a ha
  calc
    ∑ k, (w k : Real) * (a k : Real) ≤
        ∑ j, (u j : Real) * (D : Real) := hprod
    _ = (∑ j, (u j : Real)) * (D : Real) := by rw [Finset.sum_mul]