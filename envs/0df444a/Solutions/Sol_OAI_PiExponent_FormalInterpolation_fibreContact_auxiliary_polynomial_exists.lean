-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_auxiliary_polynomial_exists
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T13:45:49.549421+00:00
-- url     : https://prove2.me/submissions/47090e60-0f51-4531-be70-0a0ccb59dab4

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_simplex_count_comparison
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_jet_kernel

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    (n K : Nat) (W V : Fin n → Rat)
    (hW : ∀ i, 0 < (W i : Real)) (hV : ∀ i, 0 < (V i : Real))
    (a : Real) (ha : 0 < a)
    (hvolume : (K : Real) * a ^ n *
      (∏ i : Fin n, (W i : Real)) / (∏ i : Fin n, (V i : Real)) < 1)
    (c : Fin K → Fin n → Complex) :
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N →
      ∃ F : MvPolynomial (Fin n) Complex,
        F ≠ 0 ∧ fibreContactSupportBound W N F ∧
          fibreContactJetVanishing c V (a * (N : Real)) F := by
  obtain ⟨N0, hcounts⟩ :=
    OAI.PiExponent.FormalInterpolation.weighted_simplex_count_comparison
      n K W V hW hV a ha hvolume
  refine ⟨N0, ?_⟩
  intro N hN
  obtain ⟨hSfinite, hTfinite, hcard⟩ := hcounts N hN
  exact OAI.PiExponent.FormalInterpolation.finite_jet_kernel
    n K W V N a c hSfinite hTfinite hcard