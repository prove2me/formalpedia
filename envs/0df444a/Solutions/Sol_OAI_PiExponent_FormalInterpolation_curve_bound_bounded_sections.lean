-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.curve_bound_bounded_sections
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:01:13.490984+00:00
-- url     : https://prove2.me/submissions/7fe8ac85-da8d-4696-b8df-cd746cb2344a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_exact_initial_power_with_integer_margin

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∃ s : Nat, 0 < s ∧ ∃ B : Nat,
      (B : Real) < (s : Real) * ((rho : Real) + eps) ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span
          {h : MvPolynomial (Fin d) Complex |
            ∃ g : MvPolynomial (Fin d) Complex,
              g ∈ I ^ s ∧
              (∀ a ∈ g.support,
                ∑ k, (w k : Real) * (a k : Real) ≤ (B : Real)) ∧
              ∃ q : Rat, (q : Real) ≤ (B : Real) ∧
                h = MvPolynomial.weightedHomogeneousComponent
                  (fun k => (w k : ℚ)) q g} := by
  obtain ⟨s, hs, B, hB, q, hqB, hcoord⟩ :=
    OAI.PiExponent.FormalInterpolation.curve_bound_exact_initial_power_with_integer_margin
      I hfinite w hw rho hrho hcurve eps heps
  refine ⟨s, hs, B, hB, ?_⟩
  intro i
  obtain ⟨n, hn, hmem⟩ := hcoord i
  refine ⟨n, hn, ?_⟩
  have hsubset :
      Set.range (fun (p : {g : MvPolynomial (Fin d) Complex //
          g ∈ I ^ s ∧ ∀ a ∈ g.support,
            ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
          MvPolynomial.weightedHomogeneousComponent
            (fun j => (w j : ℚ)) q p.1) ⊆
        {h : MvPolynomial (Fin d) Complex |
          ∃ g : MvPolynomial (Fin d) Complex,
            g ∈ I ^ s ∧
            (∀ a ∈ g.support,
              ∑ k, (w k : Real) * (a k : Real) ≤ (B : Real)) ∧
            ∃ qPrime : Rat, (qPrime : Real) ≤ (B : Real) ∧
              h = MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : ℚ)) qPrime g} := by
    rintro z ⟨p, hp⟩
    rcases p with ⟨g, hgI, hgw⟩
    refine ⟨g, hgI, ?_, q, hqB, ?_⟩
    · intro a ha
      exact le_trans (hgw a ha) hqB
    · exact hp.symm
  exact (Ideal.span_mono hsubset) hmem
