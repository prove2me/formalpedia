-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.low_degree_relation_gives_coordinate_relation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:26:10.617372+00:00
-- url     : https://prove2.me/submissions/fb6a86d4-5a0d-4b19-95ee-f0c8c8515bff

import Mathlib
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (eps : Real) (heps : 0 < eps) (i : Fin d)
    (n : Nat) (hn : 0 < n) (f : MvPolynomial (Fin d) Complex)
    (hrel : MvPolynomial.X i ^ n - f ∈ I)
    (hsupport : ∀ a, a ∈ f.support →
      ∑ j, (w j : Real) * (a j : Real) < (n : Real) * (w i : Real))
    (hbound : (n : Real) * (w i : Real) ≤ (rho : Real)) :
    ∃ s : Nat, 0 < s ∧
      ∃ q : Rat, 0 < q ∧ (q : Real) < (s : Real) * ((rho : Real) + eps) ∧
        ∃ n' : Nat, 0 < n' ∧ (n' : Rat) * w i = q ∧
          ∃ g : MvPolynomial (Fin d) Complex,
            MvPolynomial.X i ^ n' - g ∈ I ^ s ∧
            ∀ a, a ∈ g.support →
              ∑ j, (w j : Real) * (a j : Real) < (q : Real) := by
  have hwi : (0 : ℚ) < w i := by exact_mod_cast hw i
  refine ⟨1, one_pos, (n : ℚ) * w i, mul_pos (by exact_mod_cast hn) hwi, ?_, n, hn, rfl, f,
    by simpa using hrel, ?_⟩
  · push_cast; linarith
  · intro a ha; push_cast; exact hsupport a ha
