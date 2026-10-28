-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.top_ideal_has_coordinate_relation_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:35:09.412427+00:00
-- url     : https://prove2.me/submissions/dd95f244-cbe0-451e-b3f2-7346da50db4c

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    (d : Nat) (I : Ideal (MvPolynomial (Fin d) Complex)) (hI : I = ⊤)
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (eps : Real) (heps : 0 < eps) (i : Fin d) :
    ∃ s : Nat, 0 < s ∧
      ∃ q : Rat, 0 < q ∧ (q : Real) < (s : Real) * ((rho : Real) + eps) ∧
        ∃ n : Nat, 0 < n ∧ (n : Rat) * w i = q ∧
          ∃ f : MvPolynomial (Fin d) Complex,
            MvPolynomial.X i ^ n - f ∈ I ^ s ∧
            ∀ a, a ∈ f.support →
              ∑ j, (w j : Real) * (a j : Real) < (q : Real) := by
  obtain ⟨s, hs⟩ := exists_nat_gt ((w i : Real) / eps)
  have hwi := hw i
  have hdiv : 0 < (w i : Real) / eps := div_pos hwi heps
  have hs0 : (0 : Real) < s := lt_trans hdiv hs
  have hrho' : (0 : Real) ≤ rho := by exact_mod_cast hrho
  refine ⟨s, by exact_mod_cast hs0, w i, by exact_mod_cast hwi, ?_, 1, one_pos, by simp, 0, ?_, ?_⟩
  · have : (w i : Real) < s * eps := by
      rw [div_lt_iff₀ heps] at hs; linarith
    nlinarith
  · subst hI; simp [Ideal.top_pow]
  · intro a ha; simp at ha
