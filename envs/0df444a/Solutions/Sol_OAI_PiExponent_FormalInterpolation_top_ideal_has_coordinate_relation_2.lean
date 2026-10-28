-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.top_ideal_has_coordinate_relation
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:27:36.504451+00:00
-- url     : https://prove2.me/submissions/42306f6d-b124-42d2-a675-883f13631a78

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution : ¬ (∀
    (d : Nat) (I : Ideal (MvPolynomial (Fin d) Complex)) (hI : I = ⊤)
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (eps : Real) (heps : 0 < eps) (i : Fin d),
    ∃ s : Nat, 0 < s ∧
      ∃ q : Rat, 0 < q ∧ (q : Real) < (s : Real) * ((rho : Real) + eps) ∧
        ∃ n : Nat, 0 < n ∧ (n : Rat) * w i = q ∧
          ∃ f : MvPolynomial (Fin d) Complex,
            MvPolynomial.X i ^ n - f ∈ I ^ s ∧
            ∀ a, a ∈ f.support →
              ∑ j, (w j : Real) * (a j : Real) < (q : Real)) := by
  intro h
  obtain ⟨s, hs, q, hq, hlt, -⟩ :=
    h 1 ⊤ rfl (fun _ => 1) (fun _ => by norm_num) (-1) (1/2) (by norm_num) 0
  have hq' : (0 : Real) < q := by exact_mod_cast hq
  have hs' : (0 : Real) < s := by exact_mod_cast hs
  push_cast at hlt
  nlinarith
