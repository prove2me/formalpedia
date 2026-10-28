-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.top_ideal_has_coordinate_relation
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:27:19.88962+00:00
-- url     : https://prove2.me/submissions/03826532-a48e-4265-a6a3-21cc93bbd83a

import Mathlib
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution : ¬ (∀ (d : Nat) (I : Ideal (MvPolynomial (Fin d) Complex)) (hI : I = ⊤)
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
  obtain ⟨s, -, q, hq, hlt, -⟩ :=
    h 1 ⊤ rfl (fun _ => 1) (fun _ => by norm_num) (-1) 1 one_pos 0
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  push_cast at hlt
  linarith
