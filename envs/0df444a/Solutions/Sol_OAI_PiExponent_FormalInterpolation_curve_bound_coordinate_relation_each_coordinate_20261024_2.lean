-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.curve_bound_coordinate_relation_each_coordinate_20261024
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T00:31:30.518209+00:00
-- url     : https://prove2.me/submissions/e961b7d6-df1b-4a81-aa44-94e41a0b4643
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_coordinate_low_degree_relation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_low_degree_relation_gives_coordinate_relation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_top_ideal_has_coordinate_relation_of_nonneg
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∀ i : Fin d, ∃ s : Nat, 0 < s ∧
      ∃ q : Rat, 0 < q ∧ (q : Real) < (s : Real) * ((rho : Real) + eps) ∧
        ∃ n : Nat, 0 < n ∧ (n : Rat) * w i = q ∧
          ∃ f : MvPolynomial (Fin d) Complex,
            MvPolynomial.X i ^ n - f ∈ I ^ s ∧
            ∀ a, a ∈ f.support →
              ∑ j, (w j : Real) * (a j : Real) < (q : Real) := by
  intro i
  by_cases htop : I = ⊤
  · exact top_ideal_has_coordinate_relation_of_nonneg d I htop w hw rho hrho eps heps i
  · obtain ⟨n, hn, f, hrel, hsupport, hbound⟩ :=
      curve_bound_coordinate_low_degree_relation I hfinite w hw rho hrho hcurve htop i
    exact low_degree_relation_gives_coordinate_relation I w hw rho eps heps i n hn f
      hrel hsupport hbound