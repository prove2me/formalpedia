-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.uniform_finite_adjoin_polynomial_representations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:05:03.159813+00:00
-- url     : https://prove2.me/submissions/15b595a5-1e85-43f7-b42b-0f6553a9399e

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_uniform_finite_adjoin_module_generators
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_adjoin_eq_aeval_range

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d m : Nat} (g : Fin m → MvPolynomial (Fin d) Complex)
    (hmod : Module.Finite (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex)) :
    ∃ t : Nat, ∃ b : Fin t → MvPolynomial (Fin d) Complex,
      ∀ q : MvPolynomial (Fin d) Complex,
        ∃ F : Fin t → MvPolynomial (Fin m) Complex,
          q = ∑ i : Fin t, MvPolynomial.aeval g (F i) * b i := by
  obtain ⟨t, b, hb⟩ :=
    OAI.PiExponent.FormalInterpolation.uniform_finite_adjoin_module_generators g hmod
  refine ⟨t, b, fun q => ?_⟩
  obtain ⟨c, hc⟩ := hb q
  let F : Fin t → MvPolynomial (Fin m) Complex := fun i =>
    Classical.choose
      (OAI.PiExponent.FormalInterpolation.adjoin_eq_aeval_range g (c i))
  have hF (i : Fin t) : MvPolynomial.aeval g (F i) = (c i : MvPolynomial (Fin d) Complex) :=
    Classical.choose_spec
      (OAI.PiExponent.FormalInterpolation.adjoin_eq_aeval_range g (c i))
  refine ⟨F, ?_⟩
  calc
    q = ∑ i : Fin t, (c i : MvPolynomial (Fin d) Complex) * b i := hc
    _ = ∑ i : Fin t, MvPolynomial.aeval g (F i) * b i := by
      congr 1
      ext i
      rw [hF i]