-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.uniform_finite_adjoin_module_generators
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:09:06.151611+00:00
-- url     : https://prove2.me/submissions/fd05fb6e-8cc9-4e85-811b-cdda209c0e9b

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d m : Nat} (g : Fin m → MvPolynomial (Fin d) Complex)
    (hmod : Module.Finite (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex)) :
    ∃ t : Nat, ∃ b : Fin t → MvPolynomial (Fin d) Complex,
      ∀ q : MvPolynomial (Fin d) Complex,
        ∃ c : Fin t → Algebra.adjoin Complex (Set.range g),
          q = ∑ i : Fin t, (c i : MvPolynomial (Fin d) Complex) * b i := by
  classical
  letI := hmod
  obtain ⟨t, b, hb⟩ := Module.Finite.exists_fin
    (R := Algebra.adjoin Complex (Set.range g))
    (M := MvPolynomial (Fin d) Complex)
  refine ⟨t, b, ?_⟩
  intro q
  have hq : q ∈ Submodule.span (Algebra.adjoin Complex (Set.range g)) (Set.range b) := by
    rw [hb]
    simp
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun
      (R := Algebra.adjoin Complex (Set.range g))).mp hq
  refine ⟨c, ?_⟩
  simpa [Algebra.smul_def] using hc.symm