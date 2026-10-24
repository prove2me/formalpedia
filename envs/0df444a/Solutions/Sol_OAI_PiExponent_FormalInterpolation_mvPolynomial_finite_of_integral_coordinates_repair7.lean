-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.mvPolynomial_finite_of_integral_coordinates_repair7
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:00:44.125722+00:00
-- url     : https://prove2.me/submissions/db18b923-5af1-4da2-b25e-9d9e568edfaa

import Mathlib

set_option synthInstance.maxHeartbeats 100000

 theorem solution
    {d : Nat}
    (A : Subalgebra Complex (MvPolynomial (Fin d) Complex))
    (hX : ∀ i : Fin d,
      IsIntegral A (MvPolynomial.X i : MvPolynomial (Fin d) Complex)) :
    Module.Finite A (MvPolynomial (Fin d) Complex) := by
  classical
  let s : Set (MvPolynomial (Fin d) Complex) :=
    Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) Complex)
  let S : Subalgebra A (MvPolynomial (Fin d) Complex) := Algebra.adjoin A s
  have hS : S = ⊤ := by
    apply top_unique
    intro p hp
    clear hp
    induction p using MvPolynomial.induction_on with
    | C c =>
        simpa [S, s] using (S.algebraMap_mem (algebraMap Complex A c))
    | add p q hp hq =>
        exact S.add_mem hp hq
    | mul_X p i hp =>
        exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self i))
  haveI : Module.Finite A S := by
    apply Algebra.finite_adjoin_of_finite_of_isIntegral (R := A) (A := MvPolynomial (Fin d) Complex)
    · exact Set.finite_range _
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      exact hX i
  apply Module.Finite.of_surjective (S.val.toLinearMap)
  intro p
  refine ⟨⟨p, ?_⟩, rfl⟩
  rw [hS]
  exact Set.mem_univ p