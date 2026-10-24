-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_polynomial_representations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:53:56.079994+00:00
-- url     : https://prove2.me/submissions/f0ce9b38-3b58-4c65-a113-5ecc57d66e6a

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d m : Nat} (g : Fin m → MvPolynomial (Fin d) Complex)
    (hmod : Module.Finite (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex)) :
    ∀ q : MvPolynomial (Fin d) Complex,
      ∃ t : Nat, ∃ b : Fin t → MvPolynomial (Fin d) Complex,
        ∃ F : Fin t → MvPolynomial (Fin m) Complex,
          q = ∑ i : Fin t, MvPolynomial.aeval g (F i) * b i := by
  classical
  let R := Algebra.adjoin Complex (Set.range g)
  let A := MvPolynomial (Fin d) Complex
  letI : Module.Finite R A := hmod
  obtain ⟨t, f, hf⟩ := Module.Finite.exists_fin' R A
  intro q
  obtain ⟨c, hc⟩ := hf q
  let b : Fin t → A := fun i => f ((Pi.single i (1 : R) : Fin t → R))
  have hlinear : f c = ∑ i : Fin t, (c i) • b i := by
    calc
      f c = f (∑ i : Fin t, (Pi.single i (c i) : Fin t → R)) := by
        congr 1
        ext i
        simp
      _ = ∑ i : Fin t, f ((Pi.single i (c i) : Fin t → R)) := map_sum f _ _
      _ = ∑ i : Fin t, (c i) • b i := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [b]
        have hsingle : (Pi.single i (c i) : Fin t → R) =
            (c i) • (Pi.single i (1 : R) : Fin t → R) := by
          ext j
          by_cases hj : j = i <;> simp [hj]
        calc
          f ((Pi.single i (c i) : Fin t → R)) =
              f ((c i) • (Pi.single i (1 : R) : Fin t → R)) :=
            congrArg f hsingle
          _ = (c i) • f ((Pi.single i (1 : R) : Fin t → R)) :=
            map_smul f (c i) _
  have hcoeff : ∀ i : Fin t, ∃ p : MvPolynomial (Fin m) Complex,
      MvPolynomial.aeval g p = (c i : A) := by
    intro i
    have hc' : (c i : A) ∈ Algebra.adjoin Complex (Set.range g) := (c i).property
    rw [Algebra.adjoin_range_eq_range_aeval] at hc'
    exact Set.mem_range.mp hc'
  let F : Fin t → MvPolynomial (Fin m) Complex := fun i => Classical.choose (hcoeff i)
  have hF (i : Fin t) : MvPolynomial.aeval g (F i) = (c i : A) :=
    Classical.choose_spec (hcoeff i)
  refine ⟨t, b, F, ?_⟩
  calc
    q = f c := hc.symm
    _ = ∑ i : Fin t, (c i) • b i := hlinear
    _ = ∑ i : Fin t, MvPolynomial.aeval g (F i) * b i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Algebra.smul_def]
      change (c i : A) * b i = _
      rw [← hF i]