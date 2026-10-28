-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.scaledProduct_mem_ideal_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T18:24:51.377651+00:00
-- url     : https://prove2.me/submissions/664f156d-b132-49a8-9c17-617b6372e42b

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators

theorem solution
    {d : Nat} {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : Ideal (MvPolynomial (Fin d) Complex)) (s : Nat)
    (f : ι → MvPolynomial (Fin d) Complex)
    (hf : ∀ i, f i ∈ I ^ s) :
    (∏ i : ι, f i) ∈ I ^ (Fintype.card ι * s) := by
  classical
  have hprod : ∀ t : Finset ι, (∏ i ∈ t, f i) ∈ I ^ (t.card * s) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
        rw [Finset.prod_insert ha]
        have hmul : f a * (∏ i ∈ t, f i) ∈ I ^ s * I ^ (t.card * s) :=
          Ideal.mul_mem_mul (hf a) ih
        have hp : f a * (∏ i ∈ t, f i) ∈ I ^ (s + t.card * s) := by
          rw [Ideal.IsTwoSided.pow_add]
          exact hmul
        have hexp : s + t.card * s = (insert a t).card * s := by
          simp [ha, Nat.add_mul] <;> omega
        rw [hexp] at hp
        exact hp
  simpa using hprod Finset.univ