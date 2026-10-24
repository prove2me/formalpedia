-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_quotient_descend
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:38:52.891541+00:00
-- url     : https://prove2.me/submissions/e8b20907-6c75-4b9a-a8a1-7a112445a180

import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

open Ideal.Quotient

theorem solution
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (I J : Ideal A) (hIJ : I ≤ J)
    (hfinite : Module.Finite R (A ⧸ I)) :
    Module.Finite R (A ⧸ J) := by
  let f : A ⧸ I →ₗ[R] A ⧸ J :=
    { toFun := Ideal.Quotient.factor hIJ
      map_add' := map_add (Ideal.Quotient.factor hIJ)
      map_smul' := by
        intro r x
        refine Quotient.inductionOn' x ?_
        intro a
        change Ideal.Quotient.factor hIJ
            (Ideal.Quotient.mk I (r • a)) =
          Ideal.Quotient.mk J (r • a)
        exact Ideal.Quotient.factor_mk hIJ _ }
  letI : Module.Finite R (A ⧸ I) := hfinite
  exact Module.Finite.of_surjective f (by
    intro y
    simpa [f] using Ideal.Quotient.factor_surjective hIJ y)