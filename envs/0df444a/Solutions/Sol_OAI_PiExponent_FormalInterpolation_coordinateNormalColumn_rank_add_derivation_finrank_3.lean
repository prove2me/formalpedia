-- Prove2me | solution 3 for OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_rank_add_derivation_finrank
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T07:42:16.512797+00:00
-- url     : https://prove2.me/submissions/3cfd85f9-14a0-4b27-96bf-26d1584c89b4

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_add_kaehler_finrank
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Localization.FractionRing

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (logarithmicPrimeField P)
        (Submodule.span (logarithmicPrimeField P)
          (Set.range (coordinateNormalColumnAtPrime P))) +
      Module.finrank (logarithmicPrimeField P)
        (Derivation Complex (logarithmicPrimeField P) (logarithmicPrimeField P)) = m + 1 := by
  have h := coordinateNormalColumn_span_finrank_add_kaehler_finrank P
  have e := (KaehlerDifferential.linearMapEquivDerivation Complex (logarithmicPrimeField P)
    (M := logarithmicPrimeField P))
  rw [← e.finrank_eq]
  have : Module.finrank (logarithmicPrimeField P)
      (Module.Dual (logarithmicPrimeField P) Ω[logarithmicPrimeField P⁄Complex]) =
      Module.finrank (logarithmicPrimeField P) Ω[logarithmicPrimeField P⁄Complex] :=
    Subspace.dual_finrank_eq
  unfold Module.Dual at this
  rw [this]; exact h
