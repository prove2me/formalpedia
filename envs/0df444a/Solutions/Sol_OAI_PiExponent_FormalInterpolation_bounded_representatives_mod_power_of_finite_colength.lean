-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_representatives_mod_power_of_finite_colength
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T08:09:17.696992+00:00
-- url     : https://prove2.me/submissions/4e187cc9-88e0-402e-8e6f-9d2cc939b6fe

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finiteDimensional_quotient_power_of_finiteDimensional
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_representatives_of_finiteDimensional_quotient

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w0 : Real) (w : Fin m → Real)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfinite : FiniteDimensional Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ I))
    (s : Nat) (hs : 0 < s) :
    ∃ C : Real, ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      ∃ Q : WeightedPolynomial w0 w C, P - Q.val ∈ I ^ s := by
  have hpower : FiniteDimensional Complex
      (MvPolynomial (Fin (m + 1)) Complex ⧸ I ^ s) :=
    OAI.PiExponent.FormalInterpolation.finiteDimensional_quotient_power_of_finiteDimensional
      I hfinite s
  exact OAI.PiExponent.FormalInterpolation.bounded_representatives_of_finiteDimensional_quotient
    w0 w hw0 hw (I ^ s) hpower