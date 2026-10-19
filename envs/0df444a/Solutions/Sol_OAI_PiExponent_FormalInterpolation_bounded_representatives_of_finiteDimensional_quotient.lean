-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_representatives_of_finiteDimensional_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T08:15:46.574674+00:00
-- url     : https://prove2.me/submissions/4bf78c95-ed5d-443c-a546-5c47059b7253

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finiteDimensional_quotient_has_bounded_support_representatives
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_support_gives_weighted_polynomial

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w0 : Real) (w : Fin m → Real)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfinite : FiniteDimensional Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ J)) :
    ∃ C : Real, ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      ∃ Q : WeightedPolynomial w0 w C, P - Q.val ∈ J := by
  obtain ⟨N, hbox⟩ :=
    OAI.PiExponent.FormalInterpolation.finiteDimensional_quotient_has_bounded_support_representatives
      J hfinite
  obtain ⟨C, hweight⟩ :=
    OAI.PiExponent.FormalInterpolation.bounded_support_gives_weighted_polynomial
      w0 w hw0 hw N
  refine ⟨C, fun P => ?_⟩
  obtain ⟨R, hRbox, hPR⟩ := hbox P
  obtain ⟨Q, hQR⟩ := hweight R hRbox
  refine ⟨Q, ?_⟩
  rw [hQR]
  exact hPR
