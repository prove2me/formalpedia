-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eventual_representatives_of_subcritical_power_generators
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T08:02:55.167104+00:00
-- url     : https://prove2.me/submissions/41985f1f-eec1-4ce9-9718-49eca879bc32

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_representatives_mod_power_of_finite_colength
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_representatives_of_power_generators_of_bounded_base_representatives

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w0 : Real) (w : Fin m → Real)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfinite : FiniteDimensional Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ I))
    (R : Real) (hR : 0 < R)
    (s : Nat) (hs : 0 < s) (D : Real) (hD : D < (s : Real) * R)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (hspan : Ideal.span (S : Set (MvPolynomial (Fin (m + 1)) Complex)) = I ^ s)
    (hdeg : ∀ P ∈ S, ∀ a ∈ P.support,
      ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : Real) ≤ D) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ P : MvPolynomial (Fin (m + 1)) Complex,
        ∃ Q : WeightedPolynomial w0 w ((n : Real) * R),
          P - Q.val ∈ I ^ n := by
  obtain ⟨C, hbase⟩ :=
    OAI.PiExponent.FormalInterpolation.bounded_representatives_mod_power_of_finite_colength
      w0 w hw0 hw I hfinite s hs
  exact
    OAI.PiExponent.FormalInterpolation.eventual_representatives_of_power_generators_of_bounded_base_representatives
      w0 w hw0 hw I R hR s hs D hD S hspan hdeg C hbase