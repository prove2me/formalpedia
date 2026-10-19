-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eventual_representatives_of_power_generators_of_bounded_base_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:22:59.719128+00:00
-- url     : https://prove2.me/submissions/6a63ae5a-3ac1-40e3-9824-8f8900640bbc

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_power_generator_block_reduction
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_subcritical_block_cutoff

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w0 : Real) (w : Fin m → Real)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (R : Real) (hR : 0 < R)
    (s : Nat) (hs : 0 < s) (D : Real) (hD : D < (s : Real) * R)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (hspan : Ideal.span (S : Set (MvPolynomial (Fin (m + 1)) Complex)) = I ^ s)
    (hdeg : ∀ P ∈ S, ∀ a ∈ P.support,
      ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : Real) ≤ D)
    (C : Real)
    (hbase : ∀ P : MvPolynomial (Fin (m + 1)) Complex,
      ∃ Q : WeightedPolynomial w0 w C, P - Q.val ∈ I ^ s) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ P : MvPolynomial (Fin (m + 1)) Complex,
        ∃ Q : WeightedPolynomial w0 w ((n : Real) * R),
          P - Q.val ∈ I ^ n := by
  obtain ⟨N, hcut⟩ := OAI.PiExponent.FormalInterpolation.subcritical_block_cutoff
    R hR s hs D hD C
  refine ⟨N, ?_⟩
  intro n hn P
  obtain ⟨k, hklt, hkn, hbound⟩ := hcut n hn
  obtain ⟨Q, hQmem⟩ :=
    OAI.PiExponent.FormalInterpolation.power_generator_block_reduction
      w0 w hw0 hw I s hs S hspan D hdeg C hbase k n hkn P
  refine ⟨⟨Q.val, ?_⟩, hQmem⟩
  intro a ha
  exact le_trans (Q.property a ha) hbound