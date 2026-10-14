-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.packet_vanishes_on_products_of_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T07:29:17.889257+00:00
-- url     : https://prove2.me/submissions/25cc0f7c-1bce-4f0a-a929-0948016d994c

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_packet_vanishes_on_products_with_individual_heights

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (r : Fin m → Complex) (R : Real) (T : Fin m → Nat)
    (hR : 0 < R) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hI : ∀ Q : MvPolynomial (Fin (m + 1)) Complex, Q ∈ I →
      truncatedPolynomialPacket K v0 theta w R r T Q = 0)
    (n : Nat) (f : Fin n → MvPolynomial (Fin (m + 1)) Complex)
    (hf : ∀ i, f i ∈ I) :
    truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T (∏ i, f i) = 0 := by
  have h := OAI.PiExponent.FormalInterpolation.packet_vanishes_on_products_with_individual_heights
    K v0 theta w r (fun _ : Fin n => R) T (fun _ => hR) hw f
    (fun i => hI (f i) (hf i))
  have hs : Finset.univ.sum (fun _ : Fin n => R) = (n : Real) * R := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [← hs]
  exact h
