-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_colength_and_truncated_packet_lifting
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T08:05:17.814745+00:00
-- url     : https://prove2.me/submissions/67c60f23-4a6f-4093-b4c8-8c8ea236be60

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_finiteColength
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialPacket_surjective
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncatedPolynomialPacket_invariant_under_ideal_power

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (R : Real) (e : Fin (m + 1) → Nat) (T : Fin m → Nat)
    (r : Fin m → Complex)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : Real) * InterpolationMatrix.rowWeights v0 theta w i)
    (hr : ∃ i, r i ≠ 0) :
    FiniteDimensional Complex
      (MvPolynomial (Fin (m + 1)) Complex ⧸
        logarithmicCentersIdeal (fun j : Fin K => fun i => (j.val : Complex) * r i) T e) ∧
    ∀ n : Nat,
      ∀ f : InterpolationMatrix.Row K v0 theta w ((n : Real) * R) → Complex,
        ∃ P : MvPolynomial (Fin (m + 1)) Complex,
          ∀ Q : MvPolynomial (Fin (m + 1)) Complex,
            P - Q ∈
              (logarithmicCentersIdeal
                (fun j : Fin K => fun i => (j.val : Complex) * r i) T e) ^ n →
            truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T Q = f := by
  constructor
  · apply OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_finiteColength
      (c := fun j i => (j.val : Complex) * r i) (T := T) (e := e) he
    intro j1 j2 hne hEq
    obtain ⟨i, hi⟩ := hr
    have hmul : (j1.val : Complex) * r i = (j2.val : Complex) * r i :=
      congrFun hEq i
    have hval : (j1.val : Complex) = (j2.val : Complex) :=
      mul_right_cancel₀ hi hmul
    exact hne (Fin.ext (Nat.cast_injective hval))
  · intro n f
    obtain ⟨P, hP⟩ :=
      OAI.PiExponent.FormalInterpolation.truncatedPolynomialPacket_surjective
        K v0 theta w R e T r hR he hscale hr n f
    refine ⟨P, ?_⟩
    intro Q hPQ
    have hsame :=
      OAI.PiExponent.FormalInterpolation.truncatedPolynomialPacket_invariant_under_ideal_power
        K v0 theta w R e T r hR he hscale n P Q hPQ
    exact hsame.symm.trans hP