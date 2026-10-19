-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncatedPolynomialPacket_difference_coeff_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:14:58.161224+00:00
-- url     : https://prove2.me/submissions/e22df865-09d8-4a84-813f-f4fd731cf456

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_idealProduct_pow_mem_component
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_singleCenter_truncatedJet_coeff_vanishes

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (R : Real) (e : Fin (m + 1) → Nat) (T : Fin m → Nat)
    (r : Fin m → Complex)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : Real) * InterpolationMatrix.rowWeights v0 theta w i)
    (n : Nat) (P Q : MvPolynomial (Fin (m + 1)) Complex)
    (hPQ : P - Q ∈
      (logarithmicCentersIdeal
        (fun j : Fin K => fun i => (j.val : Complex) * r i) T e) ^ n)
    (rho : InterpolationMatrix.Row K v0 theta w ((n : Real) * R)) :
    (truncatedPolynomialJet (fun i => (rho.1.val : Complex) * r i) T (P - Q)).coeff
      (InterpolationMatrix.exponentVector rho.2.1) = 0 := by
  have hcenter : P - Q ∈
      (logarithmicCenterIdeal (fun i => (rho.1.val : Complex) * r i) T e) ^ n := by
    apply OAI.PiExponent.FormalInterpolation.idealProduct_pow_mem_component
      (fun j : Fin K => logarithmicCenterIdeal (fun i => (j.val : Complex) * r i) T e)
      (P - Q) n rho.1
    simpa [logarithmicCentersIdeal] using hPQ
  exact OAI.PiExponent.FormalInterpolation.singleCenter_truncatedJet_coeff_vanishes
    v0 theta w R e T (fun i => (rho.1.val : Complex) * r i) hR he hscale n
    (P - Q) hcenter rho.2.1 rho.2.2
