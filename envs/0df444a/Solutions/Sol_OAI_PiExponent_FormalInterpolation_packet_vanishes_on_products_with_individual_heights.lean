-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.packet_vanishes_on_products_with_individual_heights
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T07:36:16.482688+00:00
-- url     : https://prove2.me/submissions/11723538-0e81-40f5-aa0b-fe3bde913f64

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coeff_vanishes_for_product_on_weighted_simplex

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (r : Fin m → Complex) {n : Nat} (R : Fin n → Real) (T : Fin m → Nat)
    (hR : ∀ i, 0 < R i) (hw : ∀ i, 0 < w i)
    (f : Fin n → MvPolynomial (Fin (m + 1)) Complex)
    (hf : ∀ i,
      truncatedPolynomialPacket K v0 theta w (R i) r T (f i) = 0) :
    truncatedPolynomialPacket K v0 theta w (∑ i, R i) r T (∏ i, f i) = 0 := by
  classical
  funext rho
  let J : Fin n → MvPolynomial (Fin (m + 1)) Complex := fun i =>
    truncatedPolynomialJet (fun k => (rho.1.val : Complex) * r k) T (f i)
  have hcoeff := OAI.PiExponent.FormalInterpolation.coeff_vanishes_for_product_on_weighted_simplex
    (v := InterpolationMatrix.rowWeights v0 theta w) (R := R) hR J (by
      intro i a ha
      exact congrFun (hf i) ⟨rho.1, ⟨a, ha⟩⟩
    )
    rho.2.1 rho.2.2
  change MvPolynomial.coeff (InterpolationMatrix.exponentVector rho.2.1)
    (truncatedPolynomialJet (fun k => (rho.1.val : Complex) * r k) T (∏ i, f i)) = 0
  simpa [J, truncatedPolynomialJet] using hcoeff
