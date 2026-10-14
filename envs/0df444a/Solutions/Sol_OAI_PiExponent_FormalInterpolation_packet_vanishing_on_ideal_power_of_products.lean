-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.packet_vanishing_on_ideal_power_of_products
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T07:56:29.701636+00:00
-- url     : https://prove2.me/submissions/d0be0c36-a656-4cf3-a9de-93afc1024838

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_linearMap_vanishes_on_ideal_power_of_products

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (r : Fin m → Complex) (R : Real) (T : Fin m → Nat)
    (hR : 0 < R) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (n : Nat)
    (hProducts : ∀ f : Fin n → MvPolynomial (Fin (m + 1)) Complex,
      (∀ i, f i ∈ I) →
      truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T (∏ i, f i) = 0)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (hP : P ∈ I ^ n) :
    truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T P = 0 := by
  by_cases hn : n = 0
  · subst n
    have hrow : OAI.PiExponent.strictWeightedSimplex
        (InterpolationMatrix.rowWeights v0 theta w) 0 = ∅ := by
      ext a
      simp [OAI.PiExponent.strictWeightedSimplex, OAI.PiExponent.realWeightedSimplex]
      intro ha hle
      subst a
      simp
    funext rho
    have hfalse : False := by
      simpa [InterpolationMatrix.Row, hrow] using rho.2.2
    exact hfalse.elim
  · let F : MvPolynomial (Fin (m + 1)) Complex →ₗ[Complex]
      (InterpolationMatrix.Row K v0 theta w ((n : Real) * R) → Complex) :=
      { toFun := truncatedPolynomialPacket K v0 theta w ((n : Real) * R) r T
        map_add' := by
          intro A B
          funext rho
          simp [truncatedPolynomialPacket, truncatedPolynomialJet]
        map_smul' := by
          intro c A
          funext rho
          simp [truncatedPolynomialPacket, truncatedPolynomialJet] }
    exact OAI.PiExponent.FormalInterpolation.linearMap_vanishes_on_ideal_power_of_products
      I n (Nat.pos_of_ne_zero hn) F hProducts P hP
