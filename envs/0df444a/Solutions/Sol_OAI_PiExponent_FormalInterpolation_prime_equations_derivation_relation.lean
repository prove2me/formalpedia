-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.prime_equations_derivation_relation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:20:08.586787+00:00
-- url     : https://prove2.me/submissions/b0809021-bca4-4676-ab97-ec149ca6fc6a

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (D : Derivation Complex (logarithmicPrimeField P) (logarithmicPrimeField P)) :
    (∑ i : Fin (m + 1),
      D (algebraMap (MvPolynomial (Fin (m + 1)) Complex)
        (logarithmicPrimeField P) (MvPolynomial.X i)) •
          coordinateNormalColumnAtPrime P i) = 0 := by
  classical
  set L := logarithmicPrimeField P
  set φ := algebraMap (MvPolynomial (Fin (m + 1)) Complex) L
  have chain : ∀ p : MvPolynomial (Fin (m + 1)) Complex,
      D (φ p) = ∑ i, φ (MvPolynomial.pderiv i p) * D (φ (MvPolynomial.X i)) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have : φ (MvPolynomial.C a) = algebraMap ℂ L a := by
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      rw [this, D.map_algebraMap]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [MvPolynomial.pderiv_C, map_zero, zero_mul]
    | add p q hp hq =>
      rw [map_add, map_add, hp, hq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_add, map_add, add_mul]
    | mul_X p j hp =>
      rw [map_mul, D.leibniz, hp, smul_eq_mul, smul_eq_mul]
      have e : ∀ i, φ (MvPolynomial.pderiv i (p * MvPolynomial.X j)) * D (φ (MvPolynomial.X i)) =
          φ p * φ (Pi.single (M := fun _ => MvPolynomial (Fin (m + 1)) ℂ) i 1 j) * D (φ (MvPolynomial.X i)) +
            φ (MvPolynomial.X j) * (φ (MvPolynomial.pderiv i p) * D (φ (MvPolynomial.X i))) := by
        intro i
        rw [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul,
          map_mul]
        ring
      have s1 : ∑ x, φ p * φ (Pi.single (M := fun _ => MvPolynomial (Fin (m + 1)) ℂ) x 1 j) *
          D (φ (MvPolynomial.X x)) = φ p * D (φ (MvPolynomial.X j)) := by
        rw [Finset.sum_eq_single j]
        · rw [Pi.single_eq_same, map_one, mul_one]
        · intro b _ hb
          rw [Pi.single_eq_of_ne' hb, map_zero, mul_zero, zero_mul]
        · simp
      rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, ← Finset.mul_sum, s1]
  funext F
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, coordinateNormalColumnAtPrime, smul_eq_mul]
  have h0 : φ (F : MvPolynomial _ ℂ) = 0 := by
    have : (Ideal.Quotient.mk P (F : MvPolynomial _ ℂ)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr F.2
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin (m + 1)) ℂ)
      (MvPolynomial (Fin (m + 1)) ℂ ⧸ P) L]
    simp [Ideal.Quotient.algebraMap_eq, this]
  have := chain F
  rw [h0, map_zero] at this
  rw [this]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
