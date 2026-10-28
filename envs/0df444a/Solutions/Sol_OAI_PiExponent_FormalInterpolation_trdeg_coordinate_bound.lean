-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.trdeg_coordinate_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:29:43.214215+00:00
-- url     : https://prove2.me/submissions/eafccc77-13ea-4ee9-ac70-72b797e534e8

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Extension.Cotangent.Basic

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    (Algebra.trdeg Complex (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)).toNat ≤ m + 1 := by
  set B := MvPolynomial (Fin (m + 1)) Complex ⧸ P
  have hB : Algebra.trdeg Complex B ≤ (m + 1 : Nat) := by
    have h1 := trdeg_le_of_surjective (Ideal.Quotient.mkₐ Complex P)
      (Ideal.Quotient.mkₐ_surjective Complex P)
    rw [MvPolynomial.trdeg_of_isDomain] at h1
    simpa using h1
  have hL : Algebra.trdeg B (logarithmicPrimeField P) = 0 := by
    have : Algebra.IsAlgebraic B (logarithmicPrimeField P) :=
      IsLocalization.isAlgebraic (logarithmicPrimeField P) (nonZeroDivisors B)
    exact trdeg_eq_zero
  have hadd := trdeg_add_eq (R := Complex) (S := B) (A := logarithmicPrimeField P)
  rw [hL, add_zero] at hadd
  rw [← hadd]
  have hfin : Algebra.trdeg Complex B < Cardinal.aleph0 := hB.trans_lt Cardinal.natCast_lt_aleph0
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hn] at hB ⊢
  simp only [Cardinal.toNat_natCast]
  exact_mod_cast hB
