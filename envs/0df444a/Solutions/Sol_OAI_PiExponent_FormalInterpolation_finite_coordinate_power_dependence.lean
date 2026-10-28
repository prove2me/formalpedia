-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_coordinate_power_dependence
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T16:49:37.439796+00:00
-- url     : https://prove2.me/submissions/f57b6b13-b318-43f7-9363-62114ce8213d

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_module_powers_dependent
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_quotient_algebraMap_smul

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) ℂ))
    [Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ I)] (i : Fin d) :
    ∃ K : Nat, ∃ c : Fin (K + 1) → ℂ,
      (∃ n : Fin (K + 1), c n ≠ 0) ∧
      (∑ n : Fin (K + 1), MvPolynomial.C (c n) *
        (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (n : Nat)) ∈ I := by
  obtain ⟨K, c, hc, hrel⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_module_powers_dependent
      (A := MvPolynomial (Fin d) ℂ ⧸ I)
      (Ideal.Quotient.mk I (MvPolynomial.X i))
  refine ⟨K, c, hc, ?_⟩
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  have hmap :
      Ideal.Quotient.mk I
        (∑ n : Fin (K + 1), MvPolynomial.C (c n) *
          (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (n : Nat)) =
        ∑ n : Fin (K + 1), c n •
          (Ideal.Quotient.mk I (MvPolynomial.X i)) ^ (n : Nat) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    calc
      Ideal.Quotient.mk I
          (MvPolynomial.C (c n) *
            (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (n : Nat)) =
          c n • Ideal.Quotient.mk I
            ((MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (n : Nat)) := by
              rw [MvPolynomial.C_eq_algebraMap]
              exact OAI.PiExponent.FormalInterpolation.quotient_algebraMap_smul
                (R := MvPolynomial (Fin d) ℂ) (I := I) (c := c n)
                (p := (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (n : Nat))
      _ = c n • (Ideal.Quotient.mk I (MvPolynomial.X i)) ^ (n : Nat) := by
            rw [map_pow]
  rw [hmap, hrel]
