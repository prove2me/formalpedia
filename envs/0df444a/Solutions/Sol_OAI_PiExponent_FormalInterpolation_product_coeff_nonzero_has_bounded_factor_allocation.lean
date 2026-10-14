-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.product_coeff_nonzero_has_bounded_factor_allocation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T08:23:47.059715+00:00
-- url     : https://prove2.me/submissions/bd0c44a4-7ab1-4edc-93f3-f0ac5c565c73

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_product_coefficient_allocation

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    {m n : Nat} (a : Fin (m + 1) → Nat)
    (F : Fin n → MvPolynomial (Fin (m + 1)) Complex)
    (hprod : MvPolynomial.coeff (InterpolationMatrix.exponentVector a) (∏ i, F i) ≠ 0) :
    ∃ b : Fin n → Fin (m + 1) → Nat,
      (∀ i, b i ≤ a) ∧
      (∀ j, (∑ i, b i j) = a j) ∧
      (∀ i, MvPolynomial.coeff (InterpolationMatrix.exponentVector (b i)) (F i) ≠ 0) := by
  obtain ⟨d, hd, hsum⟩ :=
    OAI.PiExponent.FormalInterpolation.mvPolynomial_product_coefficient_allocation
      (P := F) (e := InterpolationMatrix.exponentVector a) hprod
  refine ⟨fun i j => d i j, ?_, ?_, ?_⟩
  · intro i j
    have hcoord : (∑ i, d i) j = a j := by
      simpa [InterpolationMatrix.exponentVector] using
        congrArg (fun v : (Fin (m + 1) →₀ Nat) => v j) hsum
    have hle : d i j ≤ ∑ k : Fin n, d k j :=
      Finset.single_le_sum (fun k hk => Nat.zero_le (d k j)) (Finset.mem_univ i)
    rw [← hcoord]
    simpa using hle
  · intro j
    have hcoord : (∑ i, d i) j = a j := by
      simpa [InterpolationMatrix.exponentVector] using
        congrArg (fun v : (Fin (m + 1) →₀ Nat) => v j) hsum
    simpa using hcoord
  · intro i
    simpa [InterpolationMatrix.exponentVector] using hd i
