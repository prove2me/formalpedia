-- Prove2me | solution 1 for LongGapsBetweenPrimes.replacedResidueWeight_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:36.014715+00:00
-- url     : https://prove2.me/submissions/43f45e5e-49bc-4f80-841c-e9b4b8649c48

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_tupleSum_split
import Theorems.Thm_LongGapsBetweenPrimes_coefficientRemainder_eq_sum
import Theorems.Thm_LongGapsBetweenPrimes_basisWeight_eq_tupleSum
import Theorems.Thm_LongGapsBetweenPrimes_coordinateBasis_replaced

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (hP : Squarefree P) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (i : Fin (k + 1))
    (t : (p : PrimeIndex P) → Fin p.val) :
    replacedResidueWeight P (k + 1) D root i t =
      ∑ r ∈ tupleRegion P k D, coefficientRemainder P (tupleProduct r) D *
        ∏ j, coefficient P (r j).val *
          coordinateBasis (fun p => rawLocalBasis (fun j => root p (i.succAbove j))) (r j) j t := by
  classical
  rw [replacedResidueWeight, basisWeight_eq_tupleSum D _ (fun _ _ => rfl),
    tupleSum_split i D (fun j d => coefficient P d.val *
      coordinateBasis (fun p => replacedLocalBasis (root p) i) d j t)]
  simp_rw [coordinateBasis_replaced hP]
  simp [coefficientRemainder_eq_sum, coordinateBasis, rawLocalBasis, div_eq_mul_inv]
end LongGapsBetweenPrimes
