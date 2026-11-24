-- Prove2me | solution 1 for GlobalTheory.cast_hilbertDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:17:59.488846+00:00
-- url     : https://prove2.me/submissions/b3e8f757-ff75-447f-90cd-af94238a5190

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Theorems.Thm_GlobalTheory_leadingCoeff_nonneg_of_eventually_eval_nat
import Theorems.Thm_GlobalTheory_exists_int_factorial_mul_coeff
import Theorems.Thm_GlobalTheory_eventually_finrank_quotPiece
import Theorems.Thm_GlobalTheory_eventually_idealHilbertPoly_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial DirectSum
variable {ι k : Type*} [Field k]
namespace GlobalTheory
theorem _root_.solution [Finite ι] {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) :
    (hilbertDegree I : ℚ) =
      ((idealHilbertPoly I).natDegree.factorial : ℚ) * (idealHilbertPoly I).leadingCoeff := by
  obtain ⟨z, hz⟩ := exists_int_factorial_mul_coeff (P := idealHilbertPoly I)
    degree_le_natDegree (by
      filter_upwards [eventually_finrank_quotPiece hI] with n hn
      exact ⟨finrank k (quotPiece I n), by rw [← hn]; simp⟩)
  have h0 : 0 ≤ ((idealHilbertPoly I).natDegree.factorial : ℚ) *
      (idealHilbertPoly I).leadingCoeff := mul_nonneg (by positivity)
    (leadingCoeff_nonneg_of_eventually_eval_nat (eventually_idealHilbertPoly_nonneg hI))
  rw [hilbertDegree, leadingCoeff, hz]
  rw [leadingCoeff, hz] at h0
  lift z to ℕ using (by exact_mod_cast h0)
  simp
end GlobalTheory
