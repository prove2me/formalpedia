-- Prove2me | solution 1 for GlobalTheory.hilbertDegree_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:25:55.546402+00:00
-- url     : https://prove2.me/submissions/8a2a1a0c-ab67-4a03-884e-cf261fef891c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Theorems.Thm_GlobalTheory_cast_hilbertDegree

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
    hilbertDegree I = 0 ↔ idealHilbertPoly I = 0 := by
  rw [← Nat.cast_eq_zero (R := ℚ), cast_hilbertDegree hI, mul_eq_zero, leadingCoeff_eq_zero]
  simp [Nat.factorial_ne_zero]
end GlobalTheory
