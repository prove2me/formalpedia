-- Prove2me | solution 1 for GlobalTheory.cast_hilbertDegree_of_degree_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:25:51.283704+00:00
-- url     : https://prove2.me/submissions/a642997c-6f49-48c0-b219-b6ca5f1b806e

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
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) {e : ℕ}
    (he : (idealHilbertPoly I).degree = e) :
    (hilbertDegree I : ℚ) = (e.factorial : ℚ) * (idealHilbertPoly I).coeff e := by
  rw [cast_hilbertDegree hI, leadingCoeff, natDegree_eq_of_degree_eq_some he]
end GlobalTheory
