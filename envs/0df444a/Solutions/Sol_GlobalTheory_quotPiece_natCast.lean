-- Prove2me | solution 1 for GlobalTheory.quotPiece_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:07:58.189089+00:00
-- url     : https://prove2.me/submissions/4320c78b-414c-4bc9-8099-d0bc8a35681a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat

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
theorem _root_.solution (I : Ideal (MvPolynomial ι k)) (n : ℕ) :
    quotPiece I n = (homogeneousSubmodule ι k n).map (Ideal.Quotient.mkₐ k I).toLinearMap := by
  rw [quotPiece, weightedHomogeneousSubmodule_one_natCast]
end GlobalTheory
