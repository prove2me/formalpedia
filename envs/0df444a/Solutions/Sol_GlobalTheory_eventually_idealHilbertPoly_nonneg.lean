-- Prove2me | solution 1 for GlobalTheory.eventually_idealHilbertPoly_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:11:25.852635+00:00
-- url     : https://prove2.me/submissions/f7b55ee8-b831-4bc5-ae12-eb81d7c7d056

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Theorems.Thm_GlobalTheory_eventually_finrank_quotPiece

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
    ∀ᶠ n : ℕ in atTop, 0 ≤ (idealHilbertPoly I).eval (n : ℚ) := by
  filter_upwards [eventually_finrank_quotPiece hI] with n hn
  rw [← hn]
  positivity
end GlobalTheory
