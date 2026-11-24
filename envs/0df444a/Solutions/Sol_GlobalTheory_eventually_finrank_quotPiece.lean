-- Prove2me | solution 1 for GlobalTheory.eventually_finrank_quotPiece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:01:25.113878+00:00
-- url     : https://prove2.me/submissions/132c1cc5-2993-4392-8568-bd1e01317d35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Theorems.Thm_GlobalTheory_isHilbertPoly_idealHilbertPoly

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
    ∀ᶠ n : ℕ in atTop, (finrank k (quotPiece I n) : ℚ) = (idealHilbertPoly I).eval (n : ℚ) := by
  have := (tendsto_natCast_atTop_atTop (R := ℤ)).eventually
    (isHilbertPoly_idealHilbertPoly hI).eventually_eq
  simpa using this
end GlobalTheory
