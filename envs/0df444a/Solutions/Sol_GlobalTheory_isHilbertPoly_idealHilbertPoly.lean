-- Prove2me | solution 1 for GlobalTheory.isHilbertPoly_idealHilbertPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:53:06.105429+00:00
-- url     : https://prove2.me/submissions/c853a9b1-7751-4821-a1c3-4abe8c191985

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Theorems.Thm_GlobalTheory_exists_isHilbertPoly_quotPiece

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
    IsHilbertPoly (quotPiece I) (idealHilbertPoly I) := by
  cases nonempty_fintype ι
  have h : ∃ P, IsHilbertPoly (quotPiece I) P :=
    (exists_isHilbertPoly_quotPiece hI).imp fun _ h => h.1
  rw [idealHilbertPoly, dif_pos h]
  exact h.choose_spec
end GlobalTheory
