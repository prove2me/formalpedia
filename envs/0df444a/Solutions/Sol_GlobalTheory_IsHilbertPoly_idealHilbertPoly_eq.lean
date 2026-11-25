-- Prove2me | solution 1 for GlobalTheory.IsHilbertPoly.idealHilbertPoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:53:52.07834+00:00
-- url     : https://prove2.me/submissions/5a3c6864-bffd-4f46-9b6b-ce8d6c1e47e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Theorems.Thm_GlobalTheory_IsHilbertPoly_unique


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
namespace IsHilbertPoly
theorem _root_.solution {I : Ideal (MvPolynomial ι k)} {P : ℚ[X]}
    (hP : IsHilbertPoly (quotPiece I) P) : idealHilbertPoly I = P := by
  have h : ∃ P, IsHilbertPoly (quotPiece I) P := ⟨P, hP⟩
  rw [idealHilbertPoly, dif_pos h]
  exact h.choose_spec.unique hP
end IsHilbertPoly
end GlobalTheory
