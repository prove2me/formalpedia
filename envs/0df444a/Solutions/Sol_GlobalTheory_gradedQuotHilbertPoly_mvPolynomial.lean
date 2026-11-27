-- Prove2me | solution 1 for GlobalTheory.gradedQuotHilbertPoly_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:38:35.801144+00:00
-- url     : https://prove2.me/submissions/294aec10-e716-4eb9-b54b-f04b5beda880

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimQuotientOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_eventually_finrank_quotPiece
import Theorems.Thm_GlobalTheory_polynomial_eq_of_eventually_eval_nat
import Theorems.Thm_GlobalTheory_quotPiece_natCast


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module DirectSum
open GlobalTheory
variable {K T : Type*} [Field K] [CommRing T] [Algebra K T] (𝒜 : ℕ → Submodule K T)
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Finite ι] {I : Ideal (MvPolynomial ι K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι K)) :
    gradedQuotHilbertPoly (homogeneousSubmodule ι K) I = idealHilbertPoly I := by
  apply polynomial_eq_of_eventually_eval_nat
  filter_upwards [eventually_finrank_quotPiece hI, GradedBezout.eventually_finrank
    (fun i => isHomogeneous_X K i) (finite_adjoin_range_X ι) hI] with n h1 h2
  rw [← h1, ← h2, quotPiece_natCast, gradedQuotPiece_natCast]
end GlobalTheory
