-- Prove2me | solution 1 for GlobalTheory.idealHilbertPoly_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:19:54.699267+00:00
-- url     : https://prove2.me/submissions/ff0ef015-7072-4a4a-9484-994ede200e1c

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Theorems.Thm_GlobalTheory_idealHilbertPoly_eq_zero_of_forall_X_mem

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
variable [Finite ι]
namespace GlobalTheory
theorem _root_.solution : idealHilbertPoly (⊤ : Ideal (MvPolynomial ι k)) = 0 :=
  idealHilbertPoly_eq_zero_of_forall_X_mem (Ideal.IsHomogeneous.top _) fun _ => trivial
end GlobalTheory
