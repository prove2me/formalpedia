-- Prove2me | solution 1 for GlobalTheory.quotientSpanLinFormEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:09.965987+00:00
-- url     : https://prove2.me/submissions/98edc16d-1b5c-4013-947a-63e6e5474cbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk

set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {ι J : Type*} [Fintype J]
variable (u : J → R) {j₀ : J} (hu : IsUnit (u j₀))
namespace GlobalTheory
theorem _root_.solution (S : Set ι)
    (p : MvPolynomial {x : ι × J // x ∉ elimIndices S j₀} R) :
    (quotientSpanLinFormEquiv u hu S).symm p = Ideal.Quotient.mk _ (rename Subtype.val p) := by
  rw [AlgEquiv.symm_apply_eq, quotientSpanLinFormEquiv_mk, linFormElim_rename]
end GlobalTheory
