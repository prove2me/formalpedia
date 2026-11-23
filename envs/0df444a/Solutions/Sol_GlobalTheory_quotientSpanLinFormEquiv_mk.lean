-- Prove2me | solution 1 for GlobalTheory.quotientSpanLinFormEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:02.056538+00:00
-- url     : https://prove2.me/submissions/a4dbeb5b-8869-4234-9c95-d563294bd81f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {ι J : Type*} [Fintype J]
variable (u : J → R) {j₀ : J} (hu : IsUnit (u j₀))
namespace GlobalTheory
theorem _root_.solution (S : Set ι) (p : MvPolynomial (ι × J) R) :
    quotientSpanLinFormEquiv u hu S (Ideal.Quotient.mk _ p) = linFormElim u hu S p := rfl
end GlobalTheory
