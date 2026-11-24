-- Prove2me | solution 1 for GlobalTheory.jacAlt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:20:03.162868+00:00
-- url     : https://prove2.me/submissions/8a556f01-731e-4414-a9d1-a90162789795

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Theorems.Thm_GlobalTheory_jacFormAlt_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] {D : ℕ}
open KaehlerDifferential
namespace GlobalTheory
theorem _root_.solution (f : Fin (D + 1) → A) : jacobianMultilinear R A D f = jac R f :=
  jacFormAlt_apply _ _ f
end GlobalTheory
