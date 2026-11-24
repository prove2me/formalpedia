-- Prove2me | solution 1 for GlobalTheory.jac_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:10.067589+00:00
-- url     : https://prove2.me/submissions/0a05a307-eeaf-4741-9219-936599d0d4da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Theorems.Thm_GlobalTheory_jacForm_mul

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
theorem _root_.solution (h : A) (f : Fin (D + 1) → A) :
    jac R (fun i => h * f i) = h ^ (D + 1) • jac R f :=
  jacForm_mul _ _ h f
end GlobalTheory
