-- Prove2me | solution 1 for GlobalTheory.WittTransitivity.hform_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:52.060416+00:00
-- url     : https://prove2.me/submissions/d3d532b6-aed7-4a03-8f18-b89b7460f042

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open Formalism.UG
open GlobalTheory GlobalTheory.WittTransitivity
variable {A : Type} [CommRing A] (c : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)
namespace GlobalTheory.WittTransitivity
theorem _root_.solution (x y z : Fin M → A) :
    hform c J x (y - z) = hform c J x y - hform c J x z := by
  simp only [Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
end GlobalTheory.WittTransitivity
