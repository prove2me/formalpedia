-- Prove2me | solution 1 for GlobalTheory.WittTransitivity.hform_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:50.567738+00:00
-- url     : https://prove2.me/submissions/d5a3693e-ad61-453e-8d0a-3d3d8805f003

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
theorem _root_.solution (x y : Fin M → A) :
    hform c J x y = ∑ j, hform c J x (Pi.single j 1) * y j := by
  have key : ∀ j, hform c J x (Pi.single j 1) = ∑ i, c (x i) * J i j := by
    intro j
    simp [Formalism.UG.hform, Pi.single_apply]
  simp_rw [key]
  simp only [Formalism.UG.hform, Finset.sum_mul]
  exact Finset.sum_comm
end GlobalTheory.WittTransitivity
