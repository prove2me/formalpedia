-- Prove2me | solution 1 for GlobalTheory.WittTransitivity.conj_hform
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:10.754067+00:00
-- url     : https://prove2.me/submissions/68fb3edd-4eb3-49ea-92e0-3e95d5c68018

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
theorem _root_.solution (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = J i j) (x y : Fin M → A) :
    c (hform c J x y) = hform c J y x := by
  simp only [Formalism.UG.hform, map_sum, map_mul, hc, hJ]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
end GlobalTheory.WittTransitivity
