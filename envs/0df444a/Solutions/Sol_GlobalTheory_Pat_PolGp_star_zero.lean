-- Prove2me | solution 1 for GlobalTheory.Pat.PolGp.star_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:30:11.716937+00:00
-- url     : https://prove2.me/submissions/42bb079b-933d-4b8a-8a06-171d7e062cc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Polynomial IsLocalRing
noncomputable section
open IsLocalRing
open GlobalTheory GlobalTheory.Pat
attribute [instance] PG.grp PG.top PG.tgrp PG.cpt PG.t2 PG.td
attribute [instance] Frame.hl Frame.iO Frame.iOd Frame.iOv Frame.iVl Frame.iSt
variable {Φ : Frame} (G : PolGp Φ) {B : Type} [CommRing B]
namespace GlobalTheory.Pat
namespace PolGp
theorem _root_.solution (j : Φ.O →+* B) : star G j (0 : MonoidAlgebra B G.Γ) = 0 := by
  unfold star
  exact Finsupp.sum_zero_index
end PolGp
end GlobalTheory.Pat
