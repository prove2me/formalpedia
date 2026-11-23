-- Prove2me | solution 1 for GlobalTheory.Pat.PolGp.star_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:52.687882+00:00
-- url     : https://prove2.me/submissions/03e72f52-94f1-480f-add3-c672c3bd592f

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
theorem _root_.solution (j : Φ.O →+* B) (x y : MonoidAlgebra B G.Γ) : star G j (x + y) = star G j x + star G j y := by
  unfold star
  rw [MonoidAlgebra.coeff_add, Finsupp.sum_add_index']
  · simp
  · intro a b c; rw [add_mul, MonoidAlgebra.single_add]
end PolGp
end GlobalTheory.Pat
