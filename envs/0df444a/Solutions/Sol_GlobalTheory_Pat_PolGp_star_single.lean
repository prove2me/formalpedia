-- Prove2me | solution 1 for GlobalTheory.Pat.PolGp.star_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:33.666539+00:00
-- url     : https://prove2.me/submissions/2c5beb61-5a11-4627-83a8-23f3feeda7fe

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
theorem _root_.solution (j : Φ.O →+* B) (g : G.Γ) (a : B) : star G j (MonoidAlgebra.single g a) =
    MonoidAlgebra.single (G.sig g)⁻¹ (a * j ((G.mu g : Φ.Oˣ) : Φ.O)) := by
  unfold star
  rw [MonoidAlgebra.coeff_single, Finsupp.sum_single_index]
  simp
end PolGp
end GlobalTheory.Pat
