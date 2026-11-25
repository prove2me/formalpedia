-- Prove2me | solution 1 for GlobalTheory.Pat.PolGp.star_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:05:26.064392+00:00
-- url     : https://prove2.me/submissions/fdfa7f38-ac01-46b5-92b7-ea6222439301

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
import Theorems.Thm_GlobalTheory_Pat_PolGp_star_single
import Theorems.Thm_GlobalTheory_Pat_PolGp_star_zero
import Theorems.Thm_GlobalTheory_Pat_PolGp_star_add

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
theorem _root_.solution (j : Φ.O →+* B) (x : MonoidAlgebra B G.Γ) : star G j (star G j x) = x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [PolGp.star_zero]
  | add a b ha hb => rw [PolGp.star_add, PolGp.star_add, ha, hb]
  | single g r =>
    rw [PolGp.star_single, PolGp.star_single, map_inv, G.sig_sig, inv_inv, map_inv, G.mu_sig, mul_assoc, ← map_mul,
      Units.mul_inv, map_one, mul_one]
end PolGp
end GlobalTheory.Pat
