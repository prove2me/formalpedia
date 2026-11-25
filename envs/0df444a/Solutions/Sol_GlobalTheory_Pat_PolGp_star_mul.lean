-- Prove2me | solution 1 for GlobalTheory.Pat.PolGp.star_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:05:22.962165+00:00
-- url     : https://prove2.me/submissions/2185750c-5893-4671-8c84-dc4315b1e0eb

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
theorem _root_.solution (j : Φ.O →+* B) (x y : MonoidAlgebra B G.Γ) : star G j (x * y) = star G j y * star G j x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [PolGp.star_zero]
  | add a b ha hb => rw [add_mul, PolGp.star_add, PolGp.star_add, ha, hb, mul_add]
  | single g r =>
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp [PolGp.star_zero]
    | add a b ha hb => rw [mul_add, PolGp.star_add, PolGp.star_add, ha, hb, add_mul]
    | single h s =>
      rw [MonoidAlgebra.single_mul_single, PolGp.star_single, PolGp.star_single, PolGp.star_single, MonoidAlgebra.single_mul_single]
      congr 1
      · simp
      · simp only [map_mul, Units.val_mul]; ring
end PolGp
end GlobalTheory.Pat
