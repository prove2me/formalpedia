-- Prove2me | solution 1 for GlobalTheory.FlatDescent.appTop_resLE_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:32.898006+00:00
-- url     : https://prove2.me/submissions/c68e7f9d-8c5d-4754-992e-61837ef00050

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory
open GlobalTheory.FlatDescent
universe u
variable {X Y Z : Scheme.{u}}
namespace GlobalTheory.FlatDescent
theorem _root_.solution (f : Z ⟶ Y) (V : Y.Opens) (W : Z.Opens) (e : W ≤ f ⁻¹ᵁ V)
    (s : Γ(Y, V)) : (f.resLE V W e).appTop (V.topIso.inv s) = W.topIso.inv (f.appLE V W e s) := by
  have : V.topIso.inv ≫ (f.resLE V W e).appTop = f.appLE V W e ≫ W.topIso.inv := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Iso.inv_hom_id_assoc]
  exact congr($this s)
end GlobalTheory.FlatDescent
