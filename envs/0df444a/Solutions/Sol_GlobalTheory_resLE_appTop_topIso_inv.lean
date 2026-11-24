-- Prove2me | solution 1 for GlobalTheory.resLE_appTop_topIso_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:31:15.125549+00:00
-- url     : https://prove2.me/submissions/d1542636-3b9c-459a-a758-e52a33f5ca2d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{0}} (t : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ t ⁻¹ᵁ U) (g : Γ(Y, U)) :
    (t.resLE U V e).appTop.hom (U.topIso.inv.hom g) = V.topIso.inv.hom ((t.appLE U V e).hom g) := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← CommRingCat.comp_apply,
    Iso.inv_hom_id_assoc, CommRingCat.comp_apply]
end GlobalTheory
