-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.homotopy_d_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:36.679611+00:00
-- url     : https://prove2.me/submissions/a0f9bc28-1704-40ef-8975-0cb5ff4215be

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_homotopy_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u
open GroundTheory.Arith.SchemeCoh.CechOrdered
variable {ι : Type w} [LinearOrder ι] {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (U : ι → Opens X)
variable {P U}
namespace GroundTheory.Arith.SchemeCoh.CechOrdered
theorem _root_.solution (σ : Cochain P U 0) :
    homotopy P U 0 (d P U 0 σ) = σ - altProj P U 0 σ := by
  funext i
  rw [homotopy_apply, Pi.sub_apply, altProj_apply]
  change pair _ _ 0 = σ i - pair σ (inter U i) (Finsupp.single i 1)
  rw [map_zero, pair_single _ _ _ le_rfl, one_smul, res_refl, sub_self]
end GroundTheory.Arith.SchemeCoh.CechOrdered
