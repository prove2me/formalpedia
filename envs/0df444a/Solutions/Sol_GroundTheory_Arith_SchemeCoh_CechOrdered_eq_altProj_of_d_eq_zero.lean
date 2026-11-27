-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.eq_altProj_of_d_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:44:10.424747+00:00
-- url     : https://prove2.me/submissions/2061e284-2318-4fc9-a1c1-24dd3c817dd0

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_homotopy_d_zero

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
theorem _root_.solution (σ : Cochain P U 0) (hσ : d P U 0 σ = 0) :
    altProj P U 0 σ = σ := by
  have := homotopy_d_zero σ
  rw [hσ, map_zero] at this
  exact (sub_eq_zero.mp this.symm).symm
end GroundTheory.Arith.SchemeCoh.CechOrdered
