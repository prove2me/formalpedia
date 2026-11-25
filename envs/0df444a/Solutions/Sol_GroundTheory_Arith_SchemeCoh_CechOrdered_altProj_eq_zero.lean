-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.altProj_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:58:44.31573+00:00
-- url     : https://prove2.me/submissions/57f06c59-6d11-44a5-8e1f-fa7125d30fdb

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_altProj_apply_of_not_injective

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
theorem _root_.solution [Fintype ι] {q : ℕ} (hq : Fintype.card ι ≤ q) (σ : Cochain P U q) :
    altProj P U q σ = 0 := by
  funext i
  refine altProj_apply_of_not_injective q σ fun hi => ?_
  have := Fintype.card_le_of_injective i hi
  rw [Fintype.card_fin] at this
  omega
end GroundTheory.Arith.SchemeCoh.CechOrdered
