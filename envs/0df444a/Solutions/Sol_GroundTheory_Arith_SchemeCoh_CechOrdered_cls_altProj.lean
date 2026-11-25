-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.cls_altProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:53:01.936422+00:00
-- url     : https://prove2.me/submissions/a66b1aa7-ca2f-4b66-a7e6-90669abbf9d7

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_exists_d_eq_sub_altProj

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
theorem _root_.solution (q : ℕ) (σ : Cochain P U (q + 1)) (hσ : d P U (q + 1) σ = 0) :
    cls (altProj P U (q + 1) σ) (by rw [d_altProj, hσ, map_zero]) = cls σ hσ := by
  rw [cls_eq_cls_iff, coboundaries_succ]
  obtain ⟨τ, hτ⟩ := exists_d_eq_sub_altProj q σ hσ
  exact ⟨τ, hτ⟩
end GroundTheory.Arith.SchemeCoh.CechOrdered
