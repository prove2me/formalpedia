-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.altProj_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:35.750673+00:00
-- url     : https://prove2.me/submissions/7e186af2-8a69-4205-865e-f393a519c571

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered

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
theorem _root_.solution (q : ℕ) {σ σ' : Cochain P U q} (h : ∀ t, StrictMono t → σ t = σ' t) :
    altProj P U q σ = altProj P U q σ' := by
  funext i
  refine eq_of_supp (pair σ (inter U i)) (pair σ' (inter U i)) (proj_supp q i) fun t k ht => ?_
  have hle := inter_le_of_inRange U ht.2
  rw [pair_single _ _ _ hle, pair_single _ _ _ hle, h t ht.1]
end GroundTheory.Arith.SchemeCoh.CechOrdered
