-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.altProj_apply_of_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:38.49113+00:00
-- url     : https://prove2.me/submissions/9df86e73-b2f5-4e4e-ba24-a2d7e62acce0

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_proj_of_strictMono

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
theorem _root_.solution (q : ℕ) (σ : Cochain P U q) {i : Fin (q + 1) → ι}
    (hi : StrictMono i) : altProj P U q σ i = σ i := by
  rw [altProj_apply, proj_of_strictMono q i hi, pair_single _ _ _ le_rfl, one_smul, res_refl]
end GroundTheory.Arith.SchemeCoh.CechOrdered
