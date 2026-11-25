-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.altProj_apply_of_not_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:39.053521+00:00
-- url     : https://prove2.me/submissions/735b51b1-a8ab-4e63-bd61-f270127d8500

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_proj_eq_zero_of_not_injective

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
    (hi : ¬ Function.Injective i) : altProj P U q σ i = 0 := by
  rw [altProj_apply, proj_eq_zero_of_not_injective q i hi, map_zero]
end GroundTheory.Arith.SchemeCoh.CechOrdered
