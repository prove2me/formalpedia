-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.d_actC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:52:39.526438+00:00
-- url     : https://prove2.me/submissions/95d4262c-5836-438c-9922-98d102ce7788

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_actC_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_apply


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
universe u
variable {X : TopCat.{u}} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {R : Type u} [CommRing R]
variable {D : R → Opens X} (A : LocalizingAction P D)
variable {ι : Type u} (U : ι → Opens X)
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (r : R) (n : ℕ) (σ : Cochain P U n) :
    d P U n (actC A U r n σ) = actC A U r (n + 1) (d P U n σ) := by
  funext i
  simp only [actC_apply, d_apply, map_sum, map_zsmul, A.res_act]
end GroundTheory.Arith.SchemeCoh
