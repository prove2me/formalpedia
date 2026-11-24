-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.actC_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:08.044852+00:00
-- url     : https://prove2.me/submissions/ffec6766-a4d2-4f19-9fd6-8b31fd0a7a9c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech

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
theorem _root_.solution (r : R) (n : ℕ) (σ : Cochain P U n) (i : Fin (n + 1) → ι) :
    actC A U r n σ i = A.act r _ (σ i) := rfl
end GroundTheory.Arith.SchemeCoh
