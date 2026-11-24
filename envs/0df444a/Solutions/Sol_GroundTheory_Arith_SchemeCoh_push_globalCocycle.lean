-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.push_globalCocycle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:33.338268+00:00
-- url     : https://prove2.me/submissions/445389de-382d-49b5-8450-d8e5b50c3c71

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechToDerived
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_res


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
noncomputable section
open CategoryTheory Opposite TopologicalSpace Limits Abelian
universe w w' u
variable {X : TopCat.{u}}
variable {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
variable {P}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P')
    (s : P.obj (op ⊤)) :
    push U φ 0 (globalCocycle P U s).1 = (globalCocycle P' U (φ.app _ s)).1 :=
  funext fun _ => app_res φ _ s
end GroundTheory.Arith.SchemeCoh
