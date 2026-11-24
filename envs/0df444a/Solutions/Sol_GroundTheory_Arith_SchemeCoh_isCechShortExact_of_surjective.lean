-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isCechShortExact_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:12.230809+00:00
-- url     : https://prove2.me/submissions/3cd2f82a-ecbd-4547-90cd-700d1fd81885

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechToDerived
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_exact_of_shortExact
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_injective_of_shortExact
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_comp_hom_eq_zero


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
variable {ι : Type w}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (U : ι → Opens X)
    (hsurj : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Surjective (S.g.hom.app (op (inter U i)))) :
    IsCechShortExact U S.f.hom S.g.hom :=
  ⟨comp_hom_eq_zero, fun _ => app_injective_of_shortExact hS _,
    fun _ y hy => app_exact_of_shortExact hS _ y hy, hsurj⟩
end GroundTheory.Arith.SchemeCoh
