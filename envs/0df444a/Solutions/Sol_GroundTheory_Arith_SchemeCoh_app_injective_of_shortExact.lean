-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.app_injective_of_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:03.365865+00:00
-- url     : https://prove2.me/submissions/a22bfc1e-fff0-4a4e-b58d-646c8dfba3d5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InjectiveCech
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan

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
open CategoryTheory Opposite TopologicalSpace Limits
universe w u
variable {X : TopCat.{u}}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P)
variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
include hS
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (W : (Opens X)ᵒᵖ) : Function.Injective (S.f.hom.app W) := by
  have : Mono S.f := hS.mono_f
  have : Mono S.f.hom := (TopCat.Sheaf.forget AddCommGrpCat.{u} X).map_mono S.f
  exact (AddCommGrpCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 this W)
end GroundTheory.Arith.SchemeCoh
