-- Prove2me | solution 1 for GlobalTheory.SiteCoh.res_map_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:18.276832+00:00
-- url     : https://prove2.me/submissions/1314c746-bd17-491d-8c78-610fd1677234

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_SubsingletonOfSubsingletonFreeSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe w v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
open GlobalTheory.SiteCoh
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
  {F G H : Sheaf J AddCommGrpCat.{v}} {n : ℕ} {U V W : C}
namespace GlobalTheory.SiteCoh
theorem _root_.solution (f : F ⟶ G) (i : V ⟶ U) (x : F.H' n U) :
    res G n i (map f n U x) = map f n V (res F n i x) :=
  (ConcreteCategory.congr_hom
    (((Sheaf.cohomologyPresheafFunctor J n).map f).naturality i.op) x).symm
end GlobalTheory.SiteCoh
