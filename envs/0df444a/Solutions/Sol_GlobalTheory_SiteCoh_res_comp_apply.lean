-- Prove2me | solution 1 for GlobalTheory.SiteCoh.res_comp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:49:13.924665+00:00
-- url     : https://prove2.me/submissions/9f863139-53f0-445e-9cfb-c6d23ff2c441

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
theorem _root_.solution (i : V ⟶ U) (j : W ⟶ V) (x : F.H' n U) :
    res F n (j ≫ i) x = res F n j (res F n i x) := by
  simp only [res, op_comp, Functor.map_comp]; rfl
end GlobalTheory.SiteCoh
