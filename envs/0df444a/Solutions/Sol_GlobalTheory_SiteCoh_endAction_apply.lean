-- Prove2me | solution 1 for GlobalTheory.SiteCoh.endAction_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:49:11.903803+00:00
-- url     : https://prove2.me/submissions/b9a5a3ca-bfe9-4a06-b729-6d2a939de90c

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
theorem _root_.solution (f : End F) (x : F.H' n U) : endAction F n U f x = map f n U x := rfl
end GlobalTheory.SiteCoh
