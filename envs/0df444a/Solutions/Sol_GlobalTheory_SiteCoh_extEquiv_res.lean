-- Prove2me | solution 1 for GlobalTheory.SiteCoh.extEquiv_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:49:12.528219+00:00
-- url     : https://prove2.me/submissions/36dc0b4f-b315-4d3f-a318-45d8cfce85fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_SubsingletonOfSubsingletonFreeSheaf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Opposite Limits Abelian
universe w v u
noncomputable section
open GlobalTheory GlobalTheory.SiteCoh
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
namespace GlobalTheory.SiteCoh
theorem _root_.solution (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U V : C} (i : V ⟶ U)
    (x : F.H' n U) :
    extEquiv F n V (res F n i x) =
      (Ext.mk₀ ((freeSheaf J).map i)).comp (extEquiv F n U x) (zero_add n) := rfl
end GlobalTheory.SiteCoh
