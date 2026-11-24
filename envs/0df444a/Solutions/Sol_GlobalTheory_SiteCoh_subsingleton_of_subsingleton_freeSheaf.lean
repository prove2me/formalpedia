-- Prove2me | solution 1 for GlobalTheory.SiteCoh.subsingleton_of_subsingleton_freeSheaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:49:15.327015+00:00
-- url     : https://prove2.me/submissions/e7a09017-ccaa-426e-b643-66277e5f03fc

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
theorem _root_.solution (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C)
    [Subsingleton (((freeSheaf J).obj U).obj.obj (op U))] : Subsingleton (F.H' n U) := by
  have h : 𝟙 ((freeSheaf J).obj U) = 0 :=
    (freeSheafHomEquiv U _).injective (Subsingleton.elim _ _)
  refine subsingleton_of_forall_eq 0 fun x ↦ (extEquiv F n U).injective ?_
  rw [← Ext.mk₀_id_comp (extEquiv F n U x), h, Ext.mk₀_zero, Ext.zero_comp, map_zero]
end GlobalTheory.SiteCoh
