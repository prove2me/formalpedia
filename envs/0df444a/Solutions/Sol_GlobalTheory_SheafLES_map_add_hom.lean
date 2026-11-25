-- Prove2me | solution 1 for GlobalTheory.SheafLES.map_add_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:09:48.708678+00:00
-- url     : https://prove2.me/submissions/dc118e12-0487-470c-90d5-755ebb930a83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_GlobalTheory_SheafLES_map_id
import Theorems.Thm_GlobalTheory_SheafLES_map_zero_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SheafLES.map_id
attribute [local simp] GlobalTheory.SheafLES.map_zero_hom

set_option autoImplicit false
universe w' v u
open CategoryTheory Limits Abelian Opposite
noncomputable section
open GlobalTheory
open GlobalTheory.SheafLES
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
variable {F G K : Sheaf J AddCommGrpCat.{v}}
namespace GlobalTheory.SheafLES
theorem _root_.solution (f g : F ⟶ G) (n : ℕ) (U : C) (x : Sheaf.H'.{w'} F n U) :
    map (f + g) n U x = map f n U x + map g n U x := by
  have (y : Ext.{w'} ((freeYoneda J).obj U) F n) :
      y.comp (Ext.mk₀ (f + g)) (add_zero n) =
        y.comp (Ext.mk₀ f) (add_zero n) + y.comp (Ext.mk₀ g) (add_zero n) := by
    simp [Ext.mk₀_add]
  exact this x
end GlobalTheory.SheafLES
