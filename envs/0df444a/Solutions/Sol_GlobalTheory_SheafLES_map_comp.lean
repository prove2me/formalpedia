-- Prove2me | solution 1 for GlobalTheory.SheafLES.map_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:48.454377+00:00
-- url     : https://prove2.me/submissions/ccfb2915-5757-4a48-8e40-76f049242297

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_GlobalTheory_SheafLES_map_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SheafLES.map_id

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
theorem _root_.solution (f : F ⟶ G) (g : G ⟶ K) (n : ℕ) (U : C) (x : Sheaf.H'.{w'} F n U) :
    map (f ≫ g) n U x = map g n U (map f n U x) := by
  have (y : Ext.{w'} ((freeYoneda J).obj U) F n) : y.comp (Ext.mk₀ (f ≫ g)) (add_zero n) =
      (y.comp (Ext.mk₀ f) (add_zero n)).comp (Ext.mk₀ g) (add_zero n) := by simp
  exact this x
end GlobalTheory.SheafLES
