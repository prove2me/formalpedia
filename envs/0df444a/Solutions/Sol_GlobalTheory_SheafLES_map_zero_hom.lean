-- Prove2me | solution 1 for GlobalTheory.SheafLES.map_zero_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:48.357118+00:00
-- url     : https://prove2.me/submissions/a6e65b60-b57b-4fc5-b45d-c9666c2975ad

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
theorem _root_.solution (n : ℕ) (U : C) (x : Sheaf.H'.{w'} F n U) :
    map (0 : F ⟶ G) n U x = 0 := by
  have (y : Ext.{w'} ((freeYoneda J).obj U) F n) :
      y.comp (Ext.mk₀ (0 : F ⟶ G)) (add_zero n) = 0 := by simp
  exact this x
end GlobalTheory.SheafLES
