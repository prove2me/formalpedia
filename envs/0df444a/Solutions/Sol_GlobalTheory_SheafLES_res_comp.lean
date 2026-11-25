-- Prove2me | solution 1 for GlobalTheory.SheafLES.res_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:09:51.975868+00:00
-- url     : https://prove2.me/submissions/40af3cb4-6d4e-42be-8501-f7af3e9fee13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_GlobalTheory_SheafLES_map_id
import Theorems.Thm_GlobalTheory_SheafLES_map_zero_hom
import Theorems.Thm_GlobalTheory_SheafLES_res_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SheafLES.map_id
attribute [local simp] GlobalTheory.SheafLES.map_zero_hom
attribute [local simp] GlobalTheory.SheafLES.res_id

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
theorem _root_.solution (n : ℕ) {U V W : C} (i : V ⟶ U) (j : W ⟶ V) (x : Sheaf.H'.{w'} F n U) :
    res F n (j ≫ i) x = res F n j (res F n i x) := by
  simp [res]
end GlobalTheory.SheafLES
