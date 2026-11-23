-- Prove2me | solution 1 for GlobalTheory.SheafLES.res_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:24.832797+00:00
-- url     : https://prove2.me/submissions/79ea2517-8369-4a8a-9ace-d5a32251c2bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (n : ℕ) {U V : C} (i : V ⟶ U) (x : Ext.{w'} ((freeYoneda J).obj U) F n) :
    res F n i x = (Ext.mk₀ ((freeYoneda J).map i)).comp x (zero_add n) := rfl
end GlobalTheory.SheafLES
