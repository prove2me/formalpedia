-- Prove2me | solution 1 for GlobalTheory.SheafLES.res_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:29:07.484143+00:00
-- url     : https://prove2.me/submissions/48395faa-e6d5-4371-8bcb-a4f31ab968b1

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
theorem _root_.solution (f : F ⟶ G) (n : ℕ) {U V : C} (i : V ⟶ U) (x : Sheaf.H'.{w'} F n U) :
    res G n i (map f n U x) = map f n V (res F n i x) :=
  (ConcreteCategory.congr_hom
    (((Sheaf.cohomologyPresheafFunctor.{w'} J n).map f).naturality i.op) x).symm
end GlobalTheory.SheafLES
