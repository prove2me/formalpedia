-- Prove2me | solution 1 for GlobalTheory.Flasque.connecting_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:52.827414+00:00
-- url     : https://prove2.me/submissions/1408a362-0cf3-47bd-902d-73da6a733b70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w v u
open GlobalTheory
open GlobalTheory.Flasque
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
namespace GlobalTheory.Flasque
theorem _root_.solution (n : ℕ) {V U : C} (i : V ⟶ U) (x : S.X₃.H' n U) :
    connecting hS n V ((S.X₃.cohomologyPresheaf n).map i.op x) =
      (S.X₁.cohomologyPresheaf (n + 1)).map i.op (connecting hS n U x) :=
  Ext.comp_assoc (Ext.mk₀ (freeSheafMap J i)) x hS.extClass (zero_add n) rfl (by lia)
end GlobalTheory.Flasque
