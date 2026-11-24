-- Prove2me | solution 1 for GlobalTheory.Flasque.connecting_naturality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:51.93248+00:00
-- url     : https://prove2.me/submissions/1e65140f-1c1a-49a6-8655-0ecdfcb04880

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
theorem _root_.solution {T : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) (U : C) (x : S.X₃.H' n U) :
    connecting hT n U (((Sheaf.cohomologyPresheafFunctor J n).map φ.τ₃).app (op U) x) =
      ((Sheaf.cohomologyPresheafFunctor J (n + 1)).map φ.τ₁).app (op U) (connecting hS n U x) := by
  have key (y : Ext (freeSheaf J U) S.X₃ n) :
      (y.comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp hT.extClass rfl =
        (y.comp hS.extClass rfl).comp (Ext.mk₀ φ.τ₁) (add_zero (n + 1)) := by
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
      hS.extClass_naturality hT φ]
  exact key x
end GlobalTheory.Flasque
