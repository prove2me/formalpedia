-- Prove2me | solution 1 for GlobalTheory.SheafPull.extMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:59.202801+00:00
-- url     : https://prove2.me/submissions/75f776d0-cc8a-47b7-835d-7e845b9904b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w w' w'' v u u₁ v₁ u₂ v₂
noncomputable section
open GlobalTheory
open GlobalTheory.SheafPull
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasExt.{w} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasExt.{w'} B]
  (Φ : A ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
namespace GlobalTheory.SheafPull
theorem _root_.solution {Z F : A} {Z' G : B} (a : Z' ⟶ Φ.obj Z) (b : Φ.obj F ⟶ G) (n : ℕ)
    (x : Ext.{w} Z F n) :
    extMap.{w, w'} Φ a b n x = (Ext.mk₀ a).comp
      ((x.mapExactFunctor Φ).comp (Ext.mk₀ b) (add_zero n)) (zero_add n) := rfl
end GlobalTheory.SheafPull
