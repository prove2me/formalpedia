-- Prove2me | solution 1 for GlobalTheory.SheafPull.extMap_extClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:47:03.030935+00:00
-- url     : https://prove2.me/submissions/fe571255-8e21-4bb5-a53f-01fd77ebbd1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
import Theorems.Thm_GlobalTheory_SheafPull_extMap_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w w' w'' v u u₁ v₁ u₂ v₂
noncomputable section
namespace GlobalTheory
namespace SheafPull
section Abstract
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasExt.{w} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasExt.{w'} B]
  (Φ : A ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
private lemma comp_comp_mk0_eq_comp_comp_of_square {X₀ X₁ X₂ X₃ Y₂ Y₃ : B} {n : ℕ} (a : Ext.{w'} X₀ X₁ 0)
    (y : Ext.{w'} X₁ X₂ n) (e : Ext.{w'} X₂ X₃ 1) (t₃ : X₃ ⟶ Y₃) (t₂ : X₂ ⟶ Y₂)
    (f : Ext.{w'} Y₂ Y₃ 1)
    (h : e.comp (Ext.mk₀ t₃) (add_zero 1) = (Ext.mk₀ t₂).comp f (zero_add 1)) :
    a.comp ((y.comp e rfl).comp (Ext.mk₀ t₃) (add_zero _)) (zero_add _) =
      (a.comp (y.comp (Ext.mk₀ t₂) (add_zero n)) (zero_add n)).comp f rfl := by
  rw [Ext.comp_assoc_of_third_deg_zero, h, ← Ext.comp_assoc_of_second_deg_zero]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm
end Abstract
section Site
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  (p : C ⥤ D) [p.IsContinuous J K]
  [(p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).IsRightAdjoint]
open SheafLES
variable [PreservesFiniteLimits (p.sheafPullback AddCommGrpCat.{v} J K)]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{v})]
  {F F' : Sheaf J AddCommGrpCat.{v}} {G G' : Sheaf K AddCommGrpCat.{v}}
end Site
end SheafPull
end GlobalTheory
end
end

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
theorem _root_.solution {Z : A} {Z' : B} (a : Z' ⟶ Φ.obj Z) {S : ShortComplex A}
    {T : ShortComplex B} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S.map Φ ⟶ T) (n : ℕ)
    (x : Ext.{w} Z S.X₃ n) :
    extMap.{w, w'} Φ a (F := S.X₁) φ.τ₁ (n + 1) (x.comp hS.extClass rfl) =
      (extMap.{w, w'} Φ a (F := S.X₃) φ.τ₃ n x).comp hT.extClass rfl := by
  erw [extMap_apply, extMap_apply]
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact comp_comp_mk0_eq_comp_comp_of_square _ _ _ _ _ _ ((hS.map_of_exact Φ).extClass_naturality hT φ)
end GlobalTheory.SheafPull
