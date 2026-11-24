-- Prove2me | solution 1 for GlobalTheory.SheafPull.sitePull_bijective_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:15:02.00056+00:00
-- url     : https://prove2.me/submissions/1434afcb-d7bd-4a84-88f6-b7cc1d44ef39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
import Theorems.Thm_GlobalTheory_SheafPull_sitePull_map
import Theorems.Thm_GlobalTheory_SheafPull_map_sitePull
import Theorems.Thm_P2M_GlobalTheory_SheafPull_sitePull___e9f696f6870b
import Theorems.Thm_P2M_GlobalTheory_SheafLES___map_026ec4bafb10
import Theorems.Thm_P2M_GlobalTheory_SheafLES___surjective_of_subsingleton_5836d34aca61
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__24269ba80ece
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GlobalTheory_SheafLES___map_026ec4bafb10



set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w w' w'' v u u₁ v₁ u₂ v₂
noncomputable section
open GlobalTheory
open GlobalTheory.SheafPull
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  (p : C ⥤ D) [p.IsContinuous J K]
  [(p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).IsRightAdjoint]
open SheafLES
variable [PreservesFiniteLimits (p.sheafPullback AddCommGrpCat.{v} J K)]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{v})]
  {F F' : Sheaf J AddCommGrpCat.{v}} {G G' : Sheaf K AddCommGrpCat.{v}}
namespace GlobalTheory.SheafPull
theorem _root_.solution {S : ShortComplex (Sheaf J AddCommGrpCat.{v})}
    {T : ShortComplex (Sheaf K AddCommGrpCat.{v})} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T.map (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K)) (n : ℕ)
    {V : C} {W : D} (i : W ⟶ p.obj V)
    (h₂ : Function.Surjective (sitePull.{w, w'} p (G := T.X₂) φ.τ₂ n i))
    (h₃ : Function.Bijective (sitePull.{w, w'} p (G := T.X₃) φ.τ₃ n i))
    (hV : Subsingleton (Sheaf.H'.{w} S.X₂ (n + 1) V))
    (hW : Subsingleton (Sheaf.H'.{w'} T.X₂ (n + 1) W)) :
    Function.Bijective (sitePull.{w, w'} p (G := T.X₁) φ.τ₁ (n + 1) i) := by
  have hδS := δ_surjective_of_subsingleton hS n V hV
  have hδT := δ_surjective_of_subsingleton hT n W hW
  have hg : ∀ y, sitePull.{w, w'} p (G := T.X₃) φ.τ₃ n i (map S.g n V y) =
      map T.g n W (sitePull.{w, w'} p (G := T.X₂) φ.τ₂ n i y) := by
    intro y
    refine (sitePull_map p _ S.g n i y).trans ?_
    refine Eq.trans ?_ (map_sitePull p _ T.g n i y).symm
    exact congrArg (fun f => sitePull.{w, w'} p f n i y) φ.comm₂₃.symm
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨z, rfl⟩ := hδS a
    have ha' := (sitePull_δ p hS hT φ n i z).symm.trans ha
    obtain ⟨y, hy⟩ := ((exact₃ hT n W) _).1 ha'
    obtain ⟨y', rfl⟩ := h₂ y
    have hz : z = map S.g n V y' := h₃.1 ((hg y').trans hy).symm
    rw [hz, δ_map]
  · intro b
    obtain ⟨z, rfl⟩ := hδT b
    obtain ⟨z', rfl⟩ := h₃.2 z
    exact ⟨δ hS n V z', sitePull_δ p hS hT φ n i z'⟩
end GlobalTheory.SheafPull
