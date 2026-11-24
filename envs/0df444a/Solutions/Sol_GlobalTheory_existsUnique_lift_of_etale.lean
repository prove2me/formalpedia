-- Prove2me | solution 1 for GlobalTheory.existsUnique_lift_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:55:39.493626+00:00
-- url     : https://prove2.me/submissions/d17c0fdc-3cef-47ac-82a9-9106f020b28a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_GlobalTheory_eq_of_surjective_of_unramified
import Theorems.Thm_GlobalTheory_surjective_of_isNilpotent_ker
import Theorems.Thm_GlobalTheory_exists_local_lift_of_smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X S T₀ T : Scheme.{u}} (f : X ⟶ S) [Etale f]
    (i : T₀ ⟶ T) [IsClosedImmersion i] (hi : IsNilpotent i.ker)
    (g : T₀ ⟶ X) (h : T ⟶ S) (w : g ≫ f = i ≫ h) :
    ∃! l : T ⟶ X, i ≫ l = g ∧ l ≫ f = h := by
  have := surjective_of_isNilpotent_ker i hi
  refine existsUnique_of_exists_of_unique ?_ fun l₁ l₂ h₁ h₂ ↦
    eq_of_surjective_of_unramified f (h₁.2.trans h₂.2.symm) i (h₁.1.trans h₂.1.symm)
  choose W hW l hl hl' using exists_local_lift_of_smooth f i hi g h w
  have key : ∀ (t : T) {Z : Scheme.{u}} (a : Z ⟶ W t) (b : Z ⟶ T₀), a ≫ (W t).ι = b ≫ i →
      a ≫ l t = b ≫ g := fun t Z a b e ↦ by
    obtain ⟨c, hc₁, hc₂⟩ := (isPullback_morphismRestrict i (W t)).exists_lift a b e
    rw [← hc₁, ← hc₂, Category.assoc, hl', Category.assoc]
  have hcov : IsOpenCover W := by
    rw [IsOpenCover, eq_top_iff]
    exact fun t _ ↦ Opens.mem_iSup.mpr ⟨t, hW t⟩
  let 𝒰 := T.openCoverOfIsOpenCover W hcov
  have hcomp : ∀ s t : T, pullback.fst (W s).ι (W t).ι ≫ l s = pullback.snd _ _ ≫ l t := by
    intro s t
    refine eq_of_surjective_of_unramified f ?_
      (pullback.fst (pullback.fst (W s).ι (W t).ι ≫ (W s).ι) i) ?_
    · simp [hl, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc, key s _ (pullback.snd _ _),
        key t _ (pullback.snd _ _)]
      · rw [Category.assoc, ← pullback.condition (f := (W s).ι)]
        exact pullback.condition
      · rw [Category.assoc]
        exact pullback.condition
  have hL : ∀ t : T, (W t).ι ≫ 𝒰.glueMorphisms l hcomp = l t :=
    fun t ↦ 𝒰.ι_glueMorphisms l hcomp t
  refine ⟨𝒰.glueMorphisms l hcomp, ?_, ?_⟩
  · refine Scheme.hom_ext_of_forall _ _ fun x ↦ ⟨i ⁻¹ᵁ W (i x), hW _, ?_⟩
    rw [← morphismRestrict_ι_assoc, hL, hl']
  · refine Scheme.hom_ext_of_forall _ _ fun x ↦ ⟨W x, hW _, ?_⟩
    rw [reassoc_of% hL, hl]
end GlobalTheory
