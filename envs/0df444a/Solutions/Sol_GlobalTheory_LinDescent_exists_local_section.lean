-- Prove2me | solution 1 for GlobalTheory.LinDescent.exists_local_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:45:12.226921+00:00
-- url     : https://prove2.me/submissions/2326df23-b24e-4e61-a42a-da7ffe433d0d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Theorems.Thm_GlobalTheory_FinEt_exists_algClosed_point
import Theorems.Thm_GlobalTheory_FunDescent_hom_ext
import Theorems.Thm_GlobalTheory_isOpenImmersion_of_section_of_etale


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
namespace GlobalTheory.LinDescent
theorem _root_.solution (ψ : A ⟶ B) [Etale ψ.left] {C : Type} (i : C → (𝟙_ (Over S) ⟶ A))
    (hi : ∀ c, i c ≫ ψ = 1)
    (hk : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A),
      x ≫ ψ = 1 → ∃ c, x = toUnit _ ≫ i c)
    {Z : Over S} (d : Z ⟶ A) (hd : d ≫ ψ = 1) (p : Z.left) :
    ∃ (c : C) (W : Over S) (a : W ⟶ Z) (_ : IsOpenImmersion a.left),
      p ∈ Set.range a.left ∧ a ≫ d = toUnit W ≫ i c := by
  have hone : ∀ {Z : Over S}, (1 : Z ⟶ B).left = Z.hom ≫ η[B].left := fun {Z} => by
    rw [Hom.one_def, Over.comp_left]; rfl
  have hη : η[B].left ≫ B.hom = 𝟙 _ := Over.w η[B]
  have hker : ∀ {Z : Over S} (d : Z ⟶ A), d ≫ ψ = 1 → d.left ≫ ψ.left = Z.hom ≫ η[B].left :=
    fun d hd => by rw [← Over.comp_left, hd, hone]
  let l : Z.left ⟶ pullback ψ.left η[B].left := pullback.lift _ _ (hker d hd)
  obtain ⟨k, _, _, q, hq⟩ := FinEt.exists_algClosed_point _ (l p)
  have hw : (q ≫ pullback.fst ψ.left η[B].left) ≫ A.hom = q ≫ pullback.snd ψ.left η[B].left := by
    rw [← Over.w ψ, Category.assoc, pullback.condition_assoc]
    erw [hη]
    exact congrArg (q ≫ ·) (Category.comp_id _)
  obtain ⟨c, hc⟩ := hk k (q ≫ pullback.snd ψ.left η[B].left) (Over.homMk _ hw) (by
    apply Over.OverMorphism.ext
    rw [hone]
    change (q ≫ pullback.fst ψ.left η[B].left) ≫ ψ.left =
      (q ≫ pullback.snd ψ.left η[B].left) ≫ η[B].left
    rw [Category.assoc, pullback.condition, Category.assoc])
  have hc' : q ≫ pullback.fst ψ.left η[B].left =
      (q ≫ pullback.snd ψ.left η[B].left) ≫ (i c).left := congrArg (·.left) hc
  let s : (𝟙_ (Over S)).left ⟶ pullback ψ.left η[B].left :=
    pullback.lift (i c).left (𝟙 _) (hker (i c) (hi c))
  have hs : s ≫ pullback.snd ψ.left η[B].left = 𝟙 _ := pullback.lift_snd _ _ _
  have hs' : s ≫ pullback.fst ψ.left η[B].left = (i c).left := pullback.lift_fst _ _ _
  have hqs : (q ≫ pullback.snd ψ.left η[B].left) ≫ s = q := by
    apply pullback.hom_ext
    · rw [Category.assoc, hs', hc']
    · rw [Category.assoc, hs, Category.comp_id]
  have := isOpenImmersion_of_section_of_etale (pullback.snd ψ.left η[B].left) s hs
  obtain ⟨z, hz⟩ : l p ∈ Set.range q := hq.ge rfl
  have ht : l p = s ((q ≫ pullback.snd ψ.left η[B].left) z) := by
    rw [← Scheme.Hom.comp_apply, hqs, hz]
  refine ⟨c, Over.mk (pullback.fst l s ≫ Z.hom), Over.homMk (pullback.fst l s) rfl,
    inferInstanceAs (IsOpenImmersion (pullback.fst l s)), ?_, ?_⟩
  · obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := l) (g := s) p _ ht
    exact ⟨w, hw⟩
  · apply Over.OverMorphism.ext
    change pullback.fst l s ≫ d.left = (pullback.fst l s ≫ Z.hom) ≫ (i c).left
    have h1 : d.left = l ≫ pullback.fst ψ.left η[B].left := (pullback.lift_fst _ _ _).symm
    have h2 : Z.hom = l ≫ pullback.snd ψ.left η[B].left := (pullback.lift_snd _ _ _).symm
    have h3 : pullback.fst l s ≫ Z.hom = pullback.snd l s := by
      rw [h2, pullback.condition_assoc]
      exact (congrArg (pullback.snd l s ≫ ·) hs).trans (Category.comp_id _)
    rw [h3, h1, pullback.condition_assoc, hs']
end GlobalTheory.LinDescent
