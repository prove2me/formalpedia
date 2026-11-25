-- Prove2me | solution 1 for GlobalTheory.SmoothLocusAdd.exists_hom_of_locally_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:17:38.805618+00:00
-- url     : https://prove2.me/submissions/0ffd0cc5-d5a0-43de-a5a4-9d02da0dd062

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfLocallyRel
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_ProjPoint_hom_ext
import Theorems.Thm_GlobalTheory_hom_eq_iff_forall_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  AlgebraicGeometry
noncomputable section
open GlobalTheory GlobalTheory.SmoothLocusAdd
open GlobalTheory.WeierstrassCurve
namespace GlobalTheory.SmoothLocusAdd
theorem _root_.solution {T Y S : Scheme.{0}} [IsReduced T] (t : T ⟶ S) (s : Y ⟶ S)
    [IsSeparated s]
    (Rel : ∀ (k : Type) [Field k], (Spec (.of k) ⟶ T) → (Spec (.of k) ⟶ Y) → Prop)
    (huniq : ∀ (k : Type) [Field k] x y y', Rel k x y → Rel k x y' → y = y')
    (H : ∀ z : T, ∃ (V : Scheme.{0}) (j : V ⟶ T) (_ : IsOpenImmersion j) (f : V ⟶ Y),
      z ∈ Set.range j ∧ f ≫ s = j ≫ t ∧
        ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ V), Rel k (x ≫ j) (x ≫ f)) :
    ∃ f : T ⟶ Y, f ≫ s = t ∧ ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), Rel k x (x ≫ f) := by
  choose V j hj f hz hs hf using H
  let 𝒰 : T.OpenCover := Scheme.Cover.mkOfCovers T V j (fun z => ⟨z, hz z⟩) hj
  have hc : ∀ a b, pullback.fst (j a) (j b) ≫ f a = pullback.snd _ _ ≫ f b := by
    intro a b
    have : IsReduced (pullback (j a) (j b)) :=
      isReduced_of_isOpenImmersion (pullback.fst (j a) (j b) ≫ j a)
    refine (hom_eq_iff_forall_field s ?_).mpr fun k _ x => ?_
    · rw [Category.assoc, Category.assoc, hs, hs, pullback.condition_assoc]
    · have h₁ := hf a k (x ≫ pullback.fst (j a) (j b))
      have h₂ := hf b k (x ≫ pullback.snd (j a) (j b))
      rw [Category.assoc, Category.assoc] at h₁ h₂
      rw [← pullback.condition] at h₂
      exact huniq k _ _ _ h₁ h₂
  have hg : ∀ z, j z ≫ 𝒰.glueMorphisms f hc = f z := 𝒰.ι_glueMorphisms f hc
  refine ⟨𝒰.glueMorphisms f hc, 𝒰.hom_ext _ _ fun z => ?_, fun k _ x => ?_⟩
  · exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ s) (hg z))).trans (hs z)
  · let z : T := x (IsLocalRing.closedPoint k)
    have hr : Set.range x ⊆ Set.range (j z) := by
      rintro _ ⟨y, rfl⟩
      obtain rfl : y = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
      exact hz z
    have hy : IsOpenImmersion.lift (j z) x hr ≫ j z = x := IsOpenImmersion.lift_fac ..
    have := hf z k (IsOpenImmersion.lift (j z) x hr)
    rw [← hg z, ← Category.assoc, hy] at this
    exact this
end GlobalTheory.SmoothLocusAdd
