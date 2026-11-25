-- Prove2me | solution 1 for GlobalTheory.splitTorus_extension_descends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:11:58.460844+00:00
-- url     : https://prove2.me/submissions/401e64ba-fee9-404b-9bcb-b0efef895cb8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusExtensionDescends
import Theorems.Thm_GlobalTheory_ExtDescent_isMonHom_of_grpPullback
import Theorems.Thm_GlobalTheory_ExtDescent_unit_comm
import Theorems.Thm_GlobalTheory_ExtDescent_fpqc_of_isPullback
import Theorems.Thm_GlobalTheory_ExtDescent_isPullback_of_baseChange
import Theorems.Thm_GlobalTheory_SplitTorus_isGrpPullback_bcMap
import Theorems.Thm_GlobalTheory_flat_descendsAlong_fpqc
import Theorems.Thm_GlobalTheory_quasiCompact_descendsAlong_fpqc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open ExtDescent
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [GrpObj B₀] (X : Type) [AddCommGroup X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap β) φG → IsGrpPullback B B₀ (spMap β) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G) (q₀ : G₀ ⟶ B₀) (i₀ : splitTorus (Sp k) X ⟶ G₀), φG ≫ q₀.left = q.left ≫ φ → GlobalTheory.SplitTorus.bcMap (spMap β) X ≫ i₀.left = i.left ≫ φG → IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → IsMonHom q₀ ∧ Flat q₀.left ∧ Surjective q₀.left ∧ QuasiCompact q₀.left ∧ IsMonHom i₀ ∧ IsPullback i₀ (toUnit _) q₀ (η[B₀] : 𝟙_ _ ⟶ B₀) := by
  intro k K _ _ β G B _ _ G₀ B₀ _ _ X _ φG φ hG hB q i q₀ i₀ wq wi hq hfl hsu hqc hi H
  haveI h₁ : Flat (spMap β) := inferInstance
  haveI h₂ : Surjective (spMap β) := inferInstance
  haveI h₃ : QuasiCompact (spMap β) := inferInstance
  have hγ : IsPullback φG q.left q₀.left φ := by
    refine IsPullback.of_bot ?_ wq hB.1
    rw [Over.w, Over.w]
    exact hG.1
  have hφ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) φ :=
    fpqc_of_isPullback hB.1
  haveI := flat_descendsAlong_fpqc
  haveI := quasiCompact_descendsAlong_fpqc.{0}
  have hT := SplitTorus.isGrpPullback_bcMap (spMap β) X
  refine ⟨isMonHom_of_grpPullback hG hB q q₀ wq,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat) hγ.flip hφ hfl,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Surjective) hγ.flip hφ hsu,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @QuasiCompact) hγ.flip hφ hqc,
    isMonHom_of_grpPullback hT hG i i₀ wi, ?_⟩
  have H' : IsPullback i.left (splitTorus (Sp K) X).hom q.left (η[B]).left :=
    H.map (Over.forget _)
  have H₀ := isPullback_of_baseChange H' hT.1 hγ wi (unit_comm hB)
  exact IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext H₀.w) H₀
end GlobalTheory
