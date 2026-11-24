-- Prove2me | solution 1 for GlobalTheory.SS.StrictLaw.good_isoAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:41:11.956842+00:00
-- url     : https://prove2.me/submissions/5d713569-eae7-491d-9f50-9b562e505f62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeronStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOnPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStrictModelOfBirational
import Theorems.Thm_GlobalTheory_SS_StrictLaw_prod_j_fst
import Theorems.Thm_GlobalTheory_SS_StrictLaw_prod_j_snd
import Theorems.Thm_GlobalTheory_SS_StrictLaw_isoAt_of_open
import Theorems.Thm_GlobalTheory_SS_StrictLaw_isPullback_prod

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
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StrictLaw
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.StrictLaw
theorem _root_.solution {M N : Model R A} (i : N.Y ⟶ M.Y) [IsOpenImmersion i.left]
    (hj : N.j ≫ i.left = M.j) {f : A ⊗ A ⟶ A ⊗ A} {z : (M.prod M).Y.left}
    (h : Good M f (Set.range i.left) z) :
    ∃ w : (N.prod N).Y.left, i.left ((pr₁ N N).left w) = (pr₁ M M).left z ∧
      i.left ((pr₂ N N).left w) = (pr₂ M M).left z ∧
      IsoAt (N.prod N) (N.prod N) f w := by
  obtain ⟨U, g, u, he, hg, hu, h1, h2, h3, h4⟩ := h
  let ii : (N.prod N).Y ⟶ (M.prod M).Y := i ⊗ₘ i
  have e1 : ii.left ≫ (pr₁ M M).left = (pr₁ N N).left ≫ i.left := by
    exact congrArg (fun t => t.left) (tensorHom_fst i i)
  have e2 : ii.left ≫ (pr₂ M M).left = (pr₂ N N).left ≫ i.left := by
    exact congrArg (fun t => t.left) (tensorHom_snd i i)
  have e : ii.left = pullback.map N.Y.hom N.Y.hom M.Y.hom M.Y.hom i.left i.left (𝟙 _)
      (by simp) (by simp) := by
    apply pullback.hom_ext
    · exact e1.trans (pullback.lift_fst _ _ _).symm
    · exact e2.trans (pullback.lift_snd _ _ _).symm
  have ho : IsOpenImmersion ii.left := by
    rw [e]
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) ‹_› ‹_› (Over.w i).symm (Over.w i).symm
  have hr : ∀ t, (pr₁ M M).left t ∈ Set.range i.left → (pr₂ M M).left t ∈ Set.range i.left →
      t ∈ Set.range ii.left := by
    intro t ht ht'
    rw [e]
    exact (Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _).ge ⟨ht, ht'⟩
  have hj' : (N.prod N).j ≫ ii.left = (M.prod M).j := by
    apply (isPullback_prod M M).hom_ext
    · rw [prod_j_fst, ← hj, ← Category.assoc, ← prod_j_fst N N, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) e1
    · rw [prod_j_snd, ← hj, ← Category.assoc, ← prod_j_snd N N, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) e2
  obtain ⟨w, hw⟩ := hr z h1 h2
  refine ⟨w, ?_, ?_, @isoAt_of_open R _ K _ _ _ _ (M.prod M) (N.prod N) (M.prod M) (N.prod N) f
    ii.left ii.left ho ho (Over.w _) (Over.w _) hj' hj' U g hg he w u
    (hu.trans hw.symm) (hr _ h3 h4)⟩
  · rw [← hw, ← Scheme.Hom.comp_apply, ← e1, Scheme.Hom.comp_apply]
  · rw [← hw, ← Scheme.Hom.comp_apply, ← e2, Scheme.Hom.comp_apply]
end GlobalTheory.SS.StrictLaw
