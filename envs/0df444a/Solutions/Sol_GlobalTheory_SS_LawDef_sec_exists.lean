-- Prove2me | solution 1 for GlobalTheory.SS.LawDef.sec_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:26:03.873998+00:00
-- url     : https://prove2.me/submissions/ffc51bfd-6371-44cc-bd7e-0d57f4f48528

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslate
import Theorems.Thm_GlobalTheory_SS_LawDef_ext_test
import Theorems.Thm_GlobalTheory_range_subset_opens_of_isLocalRing


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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LawDef
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
variable [IsLocalRing R]
namespace GlobalTheory.SS.LawDef
theorem _root_.solution {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens} {g : U.toScheme ⟶ N.Y.left}
    (h : Extends M N f U g) {p : 𝟙_ (Over (Sp K)) ⟶ A} {s : 𝟙_ (Over (Sp R)) ⟶ M.Y} (hs : Sec M p s)
    (y : U.toScheme) (hy : U.ι y = sp0 s) : ∃ t, Sec N (p ≫ f) t ∧ g y = sp0 t := by
  have hr : Set.range s.left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    refine range_subset_opens_of_isLocalRing (B := CommRingCat.of R) s.left ?_
    show sp0 s ∈ U
    rw [← hy]; exact y.2
  let s' := IsOpenImmersion.lift U.ι s.left hr
  have e : s' ≫ U.ι = s.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk (s' ≫ g) (by rw [Category.assoc, h.1, reassoc_of% e, Over.w s]), ?_, ?_⟩
  · have := ext_test h p.left (spMap (algebraMap R K) ≫ s') (by rw [Category.assoc, e]; exact hs.symm)
    show (p ≫ f).left ≫ N.j = spMap (algebraMap R K) ≫ s' ≫ g
    rw [← Category.assoc (spMap _), this, Over.comp_left, Category.assoc]
  · have : y = s' (IsLocalRing.closedPoint R) := by
      apply U.ι.isOpenEmbedding.injective
      rw [hy, ← Scheme.Hom.comp_apply, e]; rfl
    rw [this, ← Scheme.Hom.comp_apply]; rfl
end GlobalTheory.SS.LawDef
