-- Prove2me | solution 1 for GlobalTheory.SS.Translates.exists_section_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:26.5708+00:00
-- url     : https://prove2.me/submissions/f5b0bd88-616b-4fa8-80fa-bf5b8a38a5e9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_StrictModelTranslatesTwistCompatible
import Theorems.Thm_GlobalTheory_reducePoint_residue_surjective


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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Translates
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
namespace GlobalTheory.SS.Translates
theorem _root_.solution [IsDomain R] [IsLocalRing R] (hR : SH R K) (M : Model R A)
    (y : ↥(pullback M.Y.hom (spMap (IsLocalRing.residue R)))) (hy : IsClosed {y}) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ M.Y, s.left (IsLocalRing.closedPoint R) = pullback.fst M.Y.hom (spMap (IsLocalRing.residue R)) y := by
  obtain ⟨-, h2, h3, -⟩ := hR
  have := M.smooth
  let x₀ := pointOfClosedPoint (pullback.snd M.Y.hom (spMap (IsLocalRing.residue R))) y hy
  obtain ⟨⟨s, hs⟩, e⟩ := reducePoint_residue_surjective M.Y.hom R (𝟙 _)
    ⟨x₀ ≫ pullback.fst _ _, by
      rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc, Category.comp_id]⟩
  have e' : spMap (IsLocalRing.residue R) ≫ s = x₀ ≫ pullback.fst _ _ := congrArg Subtype.val e
  refine ⟨Over.homMk s hs, ?_⟩
  have e2 : s (PrimeSpectrum.comap (IsLocalRing.residue R) (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) =
      pullback.fst M.Y.hom (spMap (IsLocalRing.residue R)) (x₀ (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) :=
    congr($e' (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)))
  rw [IsLocalRing.comap_closedPoint] at e2
  exact e2.trans (congrArg _ (pointOfClosedPoint_apply _ y hy _))
end GlobalTheory.SS.Translates
