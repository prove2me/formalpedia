-- Prove2me | solution 1 for GlobalTheory.SS.TorOpen.isIso_univPt_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:46:45.376574+00:00
-- url     : https://prove2.me/submissions/e724fdce-b745-4d20-a931-2cd4ecef0220

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsMultiplicativeGroupOpenNonvanishingPolynom
import Theorems.Thm_GlobalTheory_SS_ArcInf_IsChart_hom_ext


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
open GlobalTheory.SS.ArcInf
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.TorOpen
open GlobalTheory.SplitTorus ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
namespace GlobalTheory.SS.TorOpen
theorem _root_.solution (k : Type) [CommRing k] (X : Type) [AddCommGroup X] :
    IsIso (univPt (A := CommRingCat.of k) X (𝟙 (Sp k))).left := by
  have h1 := GlobalTheory.Diag.isPullback_groupRing k X
  have h2 := GlobalTheory.Diag.isPullback_torusFst (Sp k) X
  have e : (univPt (A := CommRingCat.of k) X (𝟙 (Sp k))).left = (h1.isoIsPullback _ _ h2).hom := by
    apply h2.hom_ext
    · refine Eq.trans ?_ (IsPullback.isoIsPullback_hom_fst _ _ h1 h2).symm
      refine (pullback.lift_fst _ _ _).trans ?_
      rw [Spec.map_comp]
      exact toSpecΓ_SpecMap_ΓSpecIso_inv_assoc (torusRing (CommRingCat.of k) X) _
    · refine Eq.trans ?_ (IsPullback.isoIsPullback_hom_snd _ _ h1 h2).symm
      exact (Over.w _).trans (Category.comp_id _)
  rw [e]; infer_instance
end GlobalTheory.SS.TorOpen
