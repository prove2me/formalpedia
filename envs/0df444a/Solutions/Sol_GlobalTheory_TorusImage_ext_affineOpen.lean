-- Prove2me | solution 1 for GlobalTheory.TorusImage.ext_affineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:09:01.16362+00:00
-- url     : https://prove2.me/submissions/1d4522d8-a9d6-4134-b329-396111897322

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRatioOfWeightSumsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusImageFactorQuotientGoodOpen
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.TorusImage
namespace GlobalTheory.TorusImage
theorem _root_.solution {Z Y : Scheme.{0}} (g g' : Z ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ g ⁻¹ᵁ U) (h' : ⊤ ≤ g' ⁻¹ᵁ U) (e : g.appLE U ⊤ h = g'.appLE U ⊤ h') : g = g' := by
  have : IsAffine U.toScheme := hU
  have h1 : g.resLE U ⊤ h = g'.resLE U ⊤ h' := by
    apply ext_of_isAffine
    rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.resLE_app_top, e]
  have h2 := congrArg (· ≫ U.ι) h1
  simp only [Scheme.Hom.resLE_comp_ι] at h2
  have : IsIso (⊤ : Z.Opens).ι := inferInstanceAs (IsIso Z.topIso.hom)
  exact (cancel_epi _).1 h2
end GlobalTheory.TorusImage
