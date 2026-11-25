-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.mapHom_app_ratioOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:01:29.300774+00:00
-- url     : https://prove2.me/submissions/6fca3795-4983-4dec-9a70-f5dc37b4a124

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_SpecMapAwayFnEquivAwayChart
import Theorems.Thm_GlobalTheory_ProjFrac_map_app_frac


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap resG constFn)
open GlobalTheory.ProjFrac GlobalTheory.QCoh.Qcqs GlobalTheory.TangentOrigin
open GlobalTheory
open GlobalTheory.WeierstrassCurve
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
variable {R' : Type} [CommRing R'] {W' : WeierstrassCurve R'} (f : R →+* R') (h : W.map f = W')
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution {U : (scheme W).Opens} {i : Fin 3} (hi : U ≤ coordOpen W i) (j : Fin 3) :
    ((mapHom W f h).app U).hom (ratioOn W U i hi j) = ratioOn W' (mapHom W f h ⁻¹ᵁ U) i
      (((mapHom W f h).preimage_mono hi).trans (mapHom_preimage_coordOpen W f h i).le) j :=
  (map_app_frac (gradedMap W f h) (irrelevant_le_map_gradedMap W f h) U _ _ _ _ hi).trans
    (frac_eq (congrArg₂ (· * ·) (homRingMap_coord W f h j) (homRingMap_coord W f h i).symm))
end GlobalTheory.WeierstrassCurve
