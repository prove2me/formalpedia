-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.basicOpen_ratioOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:59:13.75957+00:00
-- url     : https://prove2.me/submissions/b3321ef9-d8ce-41fd-81b1-dcbee76f0bbd

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_SpecMapAwayFnEquivAwayChart
import Theorems.Thm_GlobalTheory_ProjFrac_basicOpen_frac


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
variable {W} {U V : (scheme W).Opens} {i j k : Fin 3}
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution (hi : U ≤ coordOpen W i) :
    (scheme W).basicOpen (ratioOn W U i hi j) = U ⊓ coordOpen W j :=
  basicOpen_frac
end GlobalTheory.WeierstrassCurve
