-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.evalPt_constOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:04.186244+00:00
-- url     : https://prove2.me/submissions/1f7e725c-11a6-4391-86c7-c56cbbbf0201

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_SpecMapAwayFnEquivAwayChart
import Theorems.Thm_GlobalTheory_WeierstrassCurve_constOn_apply

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
variable {W} {A : Type} [CommRing A]
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution {x : Sp A ⟶ scheme W} {ρ : R →+* A} (hx : x ≫ toSpec W = spMap ρ)
    {U : (scheme W).Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (r : R) : evalPt x U h (constOn W U r) = ρ r := by
  rw [constOn_apply, evalPt_constFn]
  exact (congrArg (fun y : Sp A ⟶ Sp R => evalPt y ⊤ le_rfl
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) hx).trans (evalPt_spMap _ r)
end GlobalTheory.WeierstrassCurve
