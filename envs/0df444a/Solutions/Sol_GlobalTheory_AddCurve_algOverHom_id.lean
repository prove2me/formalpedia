-- Prove2me | solution 1 for GlobalTheory.AddCurve.algOverHom_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:40:38.474451+00:00
-- url     : https://prove2.me/submissions/ec37a31f-c2cf-4ebb-abb9-2ee418438ffa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_PsJetEqToJetOfNonempty
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TopLeAlgOverHom

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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AddCurve
variable {k : Type} [CommRing k]
namespace GlobalTheory.AddCurve
theorem _root_.solution (A : Type) [CommRing A] [Algebra k A] : algOverHom (AlgHom.id k A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact Spec.map_id _
end GlobalTheory.AddCurve
