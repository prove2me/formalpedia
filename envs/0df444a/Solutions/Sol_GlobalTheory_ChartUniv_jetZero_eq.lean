-- Prove2me | solution 1 for GlobalTheory.ChartUniv.jetZero_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:10:47.925369+00:00
-- url     : https://prove2.me/submissions/1b1978fd-41b8-443b-a01b-44ce53049d8f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
import Theorems.Thm_GlobalTheory_ChartUniv_jetZero_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetZero_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartUniv
open ReciprocityTheory.ChartRestriction.G.Chart
variable {R : Type} [CommRing R]
namespace GlobalTheory.ChartUniv
theorem _root_.solution (κ : Type) (m : ℕ) : jetZeroR R κ m = (Algebra.ofId R (JetR R κ 0)).comp (jetAug R κ m) :=
  jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR, map_zero, jetZero_zR]
end GlobalTheory.ChartUniv
