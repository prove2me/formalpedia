-- Prove2me | solution 1 for GlobalTheory.JetMap.mapSt_and_dLinSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:57:15.887044+00:00
-- url     : https://prove2.me/submissions/22c5edbf-8673-464d-9979-5cade1b90180

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ToJetOneEqSum
import Theorems.Thm_GlobalTheory_JetMap_mapSt
import Theorems.Thm_GlobalTheory_JetMap_dLinSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetMap
namespace GlobalTheory.JetMap
theorem _root_.solution : JetAlgSt → RepSt → MapSt ∧ DLinSt :=
  fun hJ hR => ⟨mapSt hJ hR, dLinSt hR⟩
end GlobalTheory.JetMap
