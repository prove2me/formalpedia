-- Prove2me | solution 1 for GlobalTheory.JetSer.FBOf.exists_good_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:06.13998+00:00
-- url     : https://prove2.me/submissions/0282b98e-2bc6-4971-9736-1578a9b81540

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_val val val_of Good cubV val₂ IsCub isCub_cubV exists_chart psum_hom preHom)
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.FBOf
namespace GlobalTheory.JetSer.FBOf
theorem _root_.solution {X Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (j : L.ι) (z : Z) :
    ∃ J, Good L z J ∧ ∀ ψ : Z ⟶ X, ψ z ∈ L.U j → J ψ = j := by
  classical
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  refine ⟨fun ψ => if ψ z ∈ L.U j then j else I ψ, fun ψ => ?_, fun ψ h => if_pos h⟩
  by_cases h : ψ z ∈ L.U j
  · simpa only [if_pos h] using h
  · simpa only [if_neg h] using hI ψ
end GlobalTheory.JetSer.FBOf
