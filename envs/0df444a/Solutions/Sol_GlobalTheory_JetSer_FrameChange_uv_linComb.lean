-- Prove2me | solution 1 for GlobalTheory.JetSer.FrameChange.uv_linComb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:57:09.752769+00:00
-- url     : https://prove2.me/submissions/2aab99f9-07c3-4f45-b144-20d482b52a01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_uv_res
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_uv_pull

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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε)
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.FrameChange
variable {A : Type} [CommRing A] {X Y : Scheme.{0}}
namespace GlobalTheory.JetSer.FrameChange
theorem _root_.solution (L : LB X) (j j' : L.ι) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (p : Spec (CommRingCat.of A) ⟶ Y)
    (h : ⊤ ≤ p ⁻¹ᵁ ((LB.LinComb L φ ε).U (fun _ => j) ⊓ (LB.LinComb L φ ε).U (fun _ => j'))) :
    uv p _ ((LB.LinComb L φ ε).g (fun _ => j) (fun _ => j')) = ∏ k, hv L j j' (p ≫ φ k) ^ ε k := by
  refine (map_prod (uv p _) _ _).trans (Finset.prod_congr rfl fun k _ => ?_)
  refine (map_zpow (uv p _) _ _).trans ?_
  congr 1
  refine (uv_res p _ h _).trans ?_
  refine uv_pull p (φ k) (L.U j ⊓ L.U j') (fun z hz => ?_) (L.g j j')
  exact ⟨LB.wchart_le L φ (fun _ => j) k (h hz).1, LB.wchart_le L φ (fun _ => j') k (h hz).2⟩
end GlobalTheory.JetSer.FrameChange
