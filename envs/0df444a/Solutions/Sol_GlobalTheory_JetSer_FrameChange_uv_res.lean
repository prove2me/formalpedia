-- Prove2me | solution 1 for GlobalTheory.JetSer.FrameChange.uv_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:39.581016+00:00
-- url     : https://prove2.me/submissions/0f36c91f-3418-4338-bb5a-829cab6c099a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_fnVal_eq
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_evH_res
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_fnVal_unit

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
theorem _root_.solution (p : Spec (CommRingCat.of A) ⟶ X) {U V : X.Opens} (hUV : U ≤ V) (h : ⊤ ≤ p ⁻¹ᵁ U)
    (f : Γ(X, V)ˣ) : uv p U (res hUV f) = uv p V f := by
  have h' : ⊤ ≤ p ⁻¹ᵁ V := fun z hz => hUV (h hz)
  apply Units.ext
  rw [← fnVal_unit p U h, ← fnVal_unit p V h', fnVal_eq p U h, fnVal_eq p V h']
  exact evH_res p hUV h h' _
end GlobalTheory.JetSer.FrameChange
