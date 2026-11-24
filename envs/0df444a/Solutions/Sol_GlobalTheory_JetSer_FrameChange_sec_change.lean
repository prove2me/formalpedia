-- Prove2me | solution 1 for GlobalTheory.JetSer.FrameChange.sec_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:19:55.436857+00:00
-- url     : https://prove2.me/submissions/0a9894c6-fafe-4dfa-84fa-59faf46d2cbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_fnVal_eq
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_evH_res
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_fnVal_unit
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_uv_linComb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat


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
    (t : LB.Sec (LB.LinComb L φ ε)) (p : Spec (CommRingCat.of A) ⟶ Y)
    (h : ⊤ ≤ p ⁻¹ᵁ (LB.LinComb L φ ε).U (fun _ => j)) (h' : ⊤ ≤ p ⁻¹ᵁ (LB.LinComb L φ ε).U (fun _ => j')) :
    fnVal p _ (t.f (fun _ => j)) = (∏ k, hv L j j' (p ≫ φ k) ^ ε k).val * fnVal p _ (t.f (fun _ => j')) := by
  have h2 : ⊤ ≤ p ⁻¹ᵁ ((LB.LinComb L φ ε).U (fun _ => j) ⊓ (LB.LinComb L φ ε).U (fun _ => j')) :=
    fun z hz => ⟨h hz, h' hz⟩
  have := congrArg (evH p _ h2) (t.compat (fun _ => j) (fun _ => j'))
  rw [map_mul, evH_res p _ h2 h, evH_res p _ h2 h', ← fnVal_eq p _ h2, fnVal_unit p _ h2,
    uv_linComb L j j' φ ε p h2] at this
  rw [fnVal_eq p _ h, fnVal_eq p _ h', this]
end GlobalTheory.JetSer.FrameChange
