-- Prove2me | solution 1 for GlobalTheory.JetSer.FrameChange.gen_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:17:31.792908+00:00
-- url     : https://prove2.me/submissions/780710c9-925e-4b90-bd63-87643a779948

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_uv_res
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_uv_linComb

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
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (p : Spec (CommRingCat.of A) ⟶ Y)
    (h : ⊤ ≤ p ⁻¹ᵁ (LB.LinComb L φ ε).U (fun _ => j)) (h' : ⊤ ≤ p ⁻¹ᵁ (LB.LinComb L φ ε).U (fun _ => j')) :
    uv p _ (t.s (fun _ => j)) = (∏ k, hv L j j' (p ≫ φ k) ^ ε k) * uv p _ (t.s (fun _ => j')) := by
  have h2 : ⊤ ≤ p ⁻¹ᵁ ((LB.LinComb L φ ε).U (fun _ => j) ⊓ (LB.LinComb L φ ε).U (fun _ => j')) :=
    fun z hz => ⟨h hz, h' hz⟩
  have := congrArg (uv p _) (ht (fun _ => j) (fun _ => j'))
  rwa [map_mul, uv_res p _ h2, uv_res p _ h2, uv_linComb L j j' φ ε p h2] at this
end GlobalTheory.JetSer.FrameChange
