-- Prove2me | solution 1 for GlobalTheory.JetSer.FrameChange.uv_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:40:56.180816+00:00
-- url     : https://prove2.me/submissions/eb2e9e41-3a42-4a10-a1cd-f65211543d30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_fnVal_eq
import Theorems.Thm_GlobalTheory_JetSer_FrameChange_evH_pull
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
theorem _root_.solution (p : Spec (CommRingCat.of A) ⟶ Y) (q : Y ⟶ X) (V : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ (q ⁻¹ᵁ V))
    (f : Γ(X, V)ˣ) : uv p _ (pullU q V f) = uv (p ≫ q) V f := by
  have h' : ⊤ ≤ (p ≫ q) ⁻¹ᵁ V := h
  apply Units.ext
  rw [← fnVal_unit p _ h, ← fnVal_unit _ V h', fnVal_eq p _ h, fnVal_eq _ V h']
  exact evH_pull p q V h h' _
end GlobalTheory.JetSer.FrameChange
