-- Prove2me | solution 1 for GlobalTheory.CanonGaugeAssembly.cob_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:08:21.126197+00:00
-- url     : https://prove2.me/submissions/fd4a0340-823d-4207-b3eb-acbfeb48d684

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeOfSteps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_add


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.CanonGaugeAssembly
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.CanonGaugeAssembly
theorem _root_.solution {n : ℕ} (U V : Fin 2 → Pt k n d) (hU : ∀ j, GP (U j)) (hV : ∀ j, GP (V j)) :
    Cob (fun h : PS k 2 d => ev U h - ev V h) where
  add f g := by
    rw [gt_ev_add U hU, gt_ev_add V hV]; ring
  const f hf := by
    rw [map_sub, gt_const_ev U hU f hf, gt_const_ev V hV f hf]; simp
end GlobalTheory.CanonGaugeAssembly
