-- Prove2me | solution 1 for GlobalTheory.ChartTrans.ev_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:10:46.553204+00:00
-- url     : https://prove2.me/submissions/546f2545-88af-4022-ac48-2744a86ef8a8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Theorems.Thm_GlobalTheory_ChartTrans_ev_C
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant


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
open GlobalTheory GlobalTheory.ChartTrans
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.ChartTrans
theorem _root_.solution {n : ℕ} (f : PS k 1 d) : ev ![(0 : Pt k n d)] f = C (constantCoeff f) := by
  have e : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  conv_lhs => rw [e]
  rw [gt_ev_add _ (single_point_zero_constant gp_zero₂), ev_C]
  have h2 : ev ![(0 : Pt k n d)] (f - C (constantCoeff f)) = 0 := by
    change MvPowerSeries.subst (fun p : Fin 1 × Fin d => (![(0 : Pt k n d)] p.1) p.2) _ = 0
    have e : (fun p : Fin 1 × Fin d => (![(0 : Pt k n d)] p.1) p.2) = 0 := by
      funext p; simp
    rw [e]
    exact MvPowerSeries.subst_zero_of_constantCoeff_zero h0
  rw [h2, add_zero]
end GlobalTheory.ChartTrans
