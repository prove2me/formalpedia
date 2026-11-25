-- Prove2me | solution 1 for GlobalTheory.JetSer.IntTrans.expS_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:41.396016+00:00
-- url     : https://prove2.me/submissions/bda79aec-90ac-4c25-a05b-f267a5f0960c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RelatedMap
import Theorems.Thm_GlobalTheory_JetSer_IntTrans_expS_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.IntTrans
variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}
namespace GlobalTheory.JetSer.IntTrans
theorem _root_.solution {n : ℕ} {a : PS k n d} (ha : constantCoeff a = 0) (m : ℕ) :
    FB.expS k ((m : k) • a) = FB.expS k a ^ m := by
  rw [Nat.cast_smul_eq_nsmul]
  induction m with
  | zero => rw [zero_nsmul, expS_zero, pow_zero]
  | succ m ih => rw [succ_nsmul, gt_expS_add _ _ (by rw [map_nsmul, ha, nsmul_zero]) ha, ih, pow_succ]
end GlobalTheory.JetSer.IntTrans
