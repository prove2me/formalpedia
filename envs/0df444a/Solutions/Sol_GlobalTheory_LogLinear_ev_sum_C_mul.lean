-- Prove2me | solution 1 for GlobalTheory.LogLinear.ev_sum_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:13:24.367502+00:00
-- url     : https://prove2.me/submissions/8e4a37ca-d0d7-4789-bc59-ec118b632981

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqZeroOfAdditiveOfPderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalGroupLogEndomorphismLinear
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_hasSubst


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
open GlobalTheory GlobalTheory.LogLinear
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.LogLinear
theorem _root_.solution {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (c : Fin d → k)
    (f : Fin d → PS k m d) : ev V (∑ j, C (c j) * f j) = ∑ j, C (c j) * ev V (f j) := by
  unfold ev
  rw [← coe_substAlgHom (gt_hasSubst V hV), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, coe_substAlgHom, subst_C]
end GlobalTheory.LogLinear
