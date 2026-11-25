-- Prove2me | solution 1 for GlobalTheory.ChartTransN.dofN_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:25:01.2618+00:00
-- url     : https://prove2.me/submissions/4e21f015-669d-40b6-b810-235cc35d36bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantPolyOperatorCopiesTransportedLaw
import Theorems.Thm_GlobalTheory_NabCol_dofN_inCol
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_X


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
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.ChartTrans GlobalTheory.NabCol
open GlobalTheory GlobalTheory.ChartTransN
variable {k : Type} [CommRing k] {d n : ℕ}
namespace GlobalTheory.ChartTransN
theorem _root_.solution (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (g : PS k n d) :
    DofN F b u g = ∑ l, inCol b (Dof F u (X ((0 : Fin 1), l))) * pderiv k (b, l) g := by
  have hX : ∀ l, inCol b (X ((0 : Fin 1), l) : PS k 1 d) = X (b, l) := fun l => gt_ev_X _ (gp b) 0 l
  simp only [← dofN_inCol, hX]
  conv_lhs => unfold DofN
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  unfold DofN
  symm
  rw [Finset.sum_eq_single l]
  · rw [pderiv_X_self, mul_one]
  · intro j _ hj
    rw [pderiv_X_of_ne (fun h => hj (congrArg Prod.snd h).symm), mul_zero]
  · simp
end GlobalTheory.ChartTransN
