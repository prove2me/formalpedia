-- Prove2me | solution 1 for GlobalTheory.FormalMul.mulF_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:27:09.443302+00:00
-- url     : https://prove2.me/submissions/447fb515-9766-49a4-aa96-3c7e12f25f13

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MulFConstAndMap
import Theorems.Thm_GlobalTheory_FormalMul_constantCoeff_mulF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_hasSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.FormalMul
namespace GlobalTheory.FormalMul
theorem _root_.solution {T O : Type} [CommRing T] [CommRing O] (io : T →+* O) {d : ℕ} (F : Fin d → PS T 2 d)
    (hF : ∀ i, constantCoeff (F i) = 0) (N : ℕ) :
    ∀ j, mulF (fun i => MvPowerSeries.map io (F i)) N j = MvPowerSeries.map io (mulF F N j) := by
  induction N with
  | zero => intro j; simp [mulF]
  | succ n ih =>
    intro j
    have hs := gt_hasSubst ![mulF F n, pt T (n := 1) d 0]
      (pair_points_zero_constant (constantCoeff_mulF F hF n) (gp_pt 0))
    simp only [mulF, addOf, ev]
    rw [MvPowerSeries.map_subst hs]
    congr 1
    funext p
    rcases p with ⟨a, b⟩
    fin_cases a
    · exact ih b
    · simp [pt]
end GlobalTheory.FormalMul
