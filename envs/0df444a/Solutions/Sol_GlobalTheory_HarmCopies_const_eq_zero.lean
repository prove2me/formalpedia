-- Prove2me | solution 1 for GlobalTheory.HarmCopies.const_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:06:27.700701+00:00
-- url     : https://prove2.me/submissions/95cbb7fc-b741-4a38-9e5a-4dd3dfbb9ed8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonNCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeIndependenceHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_HarmonicValueCopiesGaugeIndependent
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.HarmCopies
open GlobalTheory.PowGerm
namespace GlobalTheory.HarmCopies
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
    [Algebra ℚ k] [Algebra R k] {B : FB R d O} {h : PS k 2 d} (hh : B.IsCanonGauge k h) :
    MvPowerSeries.constantCoeff h = 0 := by
  rw [← TB.WickVanishing.gt_const_ev_eq _ (TB.WickVanishing.pair_points_zero_constant TB.WickVanishing.gp_zero₂ (TB.WickVanishing.gp_pt (n := 1) 0)) h, hh.ax0, map_zero]
end GlobalTheory.HarmCopies
