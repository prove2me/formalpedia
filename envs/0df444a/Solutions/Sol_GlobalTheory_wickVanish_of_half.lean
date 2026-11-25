-- Prove2me | solution 1 for GlobalTheory.wickVanish_of_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:57:18.391545+00:00
-- url     : https://prove2.me/submissions/b9b2b1a4-588a-4b8d-be4e-3db5c684db23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_WickVanishOfHalf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_add_f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_zero_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_exp_cut


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : GE.HalfSt → G2.WickOperatorVanishing := by
  intro hH k _ _ d F ι _ u c P q hc hq0 hq1 hq2 hP m G
  obtain ⟨Y, hY⟩ := GE.exp_cut m q hq0 0
  have hY' : FB.expS k (m • q) = 1 + q * Y := by
    rw [hY]
    simp
  rw [hY', mul_add, mul_one, GE.dpolyOf_add_f, map_add,
    show G * (q * Y) = (G * Y) * q by ring, hH k d F ι u c q hc hq0 hq1 hq2 P (G * Y), hP,
    GE.dpolyOf_zero_P, map_zero, mul_zero, add_zero]
end GlobalTheory
