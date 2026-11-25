-- Prove2me | solution 1 for GlobalTheory.Up.Wdiv_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:57:30.239883+00:00
-- url     : https://prove2.me/submissions/4463db13-d8dc-4f7f-af4b-9dfebfd08d49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory GlobalTheory.Up
variable {r : ℕ} {X : Data E r} (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ) {x : Frame X.Ψ r}
namespace GlobalTheory.Up
theorem _root_.solution (hx : x ∈ X.dom) (hs : ∃ k, Fl.s k x ≠ 0) :
    Wdiv X Xa Fl n x = ENNReal.ofReal (Real.exp (-Psdiv X Xa Fl n x)) := by
  have hw := sum_normSq_w_pos Xa hx
  have hs' : 0 < ∑ k, ‖Fl.s k x‖ ^ 2 := sum_normSq_pos hs
  rw [Wdiv_of_mem Xa Fl n hx, ENNReal.ofReal_rpow_of_pos hw, ENNReal.ofReal_rpow_of_pos hs',
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hw.le _)),
    Real.rpow_def_of_pos hw, Real.rpow_def_of_pos hs', ← Real.exp_add, ← Real.exp_add]
  congr 2
  unfold Psdiv
  ring
end GlobalTheory.Up
