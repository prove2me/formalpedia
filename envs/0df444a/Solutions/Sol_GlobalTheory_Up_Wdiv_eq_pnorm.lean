-- Prove2me | solution 1 for GlobalTheory.Up.Wdiv_eq_pnorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:50:25.903658+00:00
-- url     : https://prove2.me/submissions/bf411274-aa90-457f-a131-59148141edb3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Theorems.Thm_GlobalTheory_Up_phla_add_nsmul
import Theorems.Thm_GlobalTheory_Up_pnorm_sq_eq_exp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory GlobalTheory.Up
variable {r : ℕ} {X : Data E r} (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ) {x : Frame X.Ψ r}
namespace GlobalTheory.Up
theorem _root_.solution (hx : x ∈ X.dom) :
    Wdiv X Xa Fl n x = ENNReal.ofReal (Real.exp (-phla X (Xa.Fp + n • Xa.L) x)) *
      ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(1 / 2 : ℝ)) *
      ENNReal.ofReal (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
  have ha := Real.exp_pos (-phla X Xa.L x)
  simp only [pnorm_sq_eq_exp hx, ← Finset.mul_sum]
  rw [Wdiv_of_mem Xa Fl n hx, ENNReal.ofReal_mul ha.le, ENNReal.ofReal_mul ha.le,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.ofReal_rpow_of_pos ha, ENNReal.ofReal_rpow_of_pos ha]
  have key : ENNReal.ofReal (Real.exp (-phla X Xa.Fp x)) =
      ENNReal.ofReal (Real.exp (-phla X (Xa.Fp + n • Xa.L) x)) *
        ENNReal.ofReal (Real.exp (-phla X Xa.L x) ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (Real.exp (-phla X Xa.L x) ^ (-((n : ℝ) - 1 / 2))) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ha.le _)),
      ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add, phla_add_nsmul hx]
    congr 2
    ring
  rw [key]
  ring
end GlobalTheory.Up
