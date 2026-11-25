-- Prove2me | solution 1 for GlobalTheory.Up.DivMetricPf.Wdiv_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:25:00.370744+00:00
-- url     : https://prove2.me/submissions/48280ad7-f1a7-45a5-b0e6-cb9887086114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OfRealRpowNegLe
import Theorems.Thm_GlobalTheory_Up_DivMetricPf_exists_sum_le
import Theorems.Thm_GlobalTheory_Up_DivMetricPf_ofReal_rpow_neg_le
import Theorems.Thm_GlobalTheory_Up_Wdiv_eq_pnorm


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
open GlobalTheory GlobalTheory.Up GlobalTheory.Up.DivMetricPf
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ)
namespace GlobalTheory.Up.DivMetricPf
theorem _root_.solution (hn : 1 ≤ n) : WLower X (Xa.Fp + n • Xa.L) (Wdiv X Xa Fl n) := by
  obtain ⟨A, hA, hAw⟩ := exists_sum_le fun k => (Xa.w_van k).1.1
  obtain ⟨B, hB, hBs⟩ := exists_sum_le fun k => (Fl.s_van k).1.1
  have hn' : 0 ≤ (n : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hA' := Real.rpow_pos_of_pos hA (-(1 / 2 : ℝ))
  have hB' := Real.rpow_pos_of_pos hB (-((n : ℝ) - 1 / 2))
  refine ⟨A ^ (-(1 / 2 : ℝ)) * B ^ (-((n : ℝ) - 1 / 2)), mul_pos hA' hB', fun x hx => ?_⟩
  rw [Wdiv_eq_pnorm Xa Fl n hx, mul_comm, ← mul_assoc,
    ENNReal.ofReal_mul (mul_pos (Real.exp_pos _) hA').le, ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact mul_le_mul' (mul_le_mul' le_rfl (ofReal_rpow_neg_le hA (hAw x hx) (by norm_num)))
    (ofReal_rpow_neg_le hB (hBs x hx) hn')
end GlobalTheory.Up.DivMetricPf
