-- Prove2me | solution 1 for GlobalTheory.Up.DivMetricPf.exists_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:02:16.509562+00:00
-- url     : https://prove2.me/submissions/45b6a4c0-a3e4-46e6-beac-07deda3b3bfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OfRealRpowNegLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoE_nfac_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowCoefficientBounds_nfac_pos


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
open NumberField MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r}
namespace GlobalTheory.Up.DivMetricPf
namespace _root_.GlobalTheory.Up.DivMetricPf
theorem _root_.solution {N : ℕ} {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : Fin N → _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : ∀ k, X.IsBddSec la (P k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ X.dom, ∑ k, X.pnorm la (P k) x ^ 2 ≤ C := by
  choose C hC using fun k => (hP k).2
  refine ⟨1 + ∑ k, C k ^ 2, by positivity, fun x hx => ?_⟩
  have hle : ∀ k, X.pnorm la (P k) x ^ 2 ≤ C k ^ 2 := by
    intro k
    have h0 : 0 ≤ X.pnorm la (P k) x := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
      exact mul_nonneg (norm_nonneg _) (_root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.nfac_pos X hx la).le
    exact pow_le_pow_left₀ h0 (hC k x hx) 2
  calc ∑ k, X.pnorm la (P k) x ^ 2 ≤ ∑ k, C k ^ 2 := Finset.sum_le_sum fun k _ => hle k
    _ ≤ 1 + ∑ k, C k ^ 2 := by linarith
end _root_.GlobalTheory.Up.DivMetricPf
end GlobalTheory.Up.DivMetricPf
