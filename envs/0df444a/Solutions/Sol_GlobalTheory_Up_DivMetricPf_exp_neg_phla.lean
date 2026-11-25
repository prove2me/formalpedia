-- Prove2me | solution 1 for GlobalTheory.Up.DivMetricPf.exp_neg_phla
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:14:39.646614+00:00
-- url     : https://prove2.me/submissions/3ed6d1c3-ce96-42e7-9fc3-2196986c0f29

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
theorem _root_.solution {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) :
    Real.exp (-_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X la x) = X.nfac la x ^ 2 := by
  have hpos := _root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.nfac_pos X hx la
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla
  rw [show -(-2 * Real.log (X.nfac la x)) = Real.log (X.nfac la x) + Real.log (X.nfac la x) by
    ring, Real.exp_add, Real.exp_log hpos]
  ring
end _root_.GlobalTheory.Up.DivMetricPf
end GlobalTheory.Up.DivMetricPf
