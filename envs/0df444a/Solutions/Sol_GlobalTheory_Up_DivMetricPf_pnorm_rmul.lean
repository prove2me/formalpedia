-- Prove2me | solution 1 for GlobalTheory.Up.DivMetricPf.pnorm_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:44:29.89171+00:00
-- url     : https://prove2.me/submissions/ce49a336-9c75-4402-b3a9-6c4a65f5e144

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OfRealRpowNegLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_pnorm_rmul


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
theorem _root_.solution (hN : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E)) {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : X.IsSec la P) {x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) :
    X.pnorm la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) = X.pnorm la P x :=
  _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx b hb
end _root_.GlobalTheory.Up.DivMetricPf
end GlobalTheory.Up.DivMetricPf
