-- Prove2me | solution 1 for GlobalTheory.NormFactor.nfacRmul_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:14:48.518416+00:00
-- url     : https://prove2.me/submissions/2bc96121-6ffe-4790-b280-412bd75a38d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NormBcharMulNfacRmul
import Theorems.Thm_GlobalTheory_NormFactor_norm_bchar_mul_nfac_rmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoE_bchar_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.NormFactor
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.NormFactor
namespace _root_.GlobalTheory.NormFactor
theorem _root_.solution : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement
  intro r X la x hx b hb
  have hne : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b‖ ≠ 0 := norm_ne_zero_iff.2 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne X la hb)
  rw [eq_inv_mul_iff_mul_eq₀ hne]
  exact _root_.GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul X la hx hb
end _root_.GlobalTheory.NormFactor
end GlobalTheory.NormFactor
