-- Prove2me | solution 1 for GlobalTheory.SharpGradient.rhF_eq_sum_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:03:07.497586+00:00
-- url     : https://prove2.me/submissions/11127a1f-1b48-4d8c-8590-189f8d597423

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_mem_OmF_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_norm_of_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_rhF_eq_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
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
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SharpGradient
theorem _root_.solution {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)}
    (hz : z ∈ OmF X x0) :
    rhF X x0 z = ∑ τ, -Real.log (1 - ExF.Zt X z τ * (ExF.Zt X z τ)ᴴ).det.re := by
  rw [ExF.rhF_eq_sum X x0 ho, Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [ExF.norm_of_pos ((ExF.mem_OmF_iff X x0 ho z).1 hz τ).det_pos]
  rfl
end GlobalTheory.SharpGradient
