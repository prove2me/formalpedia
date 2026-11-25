-- Prove2me | solution 1 for GlobalTheory.OrthFrameMahler.continuousOn_rmul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:46:01.050796+00:00
-- url     : https://prove2.me/submissions/f819478a-208d-4ea1-9c01-631abd2f10cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsContinuousGramSchmidt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MahlerCompactness
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_UpperTriangularPreservesDiagonalIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBoundOrthonormalFrameMahler
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.OrthFrameMahler
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.OrthFrameMahler
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} {r : ℕ} {β : Frame Ψ r → Frame Ψ r}
    {K : Set (Frame Ψ r)} (hβ : ContinuousOn β K) : ContinuousOn (fun y => rmul y (β y)) K := by
  refine continuousOn_pi.2 fun τ => continuousOn_pi.2 fun a => continuousOn_pi.2 fun c => ?_
  show ContinuousOn (fun y : Frame Ψ r => ∑ k, y τ a k * β y τ k c) K
  refine continuousOn_finset_sum _ fun k _ => ContinuousOn.mul (by fun_prop) ?_
  exact continuousOn_pi.1 (continuousOn_pi.1 (continuousOn_pi.1 hβ τ) k) c
end GlobalTheory.OrthFrameMahler
