-- Prove2me | solution 1 for GlobalTheory.JetsPure.monomial_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:38:18.646916+00:00
-- url     : https://prove2.me/submissions/2aa6c1f0-b459-4577-96ce-8a6bccd61dc1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_PointwiseNormConstantSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_SumMultiLtSucc

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
open GlobalTheory GlobalTheory.JetsPure
open Filter Asymptotics
open MeasureTheory Topology Filter Asymptotics
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.JetsPure
namespace _root_.GlobalTheory.JetsPure
theorem _root_.solution {n D : ℕ} (σ : Fin D → _root_.ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (hσ : ∀ k, DifferentiableAt ℂ (σ k) 0) (h0 : ∀ k, σ k 0 = 0) (α : Fin D → ℕ) :
    (fun z => ∏ q, σ q z ^ α q) =O[𝓝 0] fun z => ‖z‖ ^ (∑ q, α q) := by
  have h1 : ∀ q, σ q =O[𝓝 0] fun z : _root_.ReciprocityTheory.L2DbarEstimates.V n => ‖z‖ := by
    intro q
    have h := (hσ q).hasFDerivAt.isBigO_sub.norm_right
    simpa only [h0 q, sub_zero] using h
  have h2 : (fun z => ∏ q, σ q z ^ α q) =O[𝓝 0] fun z : _root_.ReciprocityTheory.L2DbarEstimates.V n => ∏ q, ‖z‖ ^ α q :=
    IsBigO.finsetProd fun q _ => (h1 q).pow (α q)
  simpa only [Finset.prod_pow_eq_pow_sum] using h2
end _root_.GlobalTheory.JetsPure
end GlobalTheory.JetsPure
