-- Prove2me | solution 1 for GlobalTheory.UnfoldComplex.continuous_lact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:37.105737+00:00
-- url     : https://prove2.me/submissions/63dc7b3c-a93e-43dc-8ab7-cdf778db94cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IntegralEqIntegralTsumOfLintegral

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
open GlobalTheory GlobalTheory.UnfoldComplex
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.UnfoldComplex
theorem _root_.solution {r : ℕ} {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) :
    Continuous (fun y : Frame Ψ r => lact δ y) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun y : Frame Ψ r =>
    ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ)
  have hM : Continuous fun y : Frame Ψ r => mat y τ := continuous_apply τ
  exact continuous_const.matrix_mul hM
end GlobalTheory.UnfoldComplex
