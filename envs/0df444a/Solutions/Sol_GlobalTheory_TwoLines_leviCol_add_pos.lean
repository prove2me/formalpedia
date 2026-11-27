-- Prove2me | solution 1 for GlobalTheory.TwoLines.leviCol_add_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:34:47.918044+00:00
-- url     : https://prove2.me/submissions/c91f5c00-ee92-486a-9a7c-df7ea3f28444

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumInvariantContinuousPosOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumBoundedBelow
import Theorems.Thm_GlobalTheory_TwoLines_leviCol_eq
import Theorems.Thm_GlobalTheory_TwoLines_idx_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix
open GlobalTheory GlobalTheory.TwoLines
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.TwoLines
theorem _root_.solution {X : Data E 2} {τ₁ τ₂ : X.Ψ}
    (hall : ∀ τ, τ = τ₁ ∨ τ = τ₂) {x0 : Frame X.Ψ 2} (hx : x0 ∈ X.dom)
    (z : V (nd X)) {ξ : Fin (nd X) → ℂ} (hξ : ξ ≠ 0) :
    0 < leviCol X x0 τ₁ z ξ + leviCol X x0 τ₂ z ξ := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hξ
  obtain ⟨τ, rfl⟩ := idx_surjective X k
  have h1 := leviCol_eq X (hx τ₁).1 z ξ
  have h2 := leviCol_eq X (hx τ₂).1 z ξ
  rcases hall τ with rfl | rfl
  · linarith [h1.2 hk, h2.1]
  · linarith [h2.2 hk, h1.1]
end GlobalTheory.TwoLines
