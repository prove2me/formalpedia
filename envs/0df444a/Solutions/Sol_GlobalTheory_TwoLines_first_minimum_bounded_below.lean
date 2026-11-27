-- Prove2me | solution 1 for GlobalTheory.TwoLines.first_minimum_bounded_below
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:34:41.473992+00:00
-- url     : https://prove2.me/submissions/52bf2d3e-8902-40f3-8286-b9b97f1b44a2

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
import Theorems.Thm_GlobalTheory_TwoLines_isOrth_idF
import Theorems.Thm_GlobalTheory_ClosedDiscontinuity_firstMinimum_invariant_continuous_pos_on_frames
import Theorems.Thm_GlobalTheory_TwoLines_isCompact_orth
import Theorems.Thm_P2M_GlobalTheory_TwoLines_lact_one__d9ee5c0b5a07
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_orth_mem_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ortho_holds
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono


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
theorem _root_.solution {X : Data E 2} (hG : X.Gm = 1) (hp : X.p0 = 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ X.dom, ε ≤ X.la1 x := by
  obtain ⟨h1, h2, h3⟩ := ClosedDiscontinuity.firstMinimum_invariant_continuous_pos_on_frames 2 X two_pos
  have hsub : {x : Frame X.Ψ 2 | IsOrth X x} ⊆ X.dom := fun x hx => IW.orth_mem_dom X x hx
  obtain ⟨y, hy, hmin⟩ := (isCompact_orth hG hp).exists_isMinOn ⟨_, isOrth_idF hG hp⟩ (h2.mono hsub)
  refine ⟨_, h3 y (hsub hy), fun x hx => ?_⟩
  obtain ⟨x1, ho, b, hb, rfl⟩ := ortho_holds 2 X x hx
  have := h1 1 X.Γ.one_mem x1 (hsub ho) b hb
  rw [lact_one'] at this
  rw [this]
  exact hmin ho
end GlobalTheory.TwoLines
