-- Prove2me | solution 1 for GlobalTheory.SharpGradient.rhF_sharp_gradient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:09:40.882909+00:00
-- url     : https://prove2.me/submissions/446907cc-8a9c-45f8-a0b2-459b48f6988d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_GlobalTheory_SharpGradient_sharpAt_rhF
import Theorems.Thm_GlobalTheory_SharpGradient_rhF_le_near_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_rhF_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


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
theorem _root_.solution : ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 →
    (∀ z ∈ OmF X x0, 0 ≤ rhF X x0 z ∧ ∀ ξ : Fin (nd X) → ℂ,
      Complex.normSq (∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) z * ξ j) ≤ rhF X x0 z * leviRh X x0 z ξ) ∧
    ∃ ρ C : ℝ, 0 < ρ ∧ ∀ z : V (nd X), ‖z‖ < ρ → z ∈ OmF X x0 ∧ rhF X x0 z ≤ C * ∑ e : Ent X,
      if (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ) then ‖z (Fintype.equivFin (Ent X) e)‖ ^ 2 else 0 :=
  fun _ X x0 ho =>
    ⟨fun _ hz => ⟨ExF.rhF_nonneg X x0 ho hz, fun ξ => (sharpAt_rhF X x0 ho hz ξ).2.2.2⟩,
      rhF_le_near_zero X x0 ho⟩
end GlobalTheory.SharpGradient
