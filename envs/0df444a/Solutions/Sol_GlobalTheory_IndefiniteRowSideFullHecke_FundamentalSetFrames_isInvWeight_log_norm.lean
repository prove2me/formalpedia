-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames.isInvWeight_log_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:52:44.980802+00:00
-- url     : https://prove2.me/submissions/a7c5e17a-3f6e-4c74-96fe-e12d18aed388

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_QuotientIsHausdorff
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_FundamentalSetFrames
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FundamentalSetFrames_continuous_dmin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory
open scoped ENNReal NNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames
theorem _root_.solution (X : Data E r) (L : Wt X.Ψ r) (s : Frame X.Ψ r → ℂ)
    (hs : X.IsBddSec L s)
    (hinv : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      X.pnorm L s (lact γ (rmul x b)) = X.pnorm L s x) :
    IsInvWeight X fun x => ENNReal.log (ENNReal.ofReal (X.pnorm L s x ^ 2)) := by
  obtain ⟨hsec, C, hC⟩ := hs
  refine ⟨?_, fun γ hγ x hx b hb => by simp only [hinv γ hγ x hx b hb], (|C| + 1) ^ 2, fun x hx => ?_⟩
  · refine ENNReal.measurable_log.comp (ENNReal.measurable_ofReal.comp (Measurable.pow_const ?_ 2))
    unfold Data.pnorm
    refine Measurable.mul (hsec.1.continuousOn.restrict.measurable.norm) ?_
    refine Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ => ?_
    refine Measurable.pow_const (Measurable.norm (Measurable.div ?_ ?_)) _ <;>
      exact ((continuous_dmin X τ _).comp continuous_subtype_val).measurable
  · have h0 : 0 ≤ X.pnorm L s x := by
      unfold Data.pnorm
      positivity
    have h1 : X.pnorm L s x ^ 2 ≤ (|C| + 1) ^ 2 := by
      have := hC x hx
      have := le_abs_self C
      gcongr
      linarith
    have h2 : 0 < (|C| + 1) ^ 2 := by positivity
    refine (ENNReal.log_monotone (ENNReal.ofReal_le_ofReal h1)).trans ?_
    rw [ENNReal.log_ofReal_of_pos h2]
    exact EReal.coe_le_coe_iff.2 ((Real.log_le_sub_one_of_pos h2).trans (by linarith))
end GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames
