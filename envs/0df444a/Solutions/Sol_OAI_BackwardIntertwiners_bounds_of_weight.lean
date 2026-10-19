-- Prove2me | solution 1 for OAI.BackwardIntertwiners.bounds_of_weight
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:54:34.752484+00:00
-- url     : https://prove2.me/submissions/df219615-e537-4a2d-a8ec-c1ac86a5f153

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/CoefficientSupport.lean:L237-L250
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.bounds_of_weight. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport

-- ---- from OAI.Analysis.BackwardIntertwiners.CoefficientSupport ----
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

namespace CoefficientEnvelope

variable {d : ℕ → ℂ} {G : ℕ → ℝ}
variable (hu : ∀ n : ℕ, ∃ k, n < k ∧ d k ≠ 0)
variable (hG : DiscreteConvex G) (hG0 : G 0 = 0)
variable (hb : ∀ n, ‖d n‖ ≤ Real.exp (-G n))

end CoefficientEnvelope

lemma bounds_of_weight {w : ℤ → ℝ} (hw : ∀ j, 0 < w j) {b c : ℤ → ℂ}
    (hb : ∀ j, ‖b j‖ ≤ w j) (hc : ∀ j, ‖c j‖ * w j ≤ 1) :
    EnvelopeBounds (negativeLog w) (positiveLog w) b c := by
  have hc' (j : ℤ) : ‖c j‖ ≤ (w j)⁻¹ := by
    simpa only [one_div] using (le_div_iff₀ (hw j)).mpr (hc j)
  constructor
  · intro n
    simpa [positiveLog, Real.exp_log (hw _)] using hb n
  · intro n
    simpa [negativeLog, Real.exp_log (hw _)] using hb (-(n:ℤ))
  · intro n
    simpa [positiveLog, Real.exp_neg, Real.exp_log (hw _)] using hc' n
  · intro n
    simpa [negativeLog, Real.exp_neg, Real.exp_log (hw _)] using hc' (-(n:ℤ))

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.bounds_of_weight := @_root_.OAI.BackwardIntertwiners.bounds_of_weight
