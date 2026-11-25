-- Prove2me | solution 1 for GlobalTheory.FlatChecks.cfwM_all_eta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:42:50.158584+00:00
-- url     : https://prove2.me/submissions/1cfee721-138a-4dbd-9f9f-484446bf47ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_CoordDifferentiableAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FlatChecks
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FlatChecks
theorem _root_.solution (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (h : cfwM X ps a) (ha : 0 ≤ a)
    (η : ℝ) (hη : 0 < η) : ∃ C A' : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ →
    (∀ τ, 1 ≤ X.tt ξ x τ) →
    ps x ≤ C + A' * Real.log (1 + 1 / X.la1 x) - 8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ := by
  by_cases h2 : η < 1 / 2
  · exact h.2 η hη h2
  · obtain ⟨C, A', hC⟩ := h.1
    refine ⟨C, A', fun x hx ξ _ ht => ?_⟩
    have h0 : 0 ≤ ⨅ τ, X.tt ξ x τ := Real.iInf_nonneg fun τ => zero_le_one.trans (ht τ)
    have h1 : 0 ≤ 8 * Real.pi * (2 * η - 1) * a * ⨅ τ, X.tt ξ x τ := by
      have := Real.pi_pos
      have : 0 ≤ 2 * η - 1 := by linarith
      positivity
    have := hC x hx
    nlinarith
end GlobalTheory.FlatChecks
