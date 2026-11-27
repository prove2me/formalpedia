-- Prove2me | solution 1 for GlobalTheory.TwoLines.exists_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:34:37.299891+00:00
-- url     : https://prove2.me/submissions/4ccb1f51-d87d-4ee4-b4f4-11c60f55227a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfHermOne
import Theorems.Thm_GlobalTheory_TwoLines_two_mul_card_cmType

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
theorem _root_.solution {r : ℕ} (X : Data E r) (h : Module.finrank ℚ E = 4) :
    ∃ τ₁ τ₂ : X.Ψ, τ₁ ≠ τ₂ ∧ ∀ τ, τ = τ₁ ∨ τ = τ₂ := by
  classical
  have hc := two_mul_card_cmType X
  obtain ⟨a, b, hab, hΨ⟩ := Finset.card_eq_two.mp (by omega : X.Ψ.card = 2)
  have key : ∀ σ ∈ X.Ψ, σ = a ∨ σ = b := by
    intro σ hσ
    rw [hΨ] at hσ
    simpa using hσ
  have ha : a ∈ X.Ψ := by rw [hΨ]; simp
  have hb : b ∈ X.Ψ := by rw [hΨ]; simp
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, fun e => hab (congrArg Subtype.val e), fun τ => ?_⟩
  rcases key τ.1 τ.2 with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)
end GlobalTheory.TwoLines
