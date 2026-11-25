-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations.nonempty_cmType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:55:18.646204+00:00
-- url     : https://prove2.me/submissions/0376939a-17c6-4093-8bce-19771494a353

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_LowSpanCombinations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
theorem _root_.solution (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · have := (X.cmType τ).not.1 h
    exact ⟨⟨_, not_not.1 this⟩⟩
end GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
